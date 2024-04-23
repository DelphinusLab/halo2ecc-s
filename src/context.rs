use crate::assign::AssignedValue;
use crate::assign::Cell;
use crate::assign::Chip;
use crate::assign::ValueSchema;
use crate::circuit::base_chip::BaseChip;
use crate::circuit::base_chip::FIXED_COLUMNS;
use crate::circuit::base_chip::MUL_COLUMNS;
use crate::circuit::base_chip::VAR_COLUMNS;
use crate::circuit::range_chip::RangeAdvColIndex;
use crate::circuit::range_chip::RangeChip;
use crate::circuit::range_chip::RangeFixColIndex;
use crate::circuit::range_chip::COMMON_RANGE_BITS;
use crate::circuit::range_chip::RANGE_CHIP_ADV_COLUMNS;
use crate::circuit::range_chip::RANGE_CHIP_FIX_COLUMNS;
use crate::circuit::select_chip::SelectAdvColIndex;
use crate::circuit::select_chip::SelectChip;
use crate::circuit::select_chip::SelectFixColIndex;
use crate::range_info::RangeInfo;

use ark_std::end_timer;
use ark_std::start_timer;
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Region;
use halo2_proofs::plonk::Error;
use rayon::iter::*;
use rayon::prelude::ParallelSlice;
use std::cell::RefCell;
use std::fmt::Display;
use std::fmt::Formatter;
use std::rc::Rc;
use std::sync::Arc;

const MAX_ROWS: usize = 1 << 23;
const SANITY_CHECK: bool = false;
pub(crate) const OVERFLOW_BITS: u64 = 6;

#[derive(Debug, Clone)]
pub struct Context<N: FieldExt> {
    pub records: Records<N>,
    pub base_offset: usize,
    pub range_offset: usize,
    pub select_offset: usize,
}

impl<N: FieldExt> Display for Context<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(range_offset: {}, base_offset: {}, select_offset: {})",
            self.range_offset, self.base_offset, self.select_offset
        )
    }
}

impl<N: FieldExt> Context<N> {
    pub fn dump_fix_value(&self, start: usize, end: usize) {
        for i in start..end {
            for (col, v) in self.records.inner.base_fix_record[i].iter().enumerate() {
                if v.is_some() {
                    println!("base_fix_record value at {} {} is {:?}", i, col, v);
                }
            }

            for (col, v) in self.records.inner.range_fix_record[i].iter().enumerate() {
                if v.is_some() {
                    println!("range_fix_record value at {} {} is {:?}", i, col, v);
                }
            }

            for (col, v) in self.records.inner.select_fix_record[i].iter().enumerate() {
                if v.is_some() {
                    println!("select_fix_record value at {} {} is {:?}", i, col, v);
                }
            }
        }
    }

    pub fn check_row_has_some(&self) {
        for i in 0..self.base_offset {
            let mut has_some = false;

            for (_, v) in self.records.inner.base_fix_record[i].iter().enumerate() {
                if v.is_some() {
                    has_some = true;
                }
            }

            if !has_some {
                println!("no assigned fix in base chip at row {}", i);
                assert!(false);
            }
        }

        for i in 0..self.range_offset {
            let mut has_some = false;

            for (_, v) in self.records.inner.range_fix_record[i].iter().enumerate() {
                if v.is_some() {
                    has_some = true;
                }
            }

            if !has_some {
                println!("no assigned fix in range chip at row {}", i);
                assert!(false);
            }
        }

        for i in 0..self.select_offset {
            let mut has_some = false;

            for (_, v) in self.records.inner.select_fix_record[i].iter().enumerate() {
                if v.is_some() {
                    has_some = true;
                }
            }

            if !has_some {
                println!("no assigned fix in select chip at row {}", i);
                assert!(false);
            }
        }
    }

    pub fn dump_permutation(&self) {
        for (i, p) in self.records.permutations.iter().enumerate() {
            println!("permutation at {} is {:?}", i, p);
        }
    }
}

impl<N: FieldExt> Context<N> {
    pub fn new() -> Self {
        Self {
            records: Records::default(),
            base_offset: 0,
            range_offset: 0,
            select_offset: 0,
        }
    }

    pub fn clone_without_permutation(&self) -> Self {
        Self {
            records: Records {
                inner: self.records.inner.clone(),
                permutations: vec![],
                base_height: self.records.base_height,
                range_height: self.records.range_height,
                select_height: self.records.select_height,
            },
            base_offset: self.base_offset,
            range_offset: self.range_offset,
            select_offset: self.select_offset,
        }
    }
}

#[derive(Debug, Clone)]
pub struct IntegerContext<W: BaseExt, N: FieldExt> {
    pub ctx: Rc<RefCell<Context<N>>>,
    pub info: Arc<RangeInfo<W, N>>,
}

impl<W: BaseExt, N: FieldExt> From<IntegerContext<W, N>> for Context<N> {
    fn from(value: IntegerContext<W, N>) -> Self {
        Rc::try_unwrap(value.ctx).unwrap().into_inner()
    }
}

impl<W: BaseExt, N: FieldExt> IntegerContext<W, N> {
    pub fn new(ctx: Rc<RefCell<Context<N>>>) -> Self {
        Self::new_with_options(ctx, COMMON_RANGE_BITS, OVERFLOW_BITS)
    }

    pub fn new_with_options(
        ctx: Rc<RefCell<Context<N>>>,
        common_range_bits: u64,
        overflow_bits: u64,
    ) -> Self {
        Self {
            ctx,
            info: Arc::new(RangeInfo::<W, N>::new(common_range_bits, overflow_bits)),
        }
    }
}

pub struct NativeScalarEccContext<C: CurveAffine>(
    pub IntegerContext<<C as CurveAffine>::Base, <C as CurveAffine>::ScalarExt>,
    pub usize, // msm prefix, if it is usize::MAX, disable select chip
);

impl<C: CurveAffine> NativeScalarEccContext<C> {
    pub fn new_with_select_chip(
        ctx: IntegerContext<<C as CurveAffine>::Base, <C as CurveAffine>::ScalarExt>,
    ) -> Self {
        Self(ctx, 0)
    }

    pub fn new_without_select_chip(
        ctx: IntegerContext<<C as CurveAffine>::Base, <C as CurveAffine>::ScalarExt>,
    ) -> Self {
        Self(ctx, usize::MAX)
    }
}

impl<C: CurveAffine> From<NativeScalarEccContext<C>> for Context<C::Scalar> {
    fn from(value: NativeScalarEccContext<C>) -> Self {
        value.0.into()
    }
}

pub struct GeneralScalarEccContext<C: CurveAffine, N: FieldExt> {
    pub base_integer_ctx: IntegerContext<<C as CurveAffine>::Base, N>,
    pub scalar_integer_ctx: IntegerContext<<C as CurveAffine>::ScalarExt, N>,
    pub native_ctx: Rc<RefCell<Context<N>>>,
    pub msm_prefix: usize,
}

impl<C: CurveAffine, N: FieldExt> From<GeneralScalarEccContext<C, N>> for Context<N> {
    fn from(value: GeneralScalarEccContext<C, N>) -> Self {
        drop(value.base_integer_ctx);
        drop(value.scalar_integer_ctx);
        Rc::try_unwrap(value.native_ctx).unwrap().into_inner()
    }
}

impl<C: CurveAffine, N: FieldExt> GeneralScalarEccContext<C, N> {
    pub fn new(ctx: Rc<RefCell<Context<N>>>) -> Self {
        Self {
            base_integer_ctx: IntegerContext::<C::Base, N>::new(ctx.clone()),
            scalar_integer_ctx: IntegerContext::<C::Scalar, N>::new(ctx.clone()),
            native_ctx: ctx,
            msm_prefix: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordsInner<N: FieldExt> {
    pub base_adv_record: Vec<[(Option<N>, bool); VAR_COLUMNS]>,
    pub base_fix_record: Vec<[Option<N>; FIXED_COLUMNS]>,

    pub range_adv_record: Vec<[(Option<N>, bool); RANGE_CHIP_ADV_COLUMNS]>,
    pub range_fix_record: Vec<[Option<N>; RANGE_CHIP_FIX_COLUMNS]>,

    /* For picking point candidate from sum cache */
    pub select_adv_record: Vec<[(Option<N>, bool); 2]>,
    pub select_fix_record: Vec<[Option<N>; 2]>,
}

impl<N: FieldExt> Default for RecordsInner<N> {
    fn default() -> Self {
        let timer = start_timer!(|| "default");
        let _max_rows = std::env::var("HALO2ECC_S_MAX_ROWS")
            .ok()
            .and_then(|x| usize::from_str_radix(&x, 10).ok())
            .unwrap_or(MAX_ROWS);
        let max_rows = &_max_rows;

        let res = std::thread::scope(|s| {
            let base_adv_record = s.spawn(|| vec![[(None, false); VAR_COLUMNS]; *max_rows]);
            let base_fix_record = s.spawn(|| vec![[None; FIXED_COLUMNS]; *max_rows]);
            let range_adv_record =
                s.spawn(|| vec![[(None, false); RANGE_CHIP_ADV_COLUMNS]; *max_rows]);
            let range_fix_record = s.spawn(|| vec![[None; RANGE_CHIP_FIX_COLUMNS]; *max_rows]);
            let select_adv_record = s.spawn(|| vec![[(None, false); 2]; *max_rows]);
            let select_fix_record = s.spawn(|| vec![[None; 2]; *max_rows]);

            let base_adv_record = base_adv_record.join().unwrap();
            let base_fix_record = base_fix_record.join().unwrap();
            let range_adv_record = range_adv_record.join().unwrap();
            let range_fix_record = range_fix_record.join().unwrap();
            let select_adv_record = select_adv_record.join().unwrap();
            let select_fix_record = select_fix_record.join().unwrap();

            Self {
                base_adv_record,
                base_fix_record,
                range_adv_record,
                range_fix_record,
                select_adv_record,
                select_fix_record,
            }
        });
        end_timer!(timer);

        res
    }
}

#[derive(Debug, Default, Clone)]
pub struct Records<N: FieldExt> {
    pub inner: Arc<RecordsInner<N>>,
    pub base_height: usize,
    pub range_height: usize,
    pub select_height: usize,
    pub permutations: Vec<(Cell, Cell)>,
}

// Just used for parallel synthesize.
struct ParallelWorkAround<N: FieldExt> {
    ptr: *mut *mut Option<AssignedCell<N, N>>,
}
unsafe impl<N: FieldExt> Sync for ParallelWorkAround<N> {}

impl<N: FieldExt> Records<N> {
    fn _assign_to_base_chip(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = (0..VAR_COLUMNS)
            .into_par_iter()
            .map(|_| vec![None; self.base_height])
            .collect::<Vec<_>>();

        let mut cells_mut_ptr_vec = cells.iter_mut().map(|x| x.as_mut_ptr()).collect::<Vec<_>>();
        let cells_mut_ptr = ParallelWorkAround {
            ptr: cells_mut_ptr_vec.as_mut_ptr(),
        };
        let _cells_mut_ptr = &cells_mut_ptr;

        let threads = 16;
        let chunk_size = (self.base_height + threads - 1) / threads;
        let chunk_size = if chunk_size == 0 { 1 } else { chunk_size };
        let chunk_num = chunk_size * threads;
        self.inner
            .base_adv_record
            .par_chunks(chunk_size)
            .take(chunk_num)
            .enumerate()
            .for_each(move |(ic, c)| {
                for (row, advs) in c.iter().enumerate() {
                    let row = ic * chunk_size + row;
                    for (col, adv) in advs.iter().enumerate() {
                        if adv.0.is_some() {
                            let cell = region
                                .assign_advice(
                                    || "base adv col",
                                    base_chip.config.base[col],
                                    row,
                                    || Ok(adv.0.unwrap()),
                                )
                                .unwrap();
                            if adv.1 {
                                unsafe {
                                    *(*_cells_mut_ptr.ptr.offset(col as isize))
                                        .offset(row as isize) = Some(cell);
                                }
                            }
                        }
                    }
                }
            });

        for (row, fixes) in self
            .inner
            .base_fix_record
            .iter()
            .enumerate()
            .take(self.base_height)
        {
            for (col, fix) in fixes.iter().enumerate() {
                if fix.is_some() {
                    let col = if col < VAR_COLUMNS {
                        base_chip.config.coeff[col]
                    } else if col - VAR_COLUMNS < MUL_COLUMNS {
                        base_chip.config.mul_coeff[col - VAR_COLUMNS]
                    } else if col - VAR_COLUMNS - MUL_COLUMNS == 0 {
                        base_chip.config.next_coeff
                    } else {
                        base_chip.config.constant
                    };

                    region.assign_fixed(|| " base fixed col", col, row, || Ok(fix.unwrap()))?;
                }
            }
        }

        Ok(cells)
    }

    pub fn _assign_to_range_chip(
        &self,
        region: &Region<'_, N>,
        range_chip: &RangeChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = (0..RANGE_CHIP_ADV_COLUMNS)
            .into_par_iter()
            .map(|_| vec![None; self.range_height])
            .collect::<Vec<_>>();

        let mut cells_mut_ptr_vec = cells.iter_mut().map(|x| x.as_mut_ptr()).collect::<Vec<_>>();
        let cells_mut_ptr = ParallelWorkAround {
            ptr: cells_mut_ptr_vec.as_mut_ptr(),
        };
        let _cells_mut_ptr = &cells_mut_ptr;

        for (row, fix) in self
            .inner
            .range_fix_record
            .iter()
            .enumerate()
            .take(self.range_height + 1)
        {
            for (col, fix) in fix.iter().enumerate() {
                if let Some(v) = fix {
                    region.assign_fixed(
                        || "range fixed col",
                        range_chip.config.fix_cols[col],
                        row,
                        || Ok(*v),
                    )?;
                }
            }
        }

        let threads = 16;
        let chunk_size = (self.base_height + threads - 1) / threads;
        let chunk_size = if chunk_size == 0 { 1 } else { chunk_size };
        let chunk_num = chunk_size * threads;
        self.inner
            .range_adv_record
            .par_chunks(chunk_size)
            .take(chunk_num)
            .enumerate()
            .for_each(move |(ic, c)| {
                for (row, advs) in c.iter().enumerate() {
                    let row = ic * chunk_size + row;
                    for (col, adv) in advs.iter().enumerate() {
                        if adv.0.is_some() {
                            let cell = region
                                .assign_advice(
                                    || "range adv col",
                                    range_chip.config.adv_cols[col],
                                    row,
                                    || Ok(adv.0.unwrap()),
                                )
                                .unwrap();
                            if adv.1 {
                                unsafe {
                                    *(*_cells_mut_ptr.ptr.offset(col as isize))
                                        .offset(row as isize) = Some(cell);
                                }
                            }
                        }
                    }
                }
            });

        Ok(cells)
    }

    fn _assign_to_select_chip(
        &self,
        region: &Region<'_, N>,
        select_chip: &SelectChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = (0..4)
            .into_par_iter()
            .map(|_| vec![None; self.select_height])
            .collect::<Vec<_>>();

        for (row, advs) in self
            .inner
            .select_adv_record
            .iter()
            .enumerate()
            .take(self.select_height + 1)
        {
            if advs[SelectAdvColIndex::ValueCol as usize].0.is_some() {
                let cell = region.assign_advice(
                    || "select limb_info col",
                    select_chip.config.limb_info,
                    row,
                    || Ok(advs[0].0.unwrap()),
                )?;
                if advs[0].1 {
                    cells[0][row] = Some(cell);
                }
            }
            if advs[SelectAdvColIndex::SelectCol as usize].0.is_some() {
                let cell = region.assign_advice(
                    || "select selector col",
                    select_chip.config.selector,
                    row,
                    || Ok(advs[1].0.unwrap()),
                )?;
                if advs[1].1 {
                    cells[1][row] = Some(cell);
                }
            }
        }

        for (row, fixes) in self
            .inner
            .select_fix_record
            .iter()
            .enumerate()
            .take(self.select_height + 1)
        {
            if fixes[SelectFixColIndex::EncodeCol as usize].is_some() {
                region.assign_fixed(
                    || "encoded offset",
                    select_chip.config.encoded_offset,
                    row,
                    || Ok(fixes[0].unwrap()),
                )?;
            }
            if fixes[SelectFixColIndex::IsLookupCol as usize].is_some() {
                region.assign_fixed(
                    || "is_lookup",
                    select_chip.config.is_lookup,
                    row,
                    || Ok(fixes[1].unwrap()),
                )?;
            }
        }
        Ok(cells)
    }

    pub fn _assign_permutation(
        &self,
        region: &Region<'_, N>,
        cells: &Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>,
    ) -> Result<(), Error> {
        for (left, right) in self.permutations.iter() {
            let left = cells[left.region as usize][left.col][left.row]
                .as_ref()
                .unwrap()
                .cell();
            let right = cells[right.region as usize][right.col][right.row]
                .as_ref()
                .unwrap()
                .cell();
            region.constrain_equal(left, right)?;
        }

        Ok(())
    }

    pub fn assign_all_opt(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
        range_chip: &RangeChip<N>,
        select_chip: &SelectChip<N>,
    ) -> Result<Option<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>>, Error> {
        let res = self.assign_all(region, base_chip, range_chip, select_chip)?;
        Ok(Some(res))
    }

    pub fn assign_all_with_optional_select_chip(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
        range_chip: &RangeChip<N>,
        select_chip: Option<&SelectChip<N>>,
    ) -> Result<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>, Error> {
        let base_cells = self._assign_to_base_chip(region, base_chip)?;
        let range_cells = self._assign_to_range_chip(region, range_chip)?;
        let select_cells = select_chip
            .map(|select_chip| self._assign_to_select_chip(region, select_chip))
            .unwrap_or(Ok(vec![]))?;
        // Check in case leak the chip dependency
        if select_chip.is_none() {
            assert!(self.select_height == 0);
        }
        let cells = vec![base_cells, range_cells, select_cells];
        self._assign_permutation(region, &cells)?;
        Ok(cells)
    }

    pub fn assign_all(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
        range_chip: &RangeChip<N>,
        select_chip: &SelectChip<N>,
    ) -> Result<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>, Error> {
        let base_cells = self._assign_to_base_chip(region, base_chip)?;
        let range_cells = self._assign_to_range_chip(region, range_chip)?;
        let select_cells = self._assign_to_select_chip(region, select_chip)?;
        let cells = vec![base_cells, range_cells, select_cells];
        self._assign_permutation(region, &cells)?;
        Ok(cells)
    }

    pub fn enable_permute(&mut self, cell: &Cell) {
        match cell.region {
            Chip::BaseChip => {
                unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_adv_record[cell.row]
                    [cell.col]
                    .1 = true
            }
            Chip::RangeChip => {
                unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[cell.row]
                    [cell.col]
                    .1 = true
            }
            Chip::SelectChip => {
                unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_adv_record[cell.row]
                    [cell.col]
                    .1 = true
            }
        }
    }

    fn assign_adv_cell_in_base_chip(&mut self, offset: usize, col: usize, val: N) {
        if SANITY_CHECK {
            assert!(
                self.inner.base_adv_record[offset][col as usize].0.is_none()
                    || self.inner.base_adv_record[offset][col as usize].0 == Some(val)
            );
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_adv_record[offset][col as usize]
            .0 = Some(val);
    }

    fn assign_fix_cell_in_base_chip(&mut self, offset: usize, col: usize, val: N) {
        if SANITY_CHECK {
            assert!(
                self.inner.base_fix_record[offset][col as usize].is_none()
                    || self.inner.base_fix_record[offset][col as usize] == Some(val)
            );
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_fix_record[offset][col as usize] =
            Some(val);
    }

    pub fn one_line(
        &mut self,
        offset: usize,
        base_coeff_pairs: Vec<(ValueSchema<N>, N)>,
        constant: Option<N>,
        mul_next_coeffs: (Vec<N>, Option<N>),
    ) {
        assert!(base_coeff_pairs.len() <= VAR_COLUMNS);

        if offset >= self.base_height {
            self.base_height = offset + 1;
        }

        for (i, (base, coeff)) in base_coeff_pairs.into_iter().enumerate() {
            match base.cell() {
                Some(cell) => {
                    let new_cell = Cell::new(Chip::BaseChip, i, offset);

                    self.enable_permute(&new_cell);
                    self.enable_permute(&cell);

                    self.permutations.push((cell, new_cell));
                }
                _ => {}
            }
            self.assign_adv_cell_in_base_chip(offset, i, base.value());
            self.assign_fix_cell_in_base_chip(offset, i, coeff);
        }

        let (mul_coeffs, next) = mul_next_coeffs;
        for (i, mul_coeff) in mul_coeffs.into_iter().enumerate() {
            self.assign_fix_cell_in_base_chip(offset, VAR_COLUMNS + i, mul_coeff);
        }

        if next.is_some() {
            self.assign_fix_cell_in_base_chip(offset, VAR_COLUMNS + MUL_COLUMNS, next.unwrap());
        } else {
            assert!(self.inner.base_fix_record[offset][VAR_COLUMNS + MUL_COLUMNS].is_none());
        }

        if constant.is_some() {
            self.assign_fix_cell_in_base_chip(
                offset,
                VAR_COLUMNS + MUL_COLUMNS + 1,
                constant.unwrap(),
            );
        } else {
            assert!(self.inner.base_fix_record[offset][VAR_COLUMNS + MUL_COLUMNS + 1].is_none());
        }
    }

    pub fn one_line_with_last(
        &mut self,
        offset: usize,
        base_coeff_pairs: Vec<(ValueSchema<N>, N)>,
        tail: (ValueSchema<N>, N),
        constant: Option<N>,
        mul_next_coeffs: (Vec<N>, Option<N>),
    ) {
        assert!(base_coeff_pairs.len() <= VAR_COLUMNS - 1);

        self.one_line(offset, base_coeff_pairs, constant, mul_next_coeffs);

        let (base, coeff) = tail;

        let i = VAR_COLUMNS - 1;
        match base.cell() {
            Some(cell) => {
                let new_cell = Cell::new(Chip::BaseChip, i, offset);

                self.enable_permute(&new_cell);
                self.enable_permute(&cell);

                self.permutations.push((cell, new_cell));
            }
            _ => {}
        }

        self.assign_adv_cell_in_base_chip(offset, i, base.value());
        self.assign_fix_cell_in_base_chip(offset, i, coeff);
    }

    fn ensure_range_record_size(&mut self, offset: usize) {
        if offset >= self.range_height {
            self.range_height = offset + 1;
        }
    }

    fn assign_adv_cell_in_select_chip(&mut self, offset: usize, col: SelectAdvColIndex, val: N) {
        if SANITY_CHECK {
            assert!(
                self.inner.select_adv_record[offset][col as usize]
                    .0
                    .is_none()
                    || self.inner.select_adv_record[offset][col as usize].0 == Some(val)
            );
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_adv_record[offset]
            [col as usize]
            .0 = Some(val);
    }

    fn assign_fix_cell_in_select_chip(&mut self, offset: usize, col: SelectFixColIndex, val: N) {
        if SANITY_CHECK {
            assert!(
                self.inner.select_fix_record[offset][col as usize].is_none()
                    || self.inner.select_fix_record[offset][col as usize] == Some(val)
            );
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_fix_record[offset]
            [col as usize] = Some(val);
    }

    pub fn assign_cache_value(&mut self, offset: usize, v: &AssignedValue<N>, encode: N) {
        if offset >= self.select_height {
            self.select_height = offset + 1;
        }

        self.assign_adv_cell_in_select_chip(offset, SelectAdvColIndex::ValueCol, v.val);
        let idx = Cell::new(
            Chip::SelectChip,
            SelectAdvColIndex::ValueCol as usize,
            offset,
        );
        self.permutations.push((idx, v.cell));
        self.enable_permute(&idx);
        self.enable_permute(&v.cell);
        // assign encode

        self.assign_fix_cell_in_select_chip(offset, SelectFixColIndex::EncodeCol, encode);
        self.assign_fix_cell_in_select_chip(offset, SelectFixColIndex::IsLookupCol, N::zero());
    }

    pub fn assign_select_value(
        &mut self,
        offset: usize,
        v: &AssignedValue<N>,
        encode: N,
        selector: &AssignedValue<N>,
    ) -> AssignedValue<N> {
        if offset >= self.select_height {
            self.select_height = offset + 1;
        }

        self.assign_adv_cell_in_select_chip(offset, SelectAdvColIndex::ValueCol, v.val);
        self.assign_adv_cell_in_select_chip(offset, SelectAdvColIndex::SelectCol, selector.val);

        let selector_cell = Cell::new(
            Chip::SelectChip,
            SelectAdvColIndex::SelectCol as usize,
            offset,
        );
        self.permutations.push((selector_cell, selector.cell));
        self.enable_permute(&selector_cell);
        self.enable_permute(&selector.cell);

        self.assign_fix_cell_in_select_chip(offset, SelectFixColIndex::EncodeCol, encode);
        self.assign_fix_cell_in_select_chip(offset, SelectFixColIndex::IsLookupCol, N::one());

        AssignedValue::new(
            Chip::SelectChip,
            SelectAdvColIndex::ValueCol as usize,
            offset,
            v.val,
        )
    }

    fn assign_adv_cell_in_range_chip(&mut self, offset: usize, col: RangeAdvColIndex, val: N) {
        if SANITY_CHECK {
            assert!(
                self.inner.range_adv_record[offset][col as usize]
                    .0
                    .is_none()
                    || self.inner.range_adv_record[offset][col as usize].0 == Some(val)
            );
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset][col as usize]
            .0 = Some(val);
    }

    fn assign_fix_cell_in_range_chip(&mut self, offset: usize, col: RangeFixColIndex, val: N) {
        if SANITY_CHECK {
            if col == RangeFixColIndex::AccLinesCol {
                assert!(val == N::one() || val == N::from(2u64) || val == N::from(3u64));
            } else {
                assert!(val <= N::from(COMMON_RANGE_BITS));
            }

            assert!(
                self.inner.range_fix_record[offset][col as usize].is_none()
                    || self.inner.range_fix_record[offset][col as usize] == Some(val)
            );
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset][col as usize] =
            Some(val);
    }

    pub fn assign_one_line_range_value(
        &mut self,
        offset: usize,
        v: &[N],
        v_acc: N,
        bits: u64,
    ) -> AssignedValue<N> {
        //println!("bits is {}", bits);
        assert!(bits <= COMMON_RANGE_BITS);
        self.ensure_range_record_size(offset + 1);

        self.assign_fix_cell_in_range_chip(offset, RangeFixColIndex::AccLinesCol, N::one());
        self.assign_fix_cell_in_range_chip(offset, RangeFixColIndex::TagCol, N::from(bits));
        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::TaggedRangeCol, v[0]);
        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::ValueAccCol, v_acc);

        AssignedValue::new(
            Chip::RangeChip,
            RangeAdvColIndex::ValueAccCol as usize,
            offset,
            v_acc,
        )
    }

    pub fn assign_two_line_range_value(
        &mut self,
        offset: usize,
        v: &[N],
        v_acc: N,
        bits: u64,
    ) -> AssignedValue<N> {
        assert!(bits >= COMMON_RANGE_BITS * 2);
        assert!(bits <= COMMON_RANGE_BITS * 4);
        self.ensure_range_record_size(offset + 2);

        self.assign_fix_cell_in_range_chip(
            offset,
            RangeFixColIndex::AccLinesCol,
            N::one() + N::one(),
        );

        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::CommonRangeCol, v[0]);
        self.assign_adv_cell_in_range_chip(offset + 1, RangeAdvColIndex::CommonRangeCol, v[1]);

        let cell_bits = if bits >= 3 * COMMON_RANGE_BITS {
            COMMON_RANGE_BITS
        } else {
            bits % COMMON_RANGE_BITS
        };
        self.assign_fix_cell_in_range_chip(offset, RangeFixColIndex::TagCol, N::from(cell_bits));
        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::TaggedRangeCol, v[2]);

        let cell_bits = if bits > 3 * COMMON_RANGE_BITS {
            bits - 3 * COMMON_RANGE_BITS
        } else {
            0
        };
        self.assign_fix_cell_in_range_chip(
            offset + 1,
            RangeFixColIndex::TagCol,
            N::from(cell_bits),
        );
        self.assign_adv_cell_in_range_chip(offset + 1, RangeAdvColIndex::TaggedRangeCol, v[3]);

        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::ValueAccCol, v_acc);

        AssignedValue::new(
            Chip::RangeChip,
            RangeAdvColIndex::ValueAccCol as usize,
            offset,
            v_acc,
        )
    }

    pub fn assign_three_line_range_value(
        &mut self,
        offset: usize,
        v: &[N],
        v_acc: N,
        bits: u64,
    ) -> AssignedValue<N> {
        assert!(bits >= COMMON_RANGE_BITS * 3);
        assert!(bits <= COMMON_RANGE_BITS * 6);
        self.ensure_range_record_size(offset + 3);

        self.assign_fix_cell_in_range_chip(
            offset,
            RangeFixColIndex::AccLinesCol,
            N::one() + N::one() + N::one(),
        );

        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::CommonRangeCol, v[0]);
        self.assign_adv_cell_in_range_chip(offset + 1, RangeAdvColIndex::CommonRangeCol, v[1]);
        self.assign_adv_cell_in_range_chip(offset + 2, RangeAdvColIndex::CommonRangeCol, v[2]);

        let cell_bits = if bits >= 4 * COMMON_RANGE_BITS {
            COMMON_RANGE_BITS
        } else {
            bits % COMMON_RANGE_BITS
        };
        self.assign_fix_cell_in_range_chip(offset, RangeFixColIndex::TagCol, N::from(cell_bits));
        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::TaggedRangeCol, v[3]);

        let cell_bits = if bits >= 5 * COMMON_RANGE_BITS {
            COMMON_RANGE_BITS
        } else if bits > 4 * COMMON_RANGE_BITS {
            bits % COMMON_RANGE_BITS
        } else {
            0
        };
        self.assign_fix_cell_in_range_chip(
            offset + 1,
            RangeFixColIndex::TagCol,
            N::from(cell_bits),
        );
        self.assign_adv_cell_in_range_chip(offset + 1, RangeAdvColIndex::TaggedRangeCol, v[4]);

        let cell_bits = if bits > 5 * COMMON_RANGE_BITS {
            bits - 5 * COMMON_RANGE_BITS
        } else {
            0
        };
        self.assign_fix_cell_in_range_chip(
            offset + 2,
            RangeFixColIndex::TagCol,
            N::from(cell_bits),
        );
        self.assign_adv_cell_in_range_chip(offset + 2, RangeAdvColIndex::TaggedRangeCol, v[5]);

        self.assign_adv_cell_in_range_chip(offset, RangeAdvColIndex::ValueAccCol, v_acc);

        AssignedValue::new(
            Chip::RangeChip,
            RangeAdvColIndex::ValueAccCol as usize,
            offset,
            v_acc,
        )
    }

    pub fn assign_range_value(
        &mut self,
        offset: usize,
        mut v: Vec<N>,
        v_acc: N,
        bits: u64,
    ) -> (AssignedValue<N>, usize) {
        if bits <= COMMON_RANGE_BITS {
            let assigned = self.assign_one_line_range_value(offset, &v[..], v_acc, bits);
            (assigned, 1)
        } else if bits < 2 * COMMON_RANGE_BITS {
            unreachable!()
        } else if bits <= 4 * COMMON_RANGE_BITS {
            v.resize(4, N::zero());
            let assigned = self.assign_two_line_range_value(offset, &v[..], v_acc, bits);
            (assigned, 2)
        } else if bits <= 6 * COMMON_RANGE_BITS {
            v.resize(6, N::zero());
            let assigned = self.assign_three_line_range_value(offset, &v[..], v_acc, bits);
            (assigned, 3)
        } else {
            unreachable!()
        }
    }
}
