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
use crate::circuit::select_chip::SelectChip;
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
use std::cell::RefCell;
use std::fmt::Display;
use std::fmt::Formatter;
use std::rc::Rc;
use std::sync::Arc;

const MAX_ROWS: usize = 1 << 23;

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
        const OVERFLOW_BITS: u64 = 6;
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

impl<N: FieldExt> Records<N> {
    fn assign_for_max_row(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
        max_row: usize,
    ) -> Result<bool, Error> {
        let adv_cell = region.assign_advice(
            || "base",
            base_chip.config.base[0],
            max_row,
            || Ok(N::zero()),
        )?;

        let fixed_cell = region.assign_fixed(
            || "base",
            base_chip.config.coeff[0],
            max_row,
            || Ok(N::zero()),
        )?;

        Ok(adv_cell.value().is_none() && fixed_cell.value().is_none())
    }

    fn _assign_to_base_chip(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = (0..VAR_COLUMNS)
            .into_par_iter()
            .map(|_| vec![None; self.base_height])
            .collect::<Vec<_>>();

        for (row, advs) in self.inner.base_adv_record.iter().enumerate() {
            if row >= self.base_height {
                break;
            }

            for (col, adv) in advs.iter().enumerate() {
                if adv.0.is_some() {
                    let cell = region.assign_advice(
                        || "base",
                        base_chip.config.base[col],
                        row,
                        || Ok(adv.0.unwrap()),
                    )?;
                    if adv.1 {
                        cells[col][row] = Some(cell);
                    }
                }
            }
        }

        for (row, fixes) in self.inner.base_fix_record.iter().enumerate() {
            if row >= self.base_height {
                break;
            }

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

                    region.assign_fixed(|| "fix", col, row, || Ok(fix.unwrap()))?;
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

        for (row, fix) in self.inner.range_fix_record.iter().enumerate() {
            if row >= self.range_height {
                break;
            }

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

        for (row, adv) in self.inner.range_adv_record.iter().enumerate() {
            if row >= self.range_height {
                break;
            }

            for (col, adv) in adv.iter().enumerate() {
                if let Some(v) = &adv.0 {
                    let cell = region.assign_advice(
                        || "range adv col",
                        range_chip.config.adv_cols[col],
                        row,
                        || Ok(*v),
                    )?;
                    if adv.1 {
                        cells[col][row] = Some(cell);
                    }
                }
            }
        }

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

        for (row, advs) in self.inner.select_adv_record.iter().enumerate() {
            if row >= self.base_height {
                break;
            }
            if advs[0].0.is_some() {
                let cell = region.assign_advice(
                    || "base",
                    select_chip.config.limb_info,
                    row,
                    || Ok(advs[0].0.unwrap()),
                )?;
                if advs[0].1 {
                    cells[0][row] = Some(cell);
                }
            }
            if advs[1].0.is_some() {
                let cell = region.assign_advice(
                    || "base",
                    select_chip.config.selector,
                    row,
                    || Ok(advs[1].0.unwrap()),
                )?;
                if advs[1].1 {
                    cells[1][row] = Some(cell);
                }
            }
        }

        for (row, fixes) in self.inner.select_fix_record.iter().enumerate() {
            if row >= self.base_height {
                break;
            }
            if fixes[0].is_some() {
                region.assign_fixed(
                    || "encoded offset",
                    select_chip.config.encoded_offset,
                    row,
                    || Ok(fixes[0].unwrap()),
                )?;
            }
            if fixes[1].is_some() {
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

    pub fn assign_all_in_base(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>, Error> {
        let cells = self._assign_to_base_chip(region, base_chip)?;
        let cells = vec![cells];
        self._assign_permutation(region, &cells)?;
        Ok(cells)
    }

    pub fn assign_all_opt(
        &self,
        region: &Region<'_, N>,
        base_chip: &BaseChip<N>,
        range_chip: &RangeChip<N>,
        select_chip: &SelectChip<N>,
    ) -> Result<Option<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>>, Error> {
        let max_row = self
            .base_height
            .max(self.range_height)
            .max(self.select_height);
        let is_assign_for_max_row = self.assign_for_max_row(region, base_chip, max_row)?;
        if !is_assign_for_max_row {
            let base_cells = self._assign_to_base_chip(region, base_chip)?;
            let range_cells = self._assign_to_range_chip(region, range_chip)?;
            let select_cells = self._assign_to_select_chip(region, select_chip)?;
            let cells = vec![base_cells, range_cells, select_cells];
            self._assign_permutation(region, &cells)?;
            Ok(Some(cells))
        } else {
            Ok(None)
        }
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
                    let idx = Cell::new(Chip::BaseChip, i, offset);

                    unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_adv_record[offset][i]
                        .1 = true;
                    self.enable_permute(&cell);

                    self.permutations.push((cell, idx));
                }
                _ => {}
            }
            unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_fix_record[offset][i] =
                Some(coeff);
            unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_adv_record[offset][i].0 =
                Some(base.value());
        }

        let (mul_coeffs, next) = mul_next_coeffs;
        for (i, mul_coeff) in mul_coeffs.into_iter().enumerate() {
            unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_fix_record[offset]
                [VAR_COLUMNS + i] = Some(mul_coeff);
        }

        if next.is_some() {
            unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_fix_record[offset]
                [VAR_COLUMNS + MUL_COLUMNS] = next;
        }

        if constant.is_some() {
            unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_fix_record[offset]
                [VAR_COLUMNS + MUL_COLUMNS + 1] = constant;
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
                let idx = Cell::new(Chip::BaseChip, i, offset);

                unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_adv_record[offset][i].1 =
                    true;
                self.enable_permute(&cell);

                self.permutations.push((cell, idx));
            }
            _ => {}
        }
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_fix_record[offset][i] = Some(coeff);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.base_adv_record[offset][i].0 =
            Some(base.value());
    }

    fn ensure_range_record_size(&mut self, offset: usize) {
        if offset >= self.range_height {
            self.range_height = offset + 1;
        }
    }

    pub fn assign_cache_value(&mut self, offset: usize, v: &AssignedValue<N>, encode: N) {
        if offset >= self.select_height {
            self.select_height = offset + 1;
        }

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_adv_record[offset][0].0 =
            Some(v.val);
        let idx = Cell::new(Chip::SelectChip, 0, offset);
        self.permutations.push((idx, v.cell));
        self.enable_permute(&idx);
        self.enable_permute(&v.cell);
        // assign encode
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_fix_record[offset][0] =
            Some(encode);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_fix_record[offset][1] =
            Some(N::zero());
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

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_adv_record[offset][0].0 =
            Some(v.val);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_adv_record[offset][1].0 =
            Some(selector.val);
        let selector_cell = Cell::new(Chip::SelectChip, 1, offset);
        self.permutations.push((selector_cell, selector.cell));
        self.enable_permute(&selector_cell);
        self.enable_permute(&selector.cell);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_fix_record[offset][0] =
            Some(encode);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.select_fix_record[offset][1] =
            Some(N::one());

        AssignedValue::new(Chip::SelectChip, 0, offset, v.val)
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

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset]
            [RangeFixColIndex::AccLinesCol as usize] = Some(N::one());
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset]
            [RangeFixColIndex::TagCol as usize] = Some(N::from(bits));
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::TaggedRangeCol as usize]
            .0 = Some(v[0]);

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::ValueAccCol as usize]
            .0 = Some(v_acc);

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

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset]
            [RangeFixColIndex::AccLinesCol as usize] = Some(N::one() + N::one());

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::CommonRangeCol as usize]
            .0 = Some(v[0]);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset + 1]
            [RangeAdvColIndex::CommonRangeCol as usize]
            .0 = Some(v[1]);

        let cell_bits = if bits >= 3 * COMMON_RANGE_BITS {
            COMMON_RANGE_BITS
        } else {
            bits % COMMON_RANGE_BITS
        };
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset]
            [RangeFixColIndex::TagCol as usize] = Some(N::from(cell_bits));
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::TaggedRangeCol as usize]
            .0 = Some(v[2]);

        let cell_bits = if bits > 3 * COMMON_RANGE_BITS {
            bits - 3 * COMMON_RANGE_BITS
        } else {
            0
        };
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset + 1]
            [RangeFixColIndex::TagCol as usize] = Some(N::from(cell_bits));
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset + 1]
            [RangeAdvColIndex::TaggedRangeCol as usize]
            .0 = Some(v[3]);

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::ValueAccCol as usize]
            .0 = Some(v_acc);

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

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset]
            [RangeFixColIndex::AccLinesCol as usize] = Some(N::one() + N::one() + N::one());

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::CommonRangeCol as usize]
            .0 = Some(v[0]);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset + 1]
            [RangeAdvColIndex::CommonRangeCol as usize]
            .0 = Some(v[1]);
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset + 2]
            [RangeAdvColIndex::CommonRangeCol as usize]
            .0 = Some(v[2]);

        let cell_bits = if bits >= 4 * COMMON_RANGE_BITS {
            COMMON_RANGE_BITS
        } else {
            bits % COMMON_RANGE_BITS
        };
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset]
            [RangeFixColIndex::TagCol as usize] = Some(N::from(cell_bits));
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::TaggedRangeCol as usize]
            .0 = Some(v[3]);

        let cell_bits = if bits >= 5 * COMMON_RANGE_BITS {
            COMMON_RANGE_BITS
        } else if bits > 4 * COMMON_RANGE_BITS {
            bits % COMMON_RANGE_BITS
        } else {
            0
        };
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset + 1]
            [RangeFixColIndex::TagCol as usize] = Some(N::from(cell_bits));
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset + 1]
            [RangeAdvColIndex::TaggedRangeCol as usize]
            .0 = Some(v[4]);

        let cell_bits = if bits > 5 * COMMON_RANGE_BITS {
            bits - 5 * COMMON_RANGE_BITS
        } else {
            0
        };
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_fix_record[offset + 2]
            [RangeFixColIndex::TagCol as usize] = Some(N::from(cell_bits));
        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset + 2]
            [RangeAdvColIndex::TaggedRangeCol as usize]
            .0 = Some(v[5]);

        unsafe { Arc::get_mut_unchecked(&mut self.inner) }.range_adv_record[offset]
            [RangeAdvColIndex::ValueAccCol as usize]
            .0 = Some(v_acc);

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
        } else if bits <= 2 * COMMON_RANGE_BITS {
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
