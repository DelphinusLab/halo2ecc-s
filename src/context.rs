use crate::assign::AssignedValue;
use crate::assign::Cell;
use crate::assign::Chip;
use crate::assign::ValueSchema;
use crate::circuit::base_chip::BaseChip;
use crate::circuit::base_chip::FIXED_COLUMNS;
use crate::circuit::base_chip::MUL_COLUMNS;
use crate::circuit::base_chip::VAR_COLUMNS;
use crate::circuit::range_chip::RangeChip;
use crate::circuit::range_chip::COMMON_RANGE_BITS;
use crate::circuit::range_chip::MAX_CHUNKS;
use crate::circuit::range_chip::RANGE_VALUE_DECOMPOSE;
use crate::circuit::range_chip::VALUE_COLUMNS;
use crate::circuit::select_chip::SelectChip;
use crate::range_info::RangeInfo;
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Region;
use halo2_proofs::plonk::Error;
use std::cell::RefCell;
use std::fmt::Display;
use std::fmt::Formatter;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::Mutex;

#[derive(Debug, Clone)]
pub struct Context<N: FieldExt> {
    pub records: Arc<Mutex<Records<N>>>,
    pub base_offset: usize,
    pub range_offset: usize,
    pub select_offset: usize,
}

impl<N: FieldExt> Display for Context<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(range_offset: {}, base_offset: {})",
            self.range_offset, self.base_offset
        )
    }
}

impl<N: FieldExt> Context<N> {
    pub fn new() -> Self {
        Self {
            records: Arc::new(Mutex::new(Records::default())),
            base_offset: 0,
            range_offset: 0,
            select_offset: 0,
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
    pub usize, // msm prefix
);

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

#[derive(Debug, Default, Clone)]
pub struct Records<N: FieldExt> {
    pub base_adv_record: Vec<[(Option<N>, bool); VAR_COLUMNS]>,
    pub base_fix_record: Vec<[Option<N>; FIXED_COLUMNS]>,
    pub base_height: usize,

    pub range_adv_record: Vec<[(Option<N>, bool); VALUE_COLUMNS]>,
    /* block_first selector and tag for last value column */
    pub range_fix_record: Vec<[Option<N>; 2]>,
    pub range_height: usize,

    /* For picking point candidate from sum cache */
    pub select_adv_record: Vec<[(Option<N>, bool); 2]>,
    pub select_fix_record: Vec<[Option<N>; 2]>,
    pub select_height: usize,

    pub permutations: Vec<(Cell, Cell)>,
}

impl<N: FieldExt> Records<N> {
    fn assign_for_max_row(
        &self,
        region: &mut Region<'_, N>,
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
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = vec![];

        cells.resize(VAR_COLUMNS, vec![None; self.base_height]);

        for (row, advs) in self.base_adv_record.iter().enumerate() {
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

        for (row, fixes) in self.base_fix_record.iter().enumerate() {
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
        region: &mut Region<'_, N>,
        range_chip: &RangeChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = vec![vec![None; self.range_height]];

        for (row, fix) in self.range_fix_record.iter().enumerate() {
            if row >= self.range_height {
                break;
            }
            if fix[0].is_some() {
                region.assign_fixed(
                    || "range block first",
                    range_chip.config.block_first,
                    row,
                    || Ok(fix[0].unwrap()),
                )?;
            }

            if fix[1].is_some() {
                region.assign_fixed(
                    || "range class",
                    range_chip.config.range_class,
                    row,
                    || Ok(fix[1].unwrap()),
                )?;
            }
        }

        for (row, adv) in self.range_adv_record.iter().enumerate() {
            if row >= self.range_height {
                break;
            }

            for (col, adv) in adv.iter().enumerate() {
                if adv.0.is_some() {
                    let cell = region.assign_advice(
                        || "range var",
                        range_chip.config.values[col],
                        row,
                        || Ok(adv.0.unwrap()),
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
        region: &mut Region<'_, N>,
        select_chip: &SelectChip<N>,
    ) -> Result<Vec<Vec<Option<AssignedCell<N, N>>>>, Error> {
        let mut cells = vec![];

        cells.resize(4, vec![None; self.select_height]);

        for (row, advs) in self.select_adv_record.iter().enumerate() {
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

        for (row, fixes) in self.select_fix_record.iter().enumerate() {
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
        region: &mut Region<'_, N>,
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
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>, Error> {
        let cells = self._assign_to_base_chip(region, base_chip)?;
        let cells = vec![cells];
        self._assign_permutation(region, &cells)?;
        Ok(cells)
    }

    pub fn assign_all_opt(
        &self,
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
        range_chip: &RangeChip<N>,
        select_chip: &SelectChip<N>,
    ) -> Result<Option<Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>>, Error> {
        let max_row = usize::max(self.base_height, self.range_height);
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

    pub fn assign_all(
        &self,
        region: &mut Region<'_, N>,
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
            Chip::BaseChip => self.base_adv_record[cell.row][cell.col].1 = true,
            Chip::RangeChip => self.range_adv_record[cell.row][cell.col].1 = true,
            Chip::SelectChip => self.select_adv_record[cell.row][cell.col].1 = true,
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

        const EXTEND_SIZE: usize = 16;

        if offset >= self.base_adv_record.len() {
            let to_len = (offset + EXTEND_SIZE) & !(EXTEND_SIZE - 1);
            self.base_adv_record
                .resize(to_len, [(None, false); VAR_COLUMNS]);
            self.base_fix_record.resize(to_len, [None; FIXED_COLUMNS]);
        }

        if offset >= self.base_height {
            self.base_height = offset + 1;
        }

        for (i, (base, coeff)) in base_coeff_pairs.into_iter().enumerate() {
            match base.cell() {
                Some(cell) => {
                    let idx = Cell::new(Chip::BaseChip, i, offset);

                    self.base_adv_record[offset][i].1 = true;
                    self.enable_permute(&cell);

                    self.permutations.push((cell, idx));
                }
                _ => {}
            }
            self.base_fix_record[offset][i] = Some(coeff);
            self.base_adv_record[offset][i].0 = Some(base.value());
        }

        let (mul_coeffs, next) = mul_next_coeffs;
        for (i, mul_coeff) in mul_coeffs.into_iter().enumerate() {
            self.base_fix_record[offset][VAR_COLUMNS + i] = Some(mul_coeff);
        }

        if next.is_some() {
            self.base_fix_record[offset][VAR_COLUMNS + MUL_COLUMNS] = next;
        }

        if constant.is_some() {
            self.base_fix_record[offset][VAR_COLUMNS + MUL_COLUMNS + 1] = constant;
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

                self.base_adv_record[offset][i].1 = true;
                self.enable_permute(&cell);

                self.permutations.push((cell, idx));
            }
            _ => {}
        }
        self.base_fix_record[offset][i] = Some(coeff);
        self.base_adv_record[offset][i].0 = Some(base.value());
    }

    fn ensure_range_record_size(&mut self, offset: usize) {
        const EXTEND_SIZE: usize = 1024;

        if offset >= self.range_adv_record.len() {
            let to_len = (offset + EXTEND_SIZE) & !(EXTEND_SIZE - 1);
            self.range_adv_record
                .resize(to_len, [(None, false); VALUE_COLUMNS]);
            self.range_fix_record.resize(to_len, [None; 2]);
        }

        if offset >= self.range_height {
            self.range_height = offset + 1;
        }
    }

    pub fn assign_single_range_value(
        &mut self,
        offset: usize,
        v: N,
        leading_bits: u64,
    ) -> AssignedValue<N> {
        self.ensure_range_record_size(offset + 1);

        self.range_fix_record[offset][1] = Some(N::from(leading_bits));
        self.range_adv_record[offset][VALUE_COLUMNS - 1].0 = Some(v);

        AssignedValue::new(Chip::RangeChip, VALUE_COLUMNS - 1, offset, v)
    }

    pub fn assign_cache_value(&mut self, offset: usize, v: &AssignedValue<N>, encode: N) {
        //println!("Cache [offset, v, encode] {:?} {:?} {:?}", offset, v.val, encode);
        if offset >= self.select_fix_record.len() {
            self.select_adv_record.resize(1 << 20, [(None, false); 2]);
            self.select_fix_record.resize(1 << 20, [None; 2]);
        }

        if offset >= self.select_height {
            self.select_height = offset + 1;
        }

        assert!(offset < 1 << 20);

        self.select_adv_record[offset][0].0 = Some(v.val);
        let idx = Cell::new(Chip::SelectChip, 0, offset);
        self.permutations.push((idx, v.cell));
        self.enable_permute(&idx);
        self.enable_permute(&v.cell);
        // assign encode
        self.select_fix_record[offset][0] = Some(encode);
        self.select_fix_record[offset][1] = Some(N::zero());
    }

    pub fn assign_select_value(
        &mut self,
        offset: usize,
        v: &AssignedValue<N>,
        encode: N,
        selector: &AssignedValue<N>,
    ) -> AssignedValue<N> {
        //println!("Select [offset, v, encode, value] {:?} {:?} {:?} {:?}", offset, v.val, encode, selector.val);
        if offset >= self.select_fix_record.len() {
            self.select_adv_record.resize(1 << 20, [(None, false); 2]);
            self.select_fix_record.resize(1 << 20, [None; 2]);
        }

        if offset >= self.select_height {
            self.select_height = offset + 1;
        }

        assert!(offset < 1 << 20);

        self.select_adv_record[offset][0].0 = Some(v.val);
        self.select_adv_record[offset][1].0 = Some(selector.val);
        let selector_cell = Cell::new(Chip::SelectChip, 1, offset);
        self.permutations.push((selector_cell, selector.cell));
        self.enable_permute(&selector_cell);
        self.enable_permute(&selector.cell);
        self.select_fix_record[offset][0] = Some(encode);
        self.select_fix_record[offset][1] = Some(N::one());

        AssignedValue::new(Chip::SelectChip, 0, offset, v.val)
    }

    pub fn assign_range_value(
        &mut self,
        offset: usize,
        (v, decompose_v): (N, Vec<N>),
        leading_bits: u64,
    ) -> AssignedValue<N> {
        assert!(decompose_v.len() as u64 <= RANGE_VALUE_DECOMPOSE);
        self.ensure_range_record_size(offset + 1 + MAX_CHUNKS as usize);

        self.range_fix_record[offset][0] = Some(N::one());
        self.range_adv_record[offset][0].0 = Some(v);

        // a row placeholder
        self.range_fix_record[offset + MAX_CHUNKS as usize][0] = Some(N::zero());

        for (index, v) in decompose_v.iter().enumerate() {
            let col = index / MAX_CHUNKS as usize;
            let row_offset = index % MAX_CHUNKS as usize;

            if col == VALUE_COLUMNS - 1 {
                self.range_fix_record[offset + 1 + row_offset][1] =
                    if index != decompose_v.len() - 1 {
                        Some(N::from(COMMON_RANGE_BITS as u64))
                    } else {
                        Some(N::from(leading_bits))
                    };
            }

            self.range_adv_record[offset + 1 + row_offset][col].0 = Some(*v);
        }

        AssignedValue::new(Chip::RangeChip, 0, offset, v)
    }
}
