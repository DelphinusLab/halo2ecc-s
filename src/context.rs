use crate::{
    assign::{AssignedValue, Cell, Chip, ValueSchema},
    circuit::{
        base_chip::{BaseChip, FIXED_COLUMNS, MUL_COLUMNS, VAR_COLUMNS},
        range_chip::RangeChip,
    },
    range_info::{RangeClass, RangeInfo, MAX_CHUNKS},
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Region},
    plonk::Error,
};
use std::collections::HashSet;
use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

#[derive(Debug, Clone)]
pub struct Context<N: FieldExt> {
    pub records: Arc<Mutex<Records<N>>>,
    pub base_offset: Box<usize>,
    pub range_offset: Box<usize>,
    pub range_info: Option<RangeInfo<N>>,
}

impl<N: FieldExt> Context<N> {
    pub fn new() -> Self {
        Self {
            records: Arc::new(Mutex::new(Records::default())),
            base_offset: Box::new(0),
            range_offset: Box::new(0),
            range_info: None,
        }
    }

    pub fn new_with_range_info<W: FieldExt>() -> Self {
        Self {
            records: Arc::new(Mutex::new(Records::default())),
            base_offset: Box::new(0),
            range_offset: Box::new(0),
            range_info: Some(RangeInfo::<N>::new::<W>()),
        }
    }
}

#[derive(Debug, Default)]
pub struct Records<N: FieldExt> {
    pub base_adv_record: Vec<[Option<N>; VAR_COLUMNS]>,
    pub base_fix_record: Vec<[Option<N>; FIXED_COLUMNS]>,
    pub base_height: usize,

    pub range_adv_record: Vec<Option<N>>,
    pub range_fix_record: Vec<[Option<N>; 2]>,
    pub range_height: usize,

    pub permutations: Vec<(Cell, Cell)>,
    pub permutations_cells: HashSet<Cell>,
}

impl<N: FieldExt> Records<N> {
    fn _assign_to_base_chip(
        &self,
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<HashMap<Cell, AssignedCell<N, N>>, Error> {
        let mut cells = HashMap::<Cell, AssignedCell<N, N>>::new();

        for (row, advs) in self.base_adv_record.iter().enumerate() {
            if row >= self.base_height {
                break;
            }

            for (col, adv) in advs.iter().enumerate() {
                if adv.is_some() {
                    let cell = region.assign_advice(
                        || "base",
                        base_chip.config.base[col],
                        row,
                        || Ok(adv.unwrap()),
                    )?;
                    let idx = Cell::new(Chip::BaseChip, col, row);
                    if self.permutations_cells.contains(&idx) {
                        cells.insert(idx, cell);
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

    pub fn _assign_to_range_chip<W: FieldExt>(
        &self,
        region: &mut Region<'_, N>,
        range_chip: &RangeChip<W, N>,
        mut cells: HashMap<Cell, AssignedCell<N, N>>,
    ) -> Result<HashMap<Cell, AssignedCell<N, N>>, Error> {
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
            if adv.is_some() {
                let cell = region.assign_advice(
                    || "range var",
                    range_chip.config.value,
                    row,
                    || Ok(adv.unwrap()),
                )?;
                let idx = Cell::new(Chip::RangeChip, 0, row);
                if self.permutations_cells.contains(&idx) {
                    cells.insert(idx, cell);
                }
            }
        }

        Ok(cells)
    }

    pub fn _assign_permutation(
        &self,
        region: &mut Region<'_, N>,
        cells: HashMap<Cell, AssignedCell<N, N>>,
    ) -> Result<HashMap<Cell, AssignedCell<N, N>>, Error> {
        for (left, right) in self.permutations.iter() {
            let left = cells.get(&left).unwrap().cell();
            let right = cells.get(&right).unwrap().cell();
            region.constrain_equal(left, right)?;
        }

        Ok(cells)
    }

    pub fn assign_all_in_base(
        &self,
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<HashMap<Cell, AssignedCell<N, N>>, Error> {
        let cells = self._assign_to_base_chip(region, base_chip)?;
        self._assign_permutation(region, cells)
    }

    pub fn assign_all<W: FieldExt>(
        &self,
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
        range_chip: &RangeChip<W, N>,
    ) -> Result<HashMap<Cell, AssignedCell<N, N>>, Error> {
        let cells = self._assign_to_base_chip(region, base_chip)?;
        let cells = self._assign_to_range_chip(region, range_chip, cells)?;
        self._assign_permutation(region, cells)
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
            self.base_adv_record.resize(to_len, [None; VAR_COLUMNS]);
            self.base_fix_record.resize(to_len, [None; FIXED_COLUMNS]);
        }

        if offset >= self.base_height {
            self.base_height = offset + 1;
        }

        for (i, (base, coeff)) in base_coeff_pairs.into_iter().enumerate() {
            match base.cell() {
                Some(cell) => {
                    let idx = Cell::new(Chip::BaseChip, i, offset);
                    self.permutations_cells.insert(idx);
                    self.permutations_cells.insert(cell);
                    self.permutations.push((cell, idx));
                }
                _ => {}
            }
            self.base_fix_record[offset][i] = Some(coeff);
            self.base_adv_record[offset][i] = Some(base.value());
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
                self.permutations_cells.insert(idx);
                self.permutations_cells.insert(cell);
                self.permutations.push((cell, idx));
            }
            _ => {}
        }
        self.base_fix_record[offset][i] = Some(coeff);
        self.base_adv_record[offset][i] = Some(base.value());
    }

    pub fn assign_range_value(
        &mut self,
        offset: usize,
        (v, chunks): (N, Vec<N>),
        leading_class: RangeClass,
    ) -> AssignedValue<N> {
        const EXTEND_SIZE: usize = 16;

        let end_offset = offset + 1 + MAX_CHUNKS;

        if end_offset >= self.range_adv_record.len() {
            let to_len = (end_offset + EXTEND_SIZE) & !(EXTEND_SIZE - 1);
            self.range_adv_record.resize(to_len, None);
            self.range_fix_record.resize(to_len, [None; 2]);
        }

        if end_offset >= self.range_height {
            self.range_height = end_offset + 1;
        }

        self.range_fix_record[offset][0] = Some(N::one());
        self.range_adv_record[offset] = Some(v);

        // a row placeholder
        self.range_fix_record[offset + MAX_CHUNKS][0] = Some(N::zero());

        for i in 0..chunks.len() - 1 {
            self.range_fix_record[offset + 1 + i][1] = Some(N::from(RangeClass::Common as u64));
        }
        self.range_fix_record[offset + 1 + chunks.len() - 1][1] =
            Some(N::from(leading_class as u64));

        for i in 0..chunks.len() {
            self.range_adv_record[offset + 1 + i] = Some(chunks[i]);
        }

        AssignedValue::new(Chip::RangeChip, 0, offset, v)
    }
}
