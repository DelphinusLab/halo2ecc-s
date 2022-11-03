use crate::circuit::base_chip::{BaseChip, FIXED_COLUMNS, MUL_COLUMNS, VAR_COLUMNS};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Region},
    plonk::Error,
};
use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Chip {
    BaseChip,
    RangeChip,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Cell {
    pub region: Chip,
    pub col: usize,
    pub row: usize,
}

impl Cell {
    pub fn new(region: Chip, col: usize, row: usize) -> Self {
        Self { region, col, row }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct AssignedValue<N: FieldExt> {
    pub cell: Cell,
    pub val: N,
}

#[derive(Debug, Copy, Clone)]
pub struct AssignedCondition<N: FieldExt>(pub AssignedValue<N>);

impl<'a, N: FieldExt> AssignedValue<N> {
    pub fn new(region: Chip, col: usize, row: usize, val: N) -> Self {
        Self {
            cell: Cell::new(region, col, row),
            val,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ValueSchema<'a, N: FieldExt> {
    Assigned(&'a AssignedValue<N>),
    Unassigned(N),
}

impl<'a, N: FieldExt> ValueSchema<'a, N> {
    pub fn value(self) -> N {
        match self {
            ValueSchema::Assigned(v) => v.val,
            ValueSchema::Unassigned(v) => v,
        }
    }

    pub fn cell(&self) -> Option<Cell> {
        match self {
            ValueSchema::Assigned(AssignedValue { cell, .. }) => Some(*cell),
            ValueSchema::Unassigned(_) => None,
        }
    }
}

#[macro_export]
macro_rules! pair {
    ($x: expr, $y: expr) => {
        (crate::context::ValueSchema::from($x), ($y))
    };
}

impl<'a, N: FieldExt> From<N> for ValueSchema<'a, N> {
    fn from(v: N) -> Self {
        Self::Unassigned(v)
    }
}

impl<'a, N: FieldExt> From<&'a AssignedValue<N>> for ValueSchema<'a, N> {
    fn from(v: &'a AssignedValue<N>) -> Self {
        Self::Assigned(v)
    }
}

#[derive(Debug, Clone)]
pub struct Context<N: FieldExt> {
    pub records: Arc<Mutex<Records<N>>>,
    pub base_offset: Box<usize>,
    pub range_ofset: Box<usize>,
}

impl<N: FieldExt> Context<N> {
    pub fn new() -> Self {
        Self {
            records: Arc::new(Mutex::new(Records::default())),
            base_offset: Box::new(0),
            range_ofset: Box::new(0),
        }
    }
}

#[derive(Debug, Default)]
pub struct Records<N: FieldExt> {
    pub adv_record: Vec<[(Option<N>, bool); VAR_COLUMNS]>,
    pub fix_record: Vec<[Option<N>; FIXED_COLUMNS]>,
    pub permutations: Vec<(Cell, Cell)>,
    pub adv_cell: Vec<[Option<AssignedCell<N, N>>; VAR_COLUMNS]>,
    pub height: usize,
}

impl<N: FieldExt> Records<N> {
    pub fn assign_all(
        &mut self,
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<(), Error> {
        let mut cell_cache = HashMap::new();
        self.adv_record.truncate(self.height);
        self.fix_record.truncate(self.height);

        for (row, advs) in self.adv_record.iter_mut().enumerate() {
            for (col, adv) in advs.iter_mut().enumerate() {
                if adv.0.is_some() || adv.1 {
                    let cell = region.assign_advice(
                        || "base",
                        base_chip.config.base[col],
                        row,
                        || Ok(adv.0.unwrap_or_default()),
                    )?;
                    if adv.1 {
                        cell_cache.insert(Cell::new(Chip::BaseChip, row, col), cell);
                    }
                }
            }
        }

        for (row, fixes) in self.fix_record.iter_mut().enumerate() {
            for (col, fix) in fixes.iter_mut().enumerate() {
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

        for (left, right) in self.permutations.iter() {
            let left = cell_cache.get(&left).unwrap();
            let right = cell_cache.get(&right).unwrap();
            region.constrain_equal(left.cell(), right.cell())?;
        }

        Ok(())
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

        if offset <= self.adv_record.len() {
            let adv_default = (None, false);
            let to_len = (offset + EXTEND_SIZE) & !(EXTEND_SIZE - 1);
            self.adv_record.resize(to_len, [adv_default; VAR_COLUMNS]);
            self.fix_record.resize(to_len, [None; FIXED_COLUMNS]);
        }

        if offset >= self.height {
            self.height = offset + 1;
        }

        for (i, (base, coeff)) in base_coeff_pairs.into_iter().enumerate() {
            match base.cell() {
                Some(cell) => {
                    self.permutations
                        .push((cell, Cell::new(Chip::BaseChip, i, offset)));
                    self.adv_record[offset][i].1 = true;
                }
                _ => {}
            }
            self.fix_record[offset][i] = Some(coeff);
            self.adv_record[offset][i].0 = Some(base.value());
        }

        let (mul_coeffs, next) = mul_next_coeffs;
        for (i, mul_coeff) in mul_coeffs.into_iter().enumerate() {
            self.fix_record[offset][VAR_COLUMNS + i] = Some(mul_coeff);
        }

        if next.is_some() {
            self.fix_record[offset][VAR_COLUMNS + MUL_COLUMNS] = next;
        }

        if constant.is_some() {
            self.fix_record[offset][VAR_COLUMNS + MUL_COLUMNS + 1] = constant;
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
                self.permutations
                    .push((cell, Cell::new(Chip::BaseChip, i, offset)));
                self.adv_record[offset][i].1 = true;
            }
            _ => {}
        }
        self.fix_record[offset][i] = Some(coeff);
        self.adv_record[offset][i].0 = Some(base.value());
    }
}
