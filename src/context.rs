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
    pub val: Option<N>,
}

#[derive(Debug, Clone)]
pub enum ValueSchema<'a, N: FieldExt> {
    Assigned(&'a AssignedValue<N>),
    Unassigned(Option<N>),
}

impl<'a, N: FieldExt> ValueSchema<'a, N> {
    pub fn value(self) -> Option<N> {
        match self {
            ValueSchema::Assigned(v) => v.val.clone(),
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
        Self::Unassigned(Some(v))
    }
}

impl<'a, N: FieldExt> From<Option<N>> for ValueSchema<'a, N> {
    fn from(v: Option<N>) -> Self {
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
    pub base_offset: usize,
    pub range_ofset: usize,
}

impl<N: FieldExt> Context<N> {
    pub fn new() -> Self {
        Self {
            records: Arc::new(Mutex::new(Records::default())),
            base_offset: 0,
            range_ofset: 0,
        }
    }
}

#[derive(Debug, Default)]
pub struct Records<N: FieldExt> {
    pub adv_record: Vec<[(Option<N>, bool); VAR_COLUMNS]>,
    pub fix_record: Vec<[Option<N>; FIXED_COLUMNS]>,
    pub permutations: Vec<(Cell, Cell)>,
    pub adv_cell: Vec<[Option<AssignedCell<N, N>>; VAR_COLUMNS]>,
}

impl<N: FieldExt> Records<N> {
    pub fn assign_all(
        &mut self,
        region: &mut Region<'_, N>,
        base_chip: &BaseChip<N>,
    ) -> Result<(), Error> {
        let mut cell_cache = HashMap::new();

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
}
