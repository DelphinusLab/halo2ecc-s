use std::marker::PhantomData;

use halo2_proofs::arithmetic::FieldExt;

use crate::range_info::LIMBS;

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
pub struct AssignedInteger<W: FieldExt, N: FieldExt> {
    pub limbs_le: [AssignedValue<N>; LIMBS],
    pub native: AssignedValue<N>,
    pub times: usize,
    _mark: PhantomData<W>,
}

impl<W: FieldExt, N: FieldExt> AssignedInteger<W, N> {
    pub fn new(limbs_le: [AssignedValue<N>; LIMBS], native: AssignedValue<N>, times: usize) -> Self {
        Self {
            limbs_le,
            native,
            times: 1,
            _mark: PhantomData,
        }
    }
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
        (crate::assign::ValueSchema::from($x), ($y))
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
