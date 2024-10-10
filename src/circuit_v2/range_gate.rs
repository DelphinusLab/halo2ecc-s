use crate::assign::AssignedValue;
use crate::circuit::range_chip::COMMON_RANGE_BITS;
use crate::context::IntegerContext;
use crate::range_info::*;
use crate::utils::bn_to_field;

use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::Fixed;
use halo2_proofs::poly::Rotation;
use num_bigint::BigUint;
use std::marker::PhantomData;
use std::sync::Arc;
use std::vec;

pub const RANGE_CHIP_ADV_COLUMNS: usize = 3;

#[derive(Clone, Debug)]
pub struct RangeChipConfig {
    pub cols: [Column<Advice>; RANGE_CHIP_ADV_COLUMNS],
    pub l_0: Column<Fixed>,
    pub l_active: Column<Fixed>,
    pub l_last_active: Column<Fixed>,
}

pub struct RangeChip<N: FieldExt> {
    pub config: RangeChipConfig,
    pub _phantom: PhantomData<N>,
}

#[derive(Clone, Copy)]
pub enum RangeAdvColIndex {
    ValueAccCol = 0,
    TaggedRangeCol = 1,
    CommonRangeCol = 2,
}

#[derive(Clone, Copy, PartialEq)]
pub enum RangeFixColIndex {
    AccLinesCol = 0,
    TagCol = 1,
}

impl<N: FieldExt> RangeChip<N> {
    pub fn new(config: RangeChipConfig) -> Self {
        RangeChip {
            config,
            _phantom: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> RangeChipConfig {
        let l_0 = meta.fixed_column();
        let l_active = meta.fixed_column();
        let l_last_active = meta.fixed_column();
        let mut cols = vec![];

        let max = (1 << COMMON_RANGE_BITS) - 1;
        for i in 0..RANGE_CHIP_ADV_COLUMNS {
            let col = meta.advice_column_range(
                l_0,
                l_active,
                l_last_active,
                (0, N::zero()),
                (max, N::from(max as u64)),
                (2, N::from(2u64)),
            );
            cols.push(col);
        }

        RangeChipConfig {
            cols: cols.try_into().unwrap(),
            l_0,
            l_active,
            l_last_active,
        }
    }
}
