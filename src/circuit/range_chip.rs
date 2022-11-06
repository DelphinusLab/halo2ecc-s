use crate::{assign::AssignedValue, context::Context, range_info::*, utils::bn_to_field};

use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, TableColumn},
    poly::Rotation,
};
use num_bigint::BigUint;
use std::{marker::PhantomData, sync::Arc, vec};

const CLASS_SHIFT_BITS: usize = 128;

#[derive(Clone, Debug)]
pub struct RangeChipConfig {
    pub range_table_column: TableColumn,
    pub block_first: Column<Fixed>,
    pub range_class: Column<Fixed>,
    pub value: Column<Advice>,
}

pub struct RangeChip<W: BaseExt, N: FieldExt> {
    pub config: RangeChipConfig,
    pub _phantom: PhantomData<(N, W)>,
}

impl<W: BaseExt, N: FieldExt> RangeChip<W, N> {
    pub fn new(config: RangeChipConfig) -> Self {
        RangeChip {
            config,
            _phantom: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> RangeChipConfig {
        let block_first = meta.fixed_column();
        let range_class = meta.fixed_column();
        let range_table_column = meta.lookup_table_column();
        let value = meta.advice_column();

        meta.enable_equality(value);

        meta.lookup("range check", |meta| {
            let class = meta.query_fixed(range_class, Rotation::cur());
            let is_block_first = meta.query_fixed(block_first, Rotation::cur());
            let v = meta.query_advice(value, Rotation::cur());

            let class_shift = bn_to_field::<N>(&(BigUint::from(1u64) << CLASS_SHIFT_BITS));
            vec![(
                (class * Expression::Constant(class_shift) + v)
                    * (Expression::Constant(N::one()) - is_block_first),
                range_table_column,
            )]
        });

        meta.create_gate("block first sum", |meta| {
            let is_block_first = meta.query_fixed(block_first, Rotation::cur());
            let shift_unit = bn_to_field::<N>(&(BigUint::from(1u64) << COMMON_RANGE_BITS));
            let mut shift_acc = N::one();

            let mut acc = meta.query_advice(value, Rotation(1));
            for i in 1..MAX_CHUNKS as i32 {
                let c = meta.query_advice(value, Rotation(i + 1));
                shift_acc = shift_acc * &shift_unit;
                acc = acc + c * Expression::Constant(shift_acc);
            }

            vec![is_block_first * (acc - meta.query_advice(value, Rotation::cur()))]
        });

        RangeChipConfig {
            range_table_column,
            block_first,
            range_class,
            value,
        }
    }

    pub fn init_table(
        &self,
        layouter: &mut impl Layouter<N>,
        range_info: &RangeInfo<N>,
    ) -> Result<(), Error> {
        let class_shift = bn_to_field::<N>(&(BigUint::from(1u64) << CLASS_SHIFT_BITS));
        layouter.assign_table(
            || "common range table",
            |mut table| {
                let mut offset = 0;

                table.assign_cell(
                    || "range table",
                    self.config.range_table_column,
                    offset,
                    || Ok(N::from(0u64)),
                )?;
                offset += 1;

                macro_rules! assign_range {
                    ($bits:expr, $class:expr) => {
                        let prefix = N::from($class as u64) * &class_shift;
                        for i in 0..1 << $bits {
                            table.assign_cell(
                                || "range table",
                                self.config.range_table_column,
                                offset,
                                || Ok(prefix + N::from(i as u64)),
                            )?;
                            offset += 1;
                        }
                    };
                }

                assign_range!(COMMON_RANGE_BITS, RangeClass::Common);
                assign_range!(range_info.d_leading_bits, RangeClass::DLeading);
                assign_range!(range_info.w_ceil_leading_bits, RangeClass::WCeilLeading);
                assign_range!(range_info.n_floor_leading_bits, RangeClass::NFloorLeading);

                Ok(())
            },
        )?;

        Ok(())
    }
}

pub trait RangeChipOps<N: FieldExt> {
    fn info(&self) -> Arc<RangeInfo<N>>;
    fn assign_common(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_nonleading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_w_ceil_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_n_floor_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
}

fn decompose_bn<N: FieldExt>(bn: &BigUint, n: usize, mask: &BigUint) -> (N, Vec<N>) {
    let v = bn_to_field::<N>(bn);
    let mut chunks = vec![];

    for i in 0..n {
        let val = (bn >> (i * COMMON_RANGE_BITS)) & mask;
        chunks.push(bn_to_field::<N>(&val));
    }

    (v, chunks)
}

impl<W: BaseExt, N: FieldExt> RangeChipOps<N> for Context<W, N> {
    fn info(&self) -> Arc<RangeInfo<N>> {
        self.range_info.clone().unwrap()
    }

    fn assign_common(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let mut records = self.records.lock().unwrap();
        let res = records.assign_single_range_value(
            *self.range_offset,
            bn_to_field(bn),
            RangeClass::Common,
        );
        *self.range_offset += 1;
        res
    }

    fn assign_nonleading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let v = decompose_bn(bn, MAX_CHUNKS, &self.info().common_range_mask);
        let mut records = self.records.lock().unwrap();
        let res = records.assign_range_value(*self.range_offset, v, RangeClass::Common);
        *self.range_offset += MAX_CHUNKS + 1;
        res
    }

    fn assign_w_ceil_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let v = decompose_bn(bn, W_CEIL_LEADING_CHUNKS, &self.info().common_range_mask);
        let mut records = self.records.lock().unwrap();
        let res = records.assign_range_value(*self.range_offset, v, RangeClass::WCeilLeading);
        *self.range_offset += MAX_CHUNKS + 1;
        res
    }

    fn assign_n_floor_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let v = decompose_bn(bn, N_FLOOR_LEADING_CHUNKS, &self.info().common_range_mask);
        let mut records = self.records.lock().unwrap();
        let res = records.assign_range_value(*self.range_offset, v, RangeClass::NFloorLeading);
        *self.range_offset += MAX_CHUNKS + 1;
        res
    }

    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let v = decompose_bn(bn, D_LEADING_CHUNKS, &self.info().common_range_mask);
        let mut records = self.records.lock().unwrap();
        let res = records.assign_range_value(*self.range_offset, v, RangeClass::DLeading);
        *self.range_offset += MAX_CHUNKS + 1;
        res
    }
}
