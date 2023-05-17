use crate::assign::AssignedValue;
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
use halo2_proofs::plonk::TableColumn;
use halo2_proofs::poly::Rotation;
use num_bigint::BigUint;
use std::marker::PhantomData;
use std::sync::Arc;
use std::vec;

pub const MAX_CHUNKS: u64 = 3;
pub const MAX_BITS: u64 = 18;
pub const COMMON_RANGE_BITS: u64 = MAX_BITS as u64;
pub const VALUE_COLUMNS: usize = 2;
pub const RANGE_VALUE_DECOMPOSE: u64 = MAX_CHUNKS * VALUE_COLUMNS as u64;

const CLASS_SHIFT_BITS: usize = 128;

#[derive(Clone, Debug)]
pub struct RangeChipConfig {
    pub max_range_table_column: TableColumn,
    pub tag_range_table_column: TableColumn,
    pub block_first: Column<Fixed>,
    pub range_class: Column<Fixed>,
    pub values: [Column<Advice>; VALUE_COLUMNS],
}

pub struct RangeChip<N: FieldExt> {
    pub config: RangeChipConfig,
    pub _phantom: PhantomData<N>,
}

impl<N: FieldExt> RangeChip<N> {
    pub fn new(config: RangeChipConfig) -> Self {
        RangeChip {
            config,
            _phantom: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> RangeChipConfig {
        assert!(VALUE_COLUMNS > 1);

        let block_first = meta.fixed_column();
        let range_class = meta.fixed_column();
        let tag_range_table_column = meta.lookup_table_column();
        let max_range_table_column = meta.lookup_table_column();
        let values = [(); VALUE_COLUMNS].map(|_| meta.advice_column());

        meta.enable_equality(values[0]);

        meta.lookup("tag range check", |meta| {
            let class = meta.query_fixed(range_class, Rotation::cur());
            let v = meta.query_advice(values[VALUE_COLUMNS - 1], Rotation::cur());

            let class_shift = bn_to_field::<N>(&(BigUint::from(1u64) << CLASS_SHIFT_BITS));

            vec![(
                (class * Expression::Constant(class_shift) + v),
                tag_range_table_column,
            )]
        });

        for col in 0..VALUE_COLUMNS {
            meta.lookup("max range check", |meta| {
                let is_block_first = meta.query_fixed(block_first, Rotation::cur());
                let v = meta.query_advice(values[col], Rotation::cur());

                let lookup_expr = if col == 0 {
                    v * (Expression::Constant(N::one()) - is_block_first)
                } else {
                    v
                };

                vec![(lookup_expr, max_range_table_column)]
            });
        }

        meta.create_gate("block first sum", |meta| {
            let is_block_first = meta.query_fixed(block_first, Rotation::cur());
            let shift_unit = bn_to_field::<N>(&(BigUint::from(1u64) << COMMON_RANGE_BITS));
            let mut shift_acc = N::one();

            let mut acc = None;
            for col in 0..VALUE_COLUMNS {
                for row in 0..MAX_CHUNKS as i32 {
                    let c = meta.query_advice(values[col], Rotation(row + 1));
                    if let Some(_acc) = acc {
                        acc = Some(_acc + c * Expression::Constant(shift_acc))
                    } else {
                        acc = Some(c * Expression::Constant(shift_acc))
                    }
                    shift_acc = shift_acc * &shift_unit;
                }
            }

            vec![is_block_first * (acc.unwrap() - meta.query_advice(values[0], Rotation::cur()))]
        });

        RangeChipConfig {
            max_range_table_column,
            tag_range_table_column,
            block_first,
            range_class,
            values,
        }
    }

    pub fn init_table(&self, layouter: &mut impl Layouter<N>) -> Result<(), Error> {
        let class_shift = bn_to_field::<N>(&(BigUint::from(1u64) << CLASS_SHIFT_BITS));

        layouter.assign_table(
            || "common range table",
            |mut table| {
                for i in 0..1 << COMMON_RANGE_BITS {
                    table.assign_cell(
                        || "range table",
                        self.config.max_range_table_column,
                        i,
                        || Ok(N::from(i as u64)),
                    )?;
                }

                Ok(())
            },
        )?;

        layouter.assign_table(
            || "common range table",
            |mut table| {
                let mut offset = 0;

                for i in 0..COMMON_RANGE_BITS + 1 {
                    let prefix = N::from(i) * &class_shift;
                    for j in 0..1 << i {
                        table.assign_cell(
                            || "range table",
                            self.config.tag_range_table_column,
                            offset,
                            || Ok(prefix + N::from(j)),
                        )?;
                        offset += 1;
                    }
                }

                Ok(())
            },
        )?;

        Ok(())
    }
}

// A range info that implements limb assignment for W on N
pub trait RangeChipOps<W: BaseExt, N: FieldExt> {
    fn info(&self) -> Arc<RangeInfo<W, N>>;
    fn assign_common(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_nonleading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_w_ceil_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_n_floor_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
}

fn decompose_bn<N: FieldExt>(bn: &BigUint, decompose: u64, mask: &BigUint) -> (N, Vec<N>) {
    let v = bn_to_field::<N>(bn);
    let mut decompose_v = vec![];

    for i in 0..decompose {
        let val = (bn >> (i * COMMON_RANGE_BITS)) & mask;
        decompose_v.push(bn_to_field::<N>(&val));
    }

    (v, decompose_v)
}

impl<W: BaseExt, N: FieldExt> RangeChipOps<W, N> for IntegerContext<W, N> {
    fn info(&self) -> Arc<RangeInfo<W, N>> {
        self.info.clone()
    }

    fn assign_common(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res = records.assign_single_range_value(
            self.ctx.borrow_mut().range_offset,
            bn_to_field(bn),
            COMMON_RANGE_BITS,
        );
        self.ctx.borrow_mut().range_offset += 1;
        res
    }

    fn assign_nonleading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let v = decompose_bn(
            bn,
            MAX_CHUNKS * VALUE_COLUMNS as u64,
            &self.info().common_range_mask,
        );
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res =
            records.assign_range_value(self.ctx.borrow_mut().range_offset, v, COMMON_RANGE_BITS);
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize + 1;
        res
    }

    fn assign_w_ceil_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(
            bn,
            self.info().w_ceil_leading_decompose,
            &info.common_range_mask,
        );
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res = records.assign_range_value(
            self.ctx.borrow_mut().range_offset,
            v,
            info.w_ceil_leading_bits,
        );
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize + 1;
        res
    }

    fn assign_n_floor_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(
            bn,
            self.info().n_floor_leading_decompose,
            &info.common_range_mask,
        );
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res = records.assign_range_value(
            self.ctx.borrow_mut().range_offset,
            v,
            info.n_floor_leading_bits,
        );
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize + 1;
        res
    }

    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, self.info().d_leading_decompose, &info.common_range_mask);
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res =
            records.assign_range_value(self.ctx.borrow_mut().range_offset, v, info.d_leading_bits);
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize + 1;
        res
    }
}
