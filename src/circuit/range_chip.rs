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
pub const ADV_COLUMNS: usize = VALUE_COLUMNS + 1;
pub const RANGE_VALUE_DECOMPOSE: u64 = MAX_CHUNKS * VALUE_COLUMNS as u64;
pub const TAG_RANGE_VALUE_COLUMN: usize = 1;

#[derive(Clone, Debug)]
pub struct RangeChipConfig {
    pub range_tag_table_column: TableColumn,
    pub range_value_table_column: TableColumn,

    pub value_acc_sel: Column<Fixed>,
    pub tag: Column<Fixed>,
    pub values: [Column<Advice>; ADV_COLUMNS],
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
        assert!(VALUE_COLUMNS >= 1);

        let value_acc_sel = meta.fixed_column();
        let tag = meta.fixed_column();
        let range_tag_table_column = meta.lookup_table_column();
        let range_value_table_column = meta.lookup_table_column();
        let values = [(); ADV_COLUMNS].map(|_| meta.advice_column());
        let value_acc = values[0];

        meta.enable_equality(value_acc);
        meta.enable_equality(values[TAG_RANGE_VALUE_COLUMN]);

        meta.lookup("tag range check", |meta| {
            let tag = meta.query_fixed(tag, Rotation::cur());
            let value = meta.query_advice(values[TAG_RANGE_VALUE_COLUMN], Rotation::cur());

            vec![
                (tag, range_tag_table_column),
                (value, range_value_table_column),
            ]
        });

        for col in 1..ADV_COLUMNS {
            if col != TAG_RANGE_VALUE_COLUMN {
                meta.lookup("common range check", |meta| {
                    let value = meta.query_advice(values[col], Rotation::cur());
                    vec![
                        (
                            Expression::Constant(N::from(COMMON_RANGE_BITS)),
                            range_tag_table_column,
                        ),
                        (value, range_value_table_column),
                    ]
                });
            }
        }

        meta.create_gate("block first sum", |meta| {
            let value_acc_sel = meta.query_fixed(value_acc_sel, Rotation::cur());
            let value_acc = meta.query_advice(value_acc, Rotation::cur());
            let shift_unit = bn_to_field::<N>(&(BigUint::from(1u64) << COMMON_RANGE_BITS));
            let mut shift_acc = N::one();

            let mut acc = None;
            for col in (1..ADV_COLUMNS).rev() {
                for row in 0..MAX_CHUNKS as i32 {
                    let c = meta.query_advice(values[col], Rotation(row));
                    if let Some(_acc) = acc {
                        acc = Some(_acc + c * Expression::Constant(shift_acc))
                    } else {
                        acc = Some(c * Expression::Constant(shift_acc))
                    }
                    shift_acc = shift_acc * &shift_unit;
                }
            }

            vec![value_acc_sel * (acc.unwrap() - value_acc)]
        });

        RangeChipConfig {
            range_tag_table_column,
            range_value_table_column,
            tag,
            values,
            value_acc_sel,
        }
    }

    pub fn init_table(&self, layouter: &mut impl Layouter<N>) -> Result<(), Error> {
        layouter.assign_table(
            || "common range table",
            |mut table| {
                let mut offset = 0;
                for tag in 0..COMMON_RANGE_BITS + 1 {
                    for value in 0..1 << tag {
                        table.assign_cell(
                            || "range tag",
                            self.config.range_tag_table_column,
                            offset,
                            || Ok(N::from(tag as u64)),
                        )?;
                        table.assign_cell(
                            || "range value",
                            self.config.range_value_table_column,
                            offset,
                            || Ok(N::from(value as u64)),
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
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize;
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
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize;
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
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize;
        res
    }

    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, self.info().d_leading_decompose, &info.common_range_mask);
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res =
            records.assign_range_value(self.ctx.borrow_mut().range_offset, v, info.d_leading_bits);
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize;
        res
    }
}
