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

pub const RANGE_CHIP_RANGE_COLUMNS: usize = 2;
pub const RANGE_CHIP_COMMON_RANGE_COLUMNS: usize = RANGE_CHIP_RANGE_COLUMNS - 1;
pub const RANGE_CHIP_ADV_COLUMNS: usize = RANGE_CHIP_RANGE_COLUMNS + 1;
pub const RANGE_CHIP_FIX_COLUMNS: usize = 2;

pub const RANGE_VALUE_DECOMPOSE: u64 = MAX_CHUNKS * RANGE_CHIP_RANGE_COLUMNS as u64;
pub const RANGE_VALUE_DECOMPOSE_COMMON_PARTS: u64 =
    MAX_CHUNKS * RANGE_CHIP_COMMON_RANGE_COLUMNS as u64;

#[derive(Clone, Debug)]
pub struct RangeChipConfig {
    pub range_tag_table_column: TableColumn,
    pub range_value_table_column: TableColumn,

    pub adv_cols: [Column<Advice>; RANGE_CHIP_ADV_COLUMNS],
    pub fix_cols: [Column<Fixed>; RANGE_CHIP_FIX_COLUMNS],
}

pub struct RangeChip<N: FieldExt> {
    pub config: RangeChipConfig,
    pub _phantom: PhantomData<N>,
}

pub enum RangeAdvColIndex {
    ValueAccCol = 0,
    TaggedRangeCol = 1,
    CommonRangeColStart = 2,
}

pub enum RangeFixColIndex {
    ValueAccSelCol = 0,
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
        assert!(RANGE_CHIP_RANGE_COLUMNS >= 1);

        let fix_cols = [0; RANGE_CHIP_FIX_COLUMNS].map(|_| meta.fixed_column());
        let adv_cols = [0; RANGE_CHIP_ADV_COLUMNS].map(|_| meta.advice_column());
        let range_tag_table_column = meta.lookup_table_column();
        let range_value_table_column = meta.lookup_table_column();

        let tag = fix_cols[RangeFixColIndex::TagCol as usize];
        let value_acc_sel = fix_cols[RangeFixColIndex::ValueAccSelCol as usize];

        let value_acc = adv_cols[RangeAdvColIndex::ValueAccCol as usize];
        let tagged_range_col = adv_cols[RangeAdvColIndex::TaggedRangeCol as usize];
        let common_range_cols = &adv_cols[RangeAdvColIndex::CommonRangeColStart as usize..];

        meta.enable_equality(value_acc);
        meta.enable_equality(adv_cols[RangeAdvColIndex::TaggedRangeCol as usize]);

        meta.lookup("tag range check", |meta| {
            let tag = meta.query_fixed(tag, Rotation::cur());
            let value = meta.query_advice(tagged_range_col, Rotation::cur());

            vec![
                (tag, range_tag_table_column),
                (value, range_value_table_column),
            ]
        });

        for col in common_range_cols {
            meta.lookup("common range check", |meta| {
                let value = meta.query_advice(*col, Rotation::cur());
                vec![
                    (
                        Expression::Constant(N::from(COMMON_RANGE_BITS)),
                        range_tag_table_column,
                    ),
                    (value, range_value_table_column),
                ]
            });
        }

        meta.create_gate("value acc check", |meta| {
            let value_acc_sel = meta.query_fixed(value_acc_sel, Rotation::cur());
            let value_acc = meta.query_advice(value_acc, Rotation::cur());
            let shift_unit = N::from(1u64 << COMMON_RANGE_BITS);

            let mut acc = None;
            for col in common_range_cols
                .iter()
                .chain(vec![tagged_range_col].iter())
            {
                for row in 0..MAX_CHUNKS as i32 {
                    let c = meta.query_advice(*col, Rotation(row));
                    if let Some((value_acc, shift_acc)) = acc {
                        acc = Some((
                            value_acc + c * Expression::Constant(shift_acc),
                            shift_acc * &shift_unit,
                        ))
                    } else {
                        acc = Some((c, shift_unit))
                    }
                }
            }

            vec![value_acc_sel * (acc.unwrap().0 - value_acc)]
        });

        RangeChipConfig {
            range_tag_table_column,
            range_value_table_column,
            adv_cols,
            fix_cols,
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
            MAX_CHUNKS * RANGE_CHIP_RANGE_COLUMNS as u64,
            &self.info().common_range_mask,
        );
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let res = records.assign_acc_range_value(
            self.ctx.borrow_mut().range_offset,
            v,
            COMMON_RANGE_BITS,
        );
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
        let res = records.assign_acc_range_value(
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
        let res = records.assign_acc_range_value(
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
        let res = records.assign_acc_range_value(
            self.ctx.borrow_mut().range_offset,
            v,
            info.d_leading_bits,
        );
        self.ctx.borrow_mut().range_offset += MAX_CHUNKS as usize;
        res
    }
}
