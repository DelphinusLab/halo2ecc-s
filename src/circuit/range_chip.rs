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

/*
 *  Range chip is used to assigned range constrained cell.
 *
 *  | acc lines (fixed) | acc value | tag (fixed) | tagged range | common range |
 *  |     acc_lines     |    acc    |     tag3    |      v3      |      v0      |
 *  |                   |           |     tag4    |      v4      |      v1      |
 *  |                   |           |     tag5    |      v5      |      v2      |
 *
 *  lookup constraints:
 *  v0, v1, v2 is in range (0..common_range)
 *  guaranteed by lookup constraint: (COMMON_RANGE_BITS, col(common range)) in (range_tag_table_column, range_value_table_column)
 *
 *  v3 is in range (0 .. 1 << tag3), v4 is in range (0 .. 1 << tag4), v5 is in range (0 .. 1 << tag5),
 *  guaranteed by lookup constraint: (col(tag), col(tagged range)) in (range_tag_table_column, range_value_table_column)
 *
 *  (range_tag_table_column, range_value_table_column) contains:
 *  (0, 0)
 *  (1, 0), (1, 1)
 *  (2, 0), (2, 1), (2, 2), (2, 3)
 *  ...
 *  (COMMON_RANGE_BITS, 0), (COMMON_RANGE_BITS, 1), ..., (COMMON_RANGE_BITS, (1 << COMMON_RANGE_BITS) - 1)
 *
 *  accumulate constraints:
 *  acc_lines = 1 -> acc = v3
 *  acc_lines = 2 -> acc = v0 + v1 * common_range ^ 1 + v3 * common_range ^ 2 + v4 * common_range ^ 3
 *  acc_lines = 3 -> acc = v0 + v1 * common_range ^ 1 + v2 * common_range ^ 2 + v3 * common_range ^ 3
 *                            + v4 * common_range ^ 4 + v5 * common_range ^ 5
 *
 *  acc_lines = 1 can limit range bits in [0, common_range_bits]
 *  acc_lines = 2 can limit range bits in [common_range_bits * 2, common_range_bits * 4]
 *  acc_lines = 3 can limit range bits in [common_range_bits * 3, common_range_bits * 6]
 */
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
        assert!(RANGE_CHIP_RANGE_COLUMNS >= 1);

        let fix_cols = [0; RANGE_CHIP_FIX_COLUMNS].map(|_| meta.fixed_column());
        let adv_cols = [0; RANGE_CHIP_ADV_COLUMNS].map(|_| meta.advice_column());
        let range_tag_table_column = meta.lookup_table_column();
        let range_value_table_column = meta.lookup_table_column();

        let tag = fix_cols[RangeFixColIndex::TagCol as usize];
        let acc_lines = fix_cols[RangeFixColIndex::AccLinesCol as usize];

        let value_acc = adv_cols[RangeAdvColIndex::ValueAccCol as usize];
        let tagged_range_col = adv_cols[RangeAdvColIndex::TaggedRangeCol as usize];
        let common_range_col = adv_cols[RangeAdvColIndex::CommonRangeCol as usize];

        meta.enable_equality(value_acc);

        meta.lookup("tag range check", |meta| {
            let tag = meta.query_fixed(tag, Rotation::cur());
            let value = meta.query_advice(tagged_range_col, Rotation::cur());

            vec![
                (tag, range_tag_table_column),
                (value, range_value_table_column),
            ]
        });
        meta.lookup("common range check", |meta| {
            let value = meta.query_advice(common_range_col, Rotation::cur());
            vec![
                (
                    Expression::Constant(N::from(COMMON_RANGE_BITS)),
                    range_tag_table_column,
                ),
                (value, range_value_table_column),
            ]
        });

        assert!(RANGE_CHIP_RANGE_COLUMNS == 2);

        meta.create_gate("acc value check one line", |meta| {
            let acc_lines = meta.query_fixed(acc_lines, Rotation::cur());
            let value_acc = meta.query_advice(value_acc, Rotation::cur());

            let mut acc = value_acc.clone();
            let v = meta.query_advice(tagged_range_col, Rotation(0 as i32));
            acc = acc - v;

            acc = acc * acc_lines.clone();
            for root in 1..=3 {
                if root != 1 {
                    acc = acc * (acc_lines.clone() - Expression::Constant(N::from(root as u64)));
                }
            }
            vec![acc]
        });

        meta.create_gate("acc value check two lines", |meta| {
            let acc_lines = meta.query_fixed(acc_lines, Rotation::cur());
            let value_acc = meta.query_advice(value_acc, Rotation::cur());
            let shift_unit = N::from(1u64 << COMMON_RANGE_BITS);

            assert!(RANGE_CHIP_RANGE_COLUMNS == 2);

            let mut acc = value_acc.clone();
            let mut shift = N::one();

            for j in 0..2 {
                let v = meta.query_advice(common_range_col, Rotation(j as i32));
                acc = acc - v * Expression::Constant(shift);
                shift = shift * shift_unit;
            }

            for j in 0..2 {
                let v = meta.query_advice(tagged_range_col, Rotation(j as i32));
                acc = acc - v * Expression::Constant(shift);
                shift = shift * shift_unit;
            }

            acc = acc * acc_lines.clone();
            for root in 1..=3 {
                if root != 2 {
                    acc = acc * (acc_lines.clone() - Expression::Constant(N::from(root as u64)));
                }
            }

            vec![acc]
        });

        meta.create_gate("acc value check three lines", |meta| {
            let acc_lines = meta.query_fixed(acc_lines, Rotation::cur());
            let value_acc = meta.query_advice(value_acc, Rotation::cur());
            let shift_unit = N::from(1u64 << COMMON_RANGE_BITS);

            assert!(RANGE_CHIP_RANGE_COLUMNS == 2);

            let mut acc = value_acc.clone();
            let mut shift = N::one();

            for j in 0..3 {
                let v = meta.query_advice(common_range_col, Rotation(j as i32));
                acc = acc - v * Expression::Constant(shift);
                shift = shift * shift_unit;
            }

            for j in 0..3 {
                let v = meta.query_advice(tagged_range_col, Rotation(j as i32));
                acc = acc - v * Expression::Constant(shift);
                shift = shift * shift_unit;
            }

            acc = acc * acc_lines.clone();
            for root in 1..=3 {
                if root != 3 {
                    acc = acc * (acc_lines.clone() - Expression::Constant(N::from(root as u64)));
                }
            }

            vec![acc]
        });

        RangeChipConfig {
            range_tag_table_column,
            range_value_table_column,
            adv_cols,
            fix_cols,
        }
    }

    pub fn init_table(&self, layouter: &impl Layouter<N>) -> Result<(), Error> {
        layouter.assign_table(
            || "common range table",
            |table| {
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
    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N>;
}

pub fn decompose_bn<N: FieldExt>(bn: &BigUint, decompose: u64, mask: &BigUint) -> (N, Vec<N>) {
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
        let v = bn_to_field(bn);
        let offset = self.ctx.borrow().range_offset;
        let res = self.ctx.borrow_mut().records.assign_one_line_range_value(
            offset,
            &[v][..],
            v,
            COMMON_RANGE_BITS,
        );
        self.ctx.borrow_mut().range_offset += 1;
        res
    }

    fn assign_nonleading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(
            bn,
            MAX_CHUNKS * RANGE_CHIP_RANGE_COLUMNS as u64,
            &self.info().common_range_mask,
        );
        let offset = self.ctx.borrow().range_offset;
        let (res, offset_increase) =
            self.ctx
                .borrow_mut()
                .records
                .assign_range_value(offset, v.1, v.0, info.limb_bits);
        self.ctx.borrow_mut().range_offset += offset_increase as usize;
        res
    }

    fn assign_w_ceil_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(
            bn,
            self.info().w_ceil_leading_decompose,
            &info.common_range_mask,
        );
        let offset = self.ctx.borrow().range_offset;
        let (res, offset_increase) = self.ctx.borrow_mut().records.assign_range_value(
            offset,
            v.1,
            v.0,
            info.w_ceil_bits % info.limb_bits,
        );
        self.ctx.borrow_mut().range_offset += offset_increase as usize;
        res
    }

    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, self.info().d_leading_decompose, &info.common_range_mask);
        let offset = self.ctx.borrow().range_offset;
        let (res, offset_increase) = self.ctx.borrow_mut().records.assign_range_value(
            offset,
            v.1,
            v.0,
            info.d_bits % info.limb_bits,
        );
        self.ctx.borrow_mut().range_offset += offset_increase as usize;
        res
    }
}
