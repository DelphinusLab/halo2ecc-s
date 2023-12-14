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
use halo2_proofs::plonk::Fixed;
use halo2_proofs::plonk::TableColumn;
use halo2_proofs::poly::Rotation;
use num_bigint::BigUint;
use std::marker::PhantomData;
use std::sync::Arc;
use std::vec;

use super::integer_chip::IntegerChipOps;

pub const MAX_BITS: u64 = 18;
pub const RANGE_VALUE_DECOMPOSE: u64 = 6;
pub const COMMON_RANGE_BITS: u64 = MAX_BITS as u64;

pub const RANGE_CHIP_ADV_COLUMNS: usize = 1;
pub const RANGE_CHIP_FIX_COLUMNS: usize = 1;

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

impl<N: FieldExt> RangeChip<N> {
    pub fn new(config: RangeChipConfig) -> Self {
        RangeChip {
            config,
            _phantom: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> RangeChipConfig {
        let fix_cols = [0; RANGE_CHIP_FIX_COLUMNS].map(|_| meta.fixed_column());
        let adv_cols = [0; RANGE_CHIP_ADV_COLUMNS].map(|_| meta.advice_column());
        let range_tag_table_column = meta.lookup_table_column();
        let range_value_table_column = meta.lookup_table_column();

        let tag = fix_cols[0];
        let tagged_range_col = adv_cols[0];
        meta.enable_equality(adv_cols[0]);

        meta.lookup("tag range check", |meta| {
            let tag = meta.query_fixed(tag, Rotation::cur());
            let value = meta.query_advice(tagged_range_col, Rotation::cur());

            vec![
                (tag, range_tag_table_column),
                (value, range_value_table_column),
            ]
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
        let res = records.assign_range_value_in_small_circuit(
            self.ctx.borrow_mut().range_offset,
            bn_to_field(bn),
            COMMON_RANGE_BITS,
        );
        self.ctx.borrow_mut().range_offset += 1;
        res
    }

    fn assign_nonleading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, info.limbs, &info.common_range_mask);

        let mut res = vec![];
        {
            let records_mtx = self.ctx.borrow().records.clone();
            let mut records = records_mtx.lock().unwrap();

            let mut shift = N::one();
            let common_range = N::from(1 << COMMON_RANGE_BITS);
            for (i, v) in v.1.into_iter().enumerate() {
                let r = records.assign_range_value_in_small_circuit(
                    self.ctx.borrow_mut().range_offset + i,
                    v,
                    COMMON_RANGE_BITS,
                );
                res.push((r, shift));
                shift *= common_range;
            }

            self.ctx.borrow_mut().range_offset += info.limbs as usize;
        }

        self.base_chip()
            .sum_with_constant(res.iter().map(|(v, s)| (v, *s)).collect(), None)
    }

    fn assign_w_ceil_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, info.w_ceil_leading_decompose, &info.common_range_mask);

        let mut res = vec![];
        {
            let records_mtx = self.ctx.borrow().records.clone();
            let mut records = records_mtx.lock().unwrap();
            let mut shift = N::one();
            let common_range = N::from(1 << COMMON_RANGE_BITS);
            for (i, v) in v.1.into_iter().enumerate() {
                let r = records.assign_range_value_in_small_circuit(
                    self.ctx.borrow_mut().range_offset + i,
                    v,
                    if i as u64 == info.w_ceil_leading_decompose - 1 {
                        info.w_ceil_leading_bits
                    } else {
                        COMMON_RANGE_BITS
                    },
                );
                res.push((r, shift));
                shift *= common_range;
            }

            self.ctx.borrow_mut().range_offset += info.w_ceil_leading_decompose as usize;
        }

        let res = self
            .base_chip()
            .sum_with_constant(res.iter().map(|(v, s)| (v, *s)).collect(), None);
        assert!(res.val == v.0);
        res
    }

    fn assign_n_floor_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, info.n_floor_leading_decompose, &info.common_range_mask);

        let mut res = vec![];
        {
            let records_mtx = self.ctx.borrow().records.clone();
            let mut records = records_mtx.lock().unwrap();
            let mut shift = N::one();
            let common_range = N::from(1 << COMMON_RANGE_BITS);
            for (i, v) in v.1.into_iter().enumerate() {
                let r = records.assign_range_value_in_small_circuit(
                    self.ctx.borrow_mut().range_offset + i,
                    v,
                    if i as u64 == info.n_floor_leading_decompose - 1 {
                        info.n_floor_leading_bits
                    } else {
                        COMMON_RANGE_BITS
                    },
                );
                res.push((r, shift));
                shift *= common_range;
            }

            self.ctx.borrow_mut().range_offset += info.n_floor_leading_decompose as usize;
        }
        let res = self
            .base_chip()
            .sum_with_constant(res.iter().map(|(v, s)| (v, *s)).collect(), None);
        assert!(res.val == v.0);
        res
    }

    fn assign_d_leading_limb(&mut self, bn: &BigUint) -> AssignedValue<N> {
        let info = self.info();
        let v = decompose_bn(bn, info.d_leading_decompose, &info.common_range_mask);

        let mut res = vec![];
        {
            let records_mtx = self.ctx.borrow().records.clone();
            let mut records = records_mtx.lock().unwrap();
            let mut shift = N::one();
            let common_range = N::from(1 << COMMON_RANGE_BITS);
            for (i, v) in v.1.into_iter().enumerate() {
                let r = records.assign_range_value_in_small_circuit(
                    self.ctx.borrow_mut().range_offset + i,
                    v,
                    if i as u64 == info.d_leading_decompose - 1 {
                        info.d_leading_bits
                    } else {
                        COMMON_RANGE_BITS
                    },
                );
                res.push((r, shift));
                shift *= common_range;
            }

            self.ctx.borrow_mut().range_offset += info.d_leading_decompose as usize;
        }
        let res = self
            .base_chip()
            .sum_with_constant(res.iter().map(|(v, s)| (v, *s)).collect(), None);
        assert!(res.val == v.0);
        res
    }
}
