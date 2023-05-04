use crate::{assign::AssignedValue, context::IntegerContext, range_info::*};

use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use std::{marker::PhantomData, sync::Arc, vec};

/**
 * |limb_info | selector | encoded_offset | is_lookup |
 * |----------| ---------| -------------  |-----------|
 * | limb[0]  |    s     | --g----------  | 0 for set |
 * | limb[1]  |    s     | --g----------  | 1 for get |
 *
 * (limb_info, encode(selector, group), limboffset) in (lookup_info, comp_selector, limb_offset)
 */

#[derive(Clone, Debug)]
pub struct SelectChipConfig {
    pub limb_info: Column<Advice>,
    pub selector: Column<Advice>,
    pub encoded_offset: Column<Fixed>,
    pub is_lookup: Column<Fixed>,
}

pub struct SelectChip<N: FieldExt> {
    pub config: SelectChipConfig,
    pub _phantom: PhantomData<N>,
}

impl<N: FieldExt> SelectChip<N> {
    pub fn new(config: SelectChipConfig) -> Self {
        SelectChip {
            config,
            _phantom: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> SelectChipConfig {
        let limb_info = meta.advice_column();
        let selector = meta.advice_column();
        let encoded_offset = meta.fixed_column();
        let is_lookup = meta.fixed_column();

        meta.enable_equality(limb_info);
        meta.enable_equality(selector);

        meta.lookup_any("perform bisect lookup", |meta| {
            let limb_info = meta.query_advice(limb_info, Rotation::cur());
            let selector = meta.query_advice(selector, Rotation::cur());
            let encoded_offset = meta.query_fixed(encoded_offset, Rotation::cur());
            let is_lookup = meta.query_fixed(is_lookup, Rotation::cur());

            let selector_encode_shift = N::from(1u64 << 20);

            vec![
                (limb_info.clone(), limb_info.clone()),
                (
                    (selector * selector_encode_shift + encoded_offset.clone()),
                    encoded_offset.clone(),
                ),
                (Expression::Constant(N::zero()), is_lookup.clone()),
            ]
        });

        SelectChipConfig {
            limb_info,
            selector,
            encoded_offset,
            is_lookup,
        }
    }
}

// A range info that implements limb assignment for W on N
pub trait SelectChipOps<W: BaseExt, N: FieldExt> {
    fn info(&self) -> Arc<RangeInfo<W, N>>;
    fn assign_cache_value(
        &mut self,
        v: &AssignedValue<N>,
        offset: usize,
        group_index: usize,
        selector: usize,
    );
    fn assign_selected_value(
        &mut self,
        v: &AssignedValue<N>,
        offset: usize,
        group_index: usize,
        selector: &AssignedValue<N>,
    );
}

fn encode_offset(g: usize, offset: usize, limb_offset: usize) -> usize {
    g * 1024 + limb_offset + (offset << 20)
}

impl<W: BaseExt, N: FieldExt> SelectChipOps<W, N> for IntegerContext<W, N> {
    fn info(&self) -> Arc<RangeInfo<W, N>> {
        self.info.clone()
    }

    fn assign_cache_value(
        &mut self,
        v: &AssignedValue<N>,
        offset: usize,
        group_index: usize,
        selector: usize,
    ) {
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let encoded_offset = encode_offset(group_index, selector, offset);
        records.assign_cache_value(
            self.ctx.borrow_mut().select_offset,
            v,
            N::from(encoded_offset as u64),
        );
        self.ctx.borrow_mut().select_offset += 1;
    }
    fn assign_selected_value(
        &mut self,
        v: &AssignedValue<N>,
        offset: usize,
        group_index: usize,
        selector: &AssignedValue<N>,
    ) {
        let records_mtx = self.ctx.borrow().records.clone();
        let mut records = records_mtx.lock().unwrap();
        let encoded_offset = encode_offset(group_index, 0, offset);
        records.assign_select_value(
            self.ctx.borrow_mut().select_offset,
            v,
            N::from(encoded_offset as u64),
            selector,
        );
        self.ctx.borrow_mut().select_offset += 1;
    }
}