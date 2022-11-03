use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Fixed},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::context::{Cell, Chip, Records, ValueSchema};

pub const VAR_COLUMNS: usize = 5;
pub const MUL_COLUMNS: usize = 1;
pub const FIXED_COLUMNS: usize = VAR_COLUMNS + MUL_COLUMNS + 2;

const EXTEND_SIZE: usize = 16;

#[derive(Clone, Debug)]
pub struct BaseChipConfig {
    pub base: [Column<Advice>; VAR_COLUMNS],
    pub coeff: [Column<Fixed>; VAR_COLUMNS],
    pub mul_coeff: [Column<Fixed>; MUL_COLUMNS],
    pub next_coeff: Column<Fixed>,
    pub constant: Column<Fixed>,
}

#[derive(Clone, Debug)]
pub struct BaseChip<N: FieldExt> {
    pub config: BaseChipConfig,
    mark: PhantomData<N>,
}

impl<N: FieldExt> BaseChip<N> {
    pub fn new(config: BaseChipConfig) -> Self {
        Self {
            config,
            mark: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> BaseChipConfig {
        let base = [(); VAR_COLUMNS].map(|_| meta.advice_column());
        let coeff = [(); VAR_COLUMNS].map(|_| meta.fixed_column());
        let mul_coeff = [(); MUL_COLUMNS].map(|_| meta.fixed_column());
        let next_coeff = meta.fixed_column();
        let constant = meta.fixed_column();

        base.iter().for_each(|c| meta.enable_equality(c.clone()));

        meta.create_gate("base_gate", |meta| {
            let _constant = meta.query_fixed(constant, Rotation::cur());
            let _next = meta.query_advice(base[VAR_COLUMNS - 1], Rotation::next());
            let _next_coeff = meta.query_fixed(next_coeff, Rotation::cur());

            let mut acc = _constant + _next * _next_coeff;
            for i in 0..VAR_COLUMNS {
                let _base = meta.query_advice(base[i], Rotation::cur());
                let _coeff = meta.query_fixed(coeff[i], Rotation::cur());
                acc = acc + _base * _coeff;
            }
            for i in 0..MUL_COLUMNS {
                let _base_l = meta.query_advice(base[i * 2], Rotation::cur());
                let _base_r = meta.query_advice(base[i * 2 + 1], Rotation::cur());
                let _mul_coeff = meta.query_fixed(mul_coeff[i], Rotation::cur());
                acc = acc + _base_l * _base_r * _mul_coeff;
            }

            vec![acc]
        });

        BaseChipConfig {
            base,
            coeff,
            mul_coeff,
            constant,
            next_coeff,
        }
    }

    pub fn one_line(
        &self,
        record: &mut Records<N>,
        offset: usize,
        base_coeff_pairs: Vec<(ValueSchema<N>, N)>,
        constant: Option<N>,
        mul_next_coeffs: (Vec<N>, Option<N>),
    ) {
        assert!(base_coeff_pairs.len() <= VAR_COLUMNS);

        if offset <= record.adv_record.len() {
            let adv_default = (None, false);
            let to_len = (offset + EXTEND_SIZE) & !(EXTEND_SIZE - 1);
            record.adv_record.resize(to_len, [adv_default; VAR_COLUMNS]);
            record.fix_record.resize(to_len, [None; FIXED_COLUMNS]);
        }

        for (i, (base, coeff)) in base_coeff_pairs.into_iter().enumerate() {
            match base.cell() {
                Some(cell) => {
                    record
                        .permutations
                        .push((cell, Cell::new(Chip::BaseChip, i, offset)));
                    record.adv_record[offset][i].1 = true;
                }
                _ => {}
            }
            record.fix_record[offset][i] = Some(coeff);
            record.adv_record[offset][i].0 = base.value();
        }

        let (mul_coeffs, next) = mul_next_coeffs;
        for (i, mul_coeff) in mul_coeffs.into_iter().enumerate() {
            record.fix_record[offset][VAR_COLUMNS + i] = Some(mul_coeff);
        }

        if next.is_some() {
            record.fix_record[offset][VAR_COLUMNS + MUL_COLUMNS] = next;
        }

        if constant.is_some() {
            record.fix_record[offset][VAR_COLUMNS + MUL_COLUMNS + 1] = constant;
        }
    }

    pub fn one_line_with_last(
        &self,
        record: &mut Records<N>,
        offset: usize,
        base_coeff_pairs: Vec<(ValueSchema<N>, N)>,
        tail: (ValueSchema<N>, N),
        constant: Option<N>,
        mul_next_coeffs: (Vec<N>, Option<N>),
    ) {
        assert!(base_coeff_pairs.len() <= VAR_COLUMNS - 1);

        self.one_line(record, offset, base_coeff_pairs, constant, mul_next_coeffs);

        let (base, coeff) = tail;

        let i = VAR_COLUMNS - 1;
        match base.cell() {
            Some(cell) => {
                record
                    .permutations
                    .push((cell, Cell::new(Chip::BaseChip, i, offset)));
                record.adv_record[offset][i].1 = true;
            }
            _ => {}
        }
        record.fix_record[offset][i] = Some(coeff);
        record.adv_record[offset][i].0 = base.value();
    }
}
