use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Fixed},
    poly::Rotation,
};
use std::marker::PhantomData;

pub const VAR_COLUMNS: usize = 5;
pub const MUL_COLUMNS: usize = 2;
pub const FIXED_COLUMNS: usize = VAR_COLUMNS + MUL_COLUMNS + 2;

#[derive(Clone, Debug)]
pub struct PlonkChipConfig {
    pub var: [Column<Advice>; VAR_COLUMNS],
    pub coeff: [Column<Fixed>; VAR_COLUMNS],
    pub mul_coeff: [Column<Fixed>; MUL_COLUMNS],
    pub next_coeff: Column<Fixed>,
    pub constant: Column<Fixed>,
}

#[derive(Clone, Debug)]
pub struct PlonkChip<N: FieldExt> {
    pub config: PlonkChipConfig,
    mark: PhantomData<N>,
}

impl<N: FieldExt> PlonkChip<N> {
    pub fn new(config: PlonkChipConfig) -> Self {
        Self {
            config,
            mark: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> PlonkChipConfig {
        let var = [(); VAR_COLUMNS].map(|_| meta.advice_column());
        let coeff = [(); VAR_COLUMNS].map(|_| meta.fixed_column());
        let mul_coeff = [(); MUL_COLUMNS].map(|_| meta.fixed_column());
        let next_coeff = meta.fixed_column();
        let constant = meta.fixed_column();

        var.iter().for_each(|c| meta.enable_equality(c.clone()));

        meta.create_gate("var_gate", |meta| {
            let _constant = meta.query_fixed(constant, Rotation::cur());
            let _next = meta.query_advice(var[VAR_COLUMNS - 1], Rotation::next());
            let _next_coeff = meta.query_fixed(next_coeff, Rotation::cur());

            let mut acc = _constant + _next * _next_coeff;
            for i in 0..VAR_COLUMNS {
                let _var = meta.query_advice(var[i], Rotation::cur());
                let _coeff = meta.query_fixed(coeff[i], Rotation::cur());
                acc = acc + _var * _coeff;
            }
            for i in 0..MUL_COLUMNS {
                let _var_l = meta.query_advice(var[i * 2], Rotation::cur());
                let _var_r = meta.query_advice(var[i * 2 + 1], Rotation::cur());
                let _mul_coeff = meta.query_fixed(mul_coeff[i], Rotation::cur());
                acc = acc + _var_l * _var_r * _mul_coeff;
            }

            vec![acc]
        });

        PlonkChipConfig {
            var,
            coeff,
            mul_coeff,
            constant,
            next_coeff,
        }
    }
}

