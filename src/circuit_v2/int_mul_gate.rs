use halo2_proofs::plonk::{Expression, VirtualCells};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Fixed},
    poly::Rotation,
};
use std::marker::PhantomData;
use crate::range_info::RangeInfo;

use super::plonk_gate::VAR_COLUMNS;

#[derive(Clone, Debug)]
pub struct IntMulConfig {
    pub vars: [Column<Advice>; VAR_COLUMNS],
    pub sel: Column<Fixed>,
    pub block_rows: usize,

    pub a: Vec<(usize, i32)>,
    pub b: Vec<(usize, i32)>,
    pub d: Vec<(usize, i32)>,
    pub rem: Vec<(usize, i32)>,
    pub v_list: Vec<((usize, i32), (usize, i32))>,
}

#[derive(Clone, Debug)]
pub struct IntMulChip<W: FieldExt, N: FieldExt> {
    pub config: IntMulConfig,
    mark: PhantomData<(W, N)>,
}

impl<W: FieldExt, N: FieldExt> IntMulChip<W, N> {
    pub fn new(config: IntMulConfig) -> Self {
        Self {
            config,
            mark: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<N>,
        vars: [Column<Advice>; VAR_COLUMNS],
        info: &RangeInfo<W, N>,
    ) -> IntMulConfig {
        let sel = meta.fixed_column();

        // constraints_for_mul_equation_on_limbs in gates mod
        /*
         * inputs: a limbs, b limbs, d, rem limbs
         * l0 = a0 * b0 - d0 * w0
         * l1 = a1 * b0 + a0 * b1 - d1 * w0 - d0 * w1
         * ...
         */

        let mut col_rot = 0;
        let mut row_rot = 0;
        let mut alloc = || {
            let col = col_rot;
            let row = row_rot;
            col_rot += 1;
            if col_rot == VAR_COLUMNS {
                col_rot = 0;
                row_rot += 1;
            }
            (col, row)
        };

        let a = (0..info.limbs)
            .into_iter()
            .map(|_| alloc())
            .collect::<Vec<_>>();

        let b = (0..info.limbs)
            .into_iter()
            .map(|_| alloc())
            .collect::<Vec<_>>();

        let d = (0..info.limbs)
            .into_iter()
            .map(|_| alloc())
            .collect::<Vec<_>>();

        let rem = (0..info.limbs)
            .into_iter()
            .map(|_| alloc())
            .collect::<Vec<_>>();

        let mut v_list: Vec<_> = (0..info.limbs).map(|_| (alloc(), alloc())).collect();

        let to_cell =
            |meta: &mut VirtualCells<N>, (col, row)| meta.query_advice(vars[col], Rotation(row));

        let to_constant = |n| Expression::Constant(n);

        meta.create_gate("int_mul_gate", |meta| {
            let mut constraints = vec![];

            let mut limbs_sum = vec![];
            for pos in 0..info.mul_check_limbs as usize {
                let r_bound = usize::min(pos + 1, info.limbs as usize);
                let l_bound = pos.checked_sub(info.limbs as usize - 1).unwrap_or(0);
                //println!("pos {}, l_bound {}, r_bound {}, info.limbs {}", pos, l_bound, r_bound, info.limbs);
                let sum = (l_bound..r_bound)
                    .map(|i| {
                        to_cell(meta, a[i]) * to_cell(meta, b[pos - i])
                            - to_cell(meta, d[i]) * to_constant(info.w_modulus_limbs_le[pos - i])
                    })
                    .reduce(|acc, x| acc + x)
                    .unwrap();

                limbs_sum.push(sum);
            }

            let v_h = v_list[0].0;
            let v_l = v_list[0].1;
            let borrow = N::from(info.limbs) * info.limb_modulus_n + N::from(2u64);
            {
                let u = limbs_sum[0].clone() - to_cell(meta, rem[0])
                    + to_constant(borrow * info.limb_modulus_n);

                // prove (limbs[0] + borrow - rem[0]) % limbs_size == 0
                constraints.push(
                    to_cell(meta, v_h) * to_constant(info.limb_coeffs[2])
                        + to_cell(meta, v_l) * to_constant(info.limb_coeffs[1])
                        - u,
                );
            }

            let borrow = borrow * info.limb_modulus_n - borrow;
            for i in 1..info.limbs as usize {
                let u = limbs_sum[i].clone() - to_cell(meta, rem[i])
                    + to_cell(meta, v_h) * to_constant(info.limb_coeffs[1])
                    + to_cell(meta, v_l) * to_constant(info.limb_coeffs[0])
                    + to_constant(borrow);
                let v_h = v_list[i].0;
                let v_l = v_list[i].1;

                // prove (limbs[0] + borrow - rem[0]) % limbs_size == 0
                constraints.push(
                    to_cell(meta, v_h) * to_constant(info.limb_coeffs[2])
                        + to_cell(meta, v_l) * to_constant(info.limb_coeffs[1])
                        - u,
                );
            }

            // Only support BN254 currently
            assert!(info.limbs == info.mul_check_limbs);

            constraints
                .into_iter()
                .map(|x| x * meta.query_fixed(sel, Rotation::cur()))
                .collect::<Vec<_>>()
        });

        IntMulConfig {
            vars,
            sel,
            block_rows: todo!(),
            a,
            b,
            d,
            rem,
            v_list,
        }
    }
}
