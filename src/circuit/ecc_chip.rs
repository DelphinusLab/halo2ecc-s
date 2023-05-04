use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::pairing::group::Curve;
use halo2_proofs::pairing::group::Group;
use num_bigint::BigUint;

use super::integer_chip::IntegerChipOps;
use super::select_chip::SelectChipOps;
use crate::assign::{AssignedCondition, AssignedCurvature, AssignedInteger, AssignedPoint};
use crate::assign::{AssignedPointWithCurvature, AssignedValue};
use crate::utils::{bn_to_field, field_to_bn};

pub const MSM_PREFIX_SIZE: usize = 1 << 20;

pub trait EccChipScalarOps<C: CurveAffine, N: FieldExt>: EccChipBaseOps<C, N> {
    type AssignedScalar: Clone;

    fn get_and_increase_msm_prefix(&mut self) -> usize;

    fn decompose_scalar<const WINDOW_SIZE: usize>(
        &mut self,
        s: &Self::AssignedScalar,
    ) -> Vec<[AssignedCondition<N>; WINDOW_SIZE]>;

    // like pippenger
    fn msm_batch_on_group(
        &mut self,
        points: &Vec<AssignedPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> AssignedPoint<C, N> {
        assert!(points.len() <= MSM_PREFIX_SIZE);

        let best_group_size = 5;
        let n_group = (points.len() + best_group_size - 1) / best_group_size;
        let group_size = (points.len() + n_group - 1) / n_group;

        let identity = self.assign_identity();

        let mut candidates = vec![];
        let group_prefix = self.get_and_increase_msm_prefix();
        let mut group_index = group_prefix;

        for chunk in points.chunks(group_size) {
            candidates.push(vec![identity.clone()]);
            self.assign_cache_point(&identity, group_index, 0 as usize);
            let cl = candidates.last_mut().unwrap();
            for i in 1..1u32 << chunk.len() {
                let pos = 32 - i.leading_zeros() - 1;
                let other = i - (1 << pos);
                let p = self.ecc_add(&cl[other as usize], &chunk[pos as usize]);
                let p = self.ecc_reduce_with_curvature(&p);
                self.assign_cache_point(&p, group_index, i as usize);
                cl.push(p);
            }
            group_index += 1;
        }

        let bits = scalars
            .into_iter()
            .map(|s| self.decompose_scalar::<1>(s))
            .collect::<Vec<Vec<[AssignedCondition<_>; 1]>>>();

        let groups = bits.chunks(group_size).collect::<Vec<_>>();

        let mut acc = None;

        for wi in 0..bits[0].len() {
            let mut inner_acc = None;
            for group_index in 0..groups.len() {
                let group_bits = groups[group_index].iter().map(|bits| bits[wi][0]).collect();
                let (index_cell, ci) = self.pick_candidate(&candidates[group_index], &group_bits);
                self.assign_selected_point(&ci, &index_cell, group_index + group_prefix);

                match inner_acc {
                    None => inner_acc = Some(ci.to_point()),
                    Some(_inner_acc) => {
                        let p = self.ecc_add(&ci, &_inner_acc);
                        inner_acc = Some(p);
                    }
                }
            }

            match acc {
                None => acc = inner_acc,
                Some(_acc) => {
                    let p = self.to_point_with_curvature(_acc);
                    let p = self.ecc_double(&p);
                    let p = self.to_point_with_curvature(p);
                    acc = Some(self.ecc_add(&p, &inner_acc.unwrap()));
                }
            }
        }

        acc.unwrap()
    }

    //like shamir
    fn msm_batch_on_window(
        &mut self,
        points: &Vec<AssignedPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> AssignedPoint<C, N> {
        const WINDOW_SIZE: usize = 4;
        assert!(points.len() == scalars.len());

        // TODO: can be parallel
        let windows_in_be = scalars
            .into_iter()
            .map(|s| self.decompose_scalar(s))
            .collect::<Vec<Vec<[AssignedCondition<_>; WINDOW_SIZE]>>>();

        let identity = self.assign_identity();

        // TODO: can be parallel
        let point_candidates: Vec<Vec<AssignedPointWithCurvature<_, _>>> = points
            .iter()
            .map(|a| {
                let mut candidates =
                    vec![identity.clone(), self.to_point_with_curvature(a.clone())];
                for i in 2..(1 << WINDOW_SIZE) {
                    let ai = self.ecc_add(&candidates[i - 1], a);
                    let ai = self.to_point_with_curvature(ai);
                    candidates.push(ai)
                }
                candidates
            })
            .collect::<Vec<_>>();

        let pick_candidate =
            |ops: &mut Self, pi: usize, bits_in_le: &[AssignedCondition<N>; WINDOW_SIZE]| {
                let mut curr_candidates: Vec<_> = point_candidates[pi].clone();
                for bit in bits_in_le {
                    let mut next_candidates = vec![];

                    for it in curr_candidates.chunks(2) {
                        let a0 = &it[0];
                        let a1 = &it[1];

                        let cell = ops.bisec_point_with_curvature(&bit, a1, a0);
                        next_candidates.push(cell);
                    }
                    curr_candidates = next_candidates;
                }
                assert_eq!(curr_candidates.len(), 1);
                curr_candidates[0].clone()
            };

        let mut acc = None;

        for wi in 0..windows_in_be[0].len() {
            let mut inner_acc = None;
            // TODO: can be parallel
            for pi in 0..points.len() {
                let ci = pick_candidate(self, pi, &windows_in_be[pi][wi]);
                match inner_acc {
                    None => inner_acc = Some(ci.to_point()),
                    Some(_inner_acc) => {
                        let p = self.ecc_add(&ci, &_inner_acc);
                        inner_acc = Some(p);
                    }
                }
            }

            match acc {
                None => acc = inner_acc,
                Some(mut _acc) => {
                    for _ in 0..WINDOW_SIZE {
                        let p = self.to_point_with_curvature(_acc);
                        _acc = self.ecc_double(&p);
                    }
                    let p = self.to_point_with_curvature(inner_acc.unwrap());
                    _acc = self.ecc_add(&p, &_acc);
                    acc = Some(_acc);
                }
            }
        }

        acc.unwrap()
    }

    fn msm(
        &mut self,
        points: &Vec<AssignedPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> AssignedPoint<C, N> {
        if points.len() >= 3 {
            self.msm_batch_on_group(points, scalars)
        } else {
            self.msm_batch_on_window(points, scalars)
        }
    }

    fn ecc_mul(&mut self, a: &AssignedPoint<C, N>, s: Self::AssignedScalar) -> AssignedPoint<C, N> {
        self.msm(&vec![a.clone()], &vec![s.clone()])
    }
}

pub trait EccBaseIntegerChipWrapper<W: BaseExt, N: FieldExt> {
    fn base_integer_chip(&mut self) -> &mut dyn IntegerChipOps<W, N>;
    fn select_chip(&mut self) -> &mut dyn SelectChipOps<W, N>;
}

pub trait EccChipBaseOps<C: CurveAffine, N: FieldExt>:
    EccBaseIntegerChipWrapper<C::Base, N>
{
    fn assign_constant_point(&mut self, c: &C::CurveExt) -> AssignedPoint<C, N> {
        let coordinates = c.to_affine().coordinates();
        let t: Option<_> = coordinates.map(|v| (v.x().clone(), v.y().clone())).into();
        let (x, y) = t.unwrap_or((C::Base::zero(), C::Base::zero()));
        let z = if c.is_identity().into() {
            N::one()
        } else {
            N::zero()
        };

        let x = self.base_integer_chip().assign_int_constant(x);
        let y = self.base_integer_chip().assign_int_constant(y);
        let z = self.base_integer_chip().base_chip().assign_constant(z);

        AssignedPoint::new(x, y, AssignedCondition(z))
    }

    fn assign_point(&mut self, c: &<C as CurveAffine>::CurveExt) -> AssignedPoint<C, N> {
        let coordinates = c.to_affine().coordinates();
        let t: Option<_> = coordinates.map(|v| (v.x().clone(), v.y().clone())).into();
        let (x, y) = t.unwrap_or((C::Base::zero(), C::Base::zero()));
        let z = if c.is_identity().into() {
            N::one()
        } else {
            N::zero()
        };

        let x = self.base_integer_chip().assign_w(&field_to_bn(&x));
        let y = self.base_integer_chip().assign_w(&field_to_bn(&y));
        let z = self.base_integer_chip().base_chip().assign_bit(z);

        // Constrain y^2 = x^3 + b
        // TODO: Optimize b
        let b = self.base_integer_chip().assign_int_constant(C::b());
        let y2 = self.base_integer_chip().int_square(&y);
        let x2 = self.base_integer_chip().int_square(&x);
        let x3 = self.base_integer_chip().int_mul(&x2, &x);
        let right = self.base_integer_chip().int_add(&x3, &b);

        let eq = self.base_integer_chip().is_int_equal(&y2, &right);
        let eq_or_identity = self.base_integer_chip().base_chip().or(&eq, &z);
        self.base_integer_chip()
            .base_chip()
            .assert_true(&eq_or_identity);

        AssignedPoint::new(x, y, z)
    }

    fn assign_identity(&mut self) -> AssignedPointWithCurvature<C, N> {
        let zero = self
            .base_integer_chip()
            .assign_int_constant(C::Base::zero());
        let one = self
            .base_integer_chip()
            .base_chip()
            .assign_constant(N::one());

        AssignedPointWithCurvature::new(
            zero.clone(),
            zero.clone(),
            AssignedCondition(one),
            AssignedCurvature(zero, AssignedCondition(one)),
        )
    }

    fn bisec_point(
        &mut self,
        cond: &AssignedCondition<N>,
        a: &AssignedPoint<C, N>,
        b: &AssignedPoint<C, N>,
    ) -> AssignedPoint<C, N> {
        let x = self.base_integer_chip().bisec_int(cond, &a.x, &b.x);
        let y = self.base_integer_chip().bisec_int(cond, &a.y, &b.y);
        let z = self
            .base_integer_chip()
            .base_chip()
            .bisec_cond(cond, &a.z, &b.z);

        AssignedPoint::new(x, y, z)
    }

    fn bisec_curvature(
        &mut self,
        cond: &AssignedCondition<N>,
        a: &AssignedCurvature<C, N>,
        b: &AssignedCurvature<C, N>,
    ) -> AssignedCurvature<C, N> {
        let v = self.base_integer_chip().bisec_int(cond, &a.0, &b.0);
        let z = self
            .base_integer_chip()
            .base_chip()
            .bisec_cond(cond, &a.1, &b.1);

        AssignedCurvature(v, z)
    }

    fn bisec_point_with_curvature(
        &mut self,
        cond: &AssignedCondition<N>,
        a: &AssignedPointWithCurvature<C, N>,
        b: &AssignedPointWithCurvature<C, N>,
    ) -> AssignedPointWithCurvature<C, N> {
        let x = self.base_integer_chip().bisec_int(cond, &a.x, &b.x);
        let y = self.base_integer_chip().bisec_int(cond, &a.y, &b.y);
        let z = self
            .base_integer_chip()
            .base_chip()
            .bisec_cond(cond, &a.z, &b.z);

        let c = self.bisec_curvature(cond, &a.curvature, &b.curvature);

        AssignedPointWithCurvature::new(x, y, z, c)
    }

    fn lambda_to_point(
        &mut self,
        lambda: &AssignedCurvature<C, N>,
        a: &AssignedPoint<C, N>,
        b: &AssignedPoint<C, N>,
    ) -> AssignedPoint<C, N> {
        let l = &lambda.0;

        // cx = lambda ^ 2 - a.x - b.x
        let cx = {
            let l_square = self.base_integer_chip().int_square(l);
            let t = self.base_integer_chip().int_sub(&l_square, &a.x);
            let t = self.base_integer_chip().int_sub(&t, &b.x);
            t
        };

        let cy = {
            let t = self.base_integer_chip().int_sub(&a.x, &cx);
            let t = self.base_integer_chip().int_mul(&t, l);
            let t = self.base_integer_chip().int_sub(&t, &a.y);
            t
        };

        AssignedPoint::new(cx, cy, lambda.1)
    }

    fn ecc_add(
        &mut self,
        a: &AssignedPointWithCurvature<C, N>,
        b: &AssignedPoint<C, N>,
    ) -> AssignedPoint<C, N> {
        let diff_x = self.base_integer_chip().int_sub(&a.x, &b.x);
        let diff_y = self.base_integer_chip().int_sub(&a.y, &b.y);
        let (x_eq, tangent) = self.base_integer_chip().int_div(&diff_y, &diff_x);

        let y_eq = self.base_integer_chip().is_int_zero(&diff_y);
        let eq = self.base_integer_chip().base_chip().and(&x_eq, &y_eq);

        let tangent = AssignedCurvature(tangent, x_eq);
        let mut lambda = self.bisec_curvature(&eq, &a.curvature, &tangent);

        let a_p = a.clone().to_point();

        let p = self.lambda_to_point(&mut lambda, &a_p, b);
        let p = self.bisec_point(&a.z, b, &p);
        let p = self.bisec_point(&b.z, &a_p, &p);

        p
    }

    fn ecc_double(&mut self, a: &AssignedPointWithCurvature<C, N>) -> AssignedPoint<C, N> {
        let a_p = a.clone().to_point();
        let mut p = self.lambda_to_point(&a.curvature, &a_p, &a_p);
        p.z = self
            .base_integer_chip()
            .base_chip()
            .bisec_cond(&a.z, &a.z, &p.z);

        p
    }

    fn ecc_assert_equal(&mut self, a: &AssignedPoint<C, N>, b: &AssignedPoint<C, N>) {
        let eq_x = self.base_integer_chip().is_int_equal(&a.x, &b.x);
        let eq_y = self.base_integer_chip().is_int_equal(&a.y, &b.y);
        let eq_z = self.base_integer_chip().base_chip().xnor(&a.z, &b.z);
        let eq_xy = self.base_integer_chip().base_chip().and(&eq_x, &eq_y);
        let eq_xyz = self.base_integer_chip().base_chip().and(&eq_xy, &eq_z);

        let is_both_identity = self.base_integer_chip().base_chip().and(&a.z, &b.z);
        let eq = self
            .base_integer_chip()
            .base_chip()
            .or(&eq_xyz, &is_both_identity);

        self.base_integer_chip().base_chip().assert_true(&eq)
    }

    fn ecc_neg(&mut self, a: &AssignedPoint<C, N>) -> AssignedPoint<C, N> {
        let x = a.x.clone();
        let y = self.base_integer_chip().int_neg(&a.y);
        let z = a.z.clone();

        AssignedPoint::new(x, y, z)
    }

    fn ecc_reduce(&mut self, a: &AssignedPoint<C, N>) -> AssignedPoint<C, N> {
        let x = self.base_integer_chip().reduce(&a.x);
        let y = self.base_integer_chip().reduce(&a.y);
        let z = a.z;

        let identity = self.assign_identity();
        self.bisec_point(&z, &identity.to_point(), &AssignedPoint::new(x, y, z))
    }

    fn ecc_reduce_with_curvature(
        &mut self,
        a: &AssignedPoint<C, N>,
    ) -> AssignedPointWithCurvature<C, N> {
        let a = self.ecc_reduce(a);

        // 3 * x ^ 2 / 2 * y
        let x_square = self.base_integer_chip().int_square(&a.x);
        let numerator = self
            .base_integer_chip()
            .int_mul_small_constant(&x_square, 3);
        let denominator = self.base_integer_chip().int_mul_small_constant(&a.y, 2);

        let (z, v) = self.base_integer_chip().int_div(&numerator, &denominator);
        let v = self.base_integer_chip().reduce(&v);
        AssignedPointWithCurvature::new(a.x, a.y, a.z, AssignedCurvature(v, z))
    }

    fn to_point_with_curvature(
        &mut self,
        a: AssignedPoint<C, N>,
    ) -> AssignedPointWithCurvature<C, N> {
        // 3 * x ^ 2 / 2 * y
        let x_square = self.base_integer_chip().int_square(&a.x);
        let numerator = self
            .base_integer_chip()
            .int_mul_small_constant(&x_square, 3);
        let denominator = self.base_integer_chip().int_mul_small_constant(&a.y, 2);

        let (z, v) = self.base_integer_chip().int_div(&numerator, &denominator);
        AssignedPointWithCurvature::new(a.x, a.y, a.z, AssignedCurvature(v, z))
    }

    fn ecc_encode(&mut self, p: &AssignedPoint<C, N>) -> Vec<AssignedValue<N>> {
        let p = self.ecc_reduce(&p);
        let shift = bn_to_field(
            &(BigUint::from(1u64) << self.base_integer_chip().range_chip().info().limb_bits),
        );
        let s0 = self.base_integer_chip().base_chip().sum_with_constant(
            vec![(&p.x.limbs_le[0], N::one()), (&p.x.limbs_le[1], shift)],
            None,
        );
        let s1 = self.base_integer_chip().base_chip().sum_with_constant(
            vec![(&p.x.limbs_le[2], N::one()), (&p.y.limbs_le[0], shift)],
            None,
        );
        let s2 = self.base_integer_chip().base_chip().sum_with_constant(
            vec![(&p.y.limbs_le[1], N::one()), (&p.y.limbs_le[2], shift)],
            None,
        );
        vec![s0, s1, s2]
    }

    fn assign_cache_integer(
        &mut self,
        p: &AssignedInteger<C::Base, N>,
        sc: usize,
        g: usize,
        offset: &mut usize,
    ) {
        let limb_size = self.base_integer_chip().range_chip().info().limbs;
        for j in 0..limb_size as usize {
            self.select_chip()
                .assign_cache_value(&p.limbs_le[j], *offset, g, sc);
            *offset += 1;
        }
        self.select_chip()
            .assign_cache_value(&p.native, *offset, g, sc);
        *offset += 1;
    }

    fn assign_selected_integer(
        &mut self,
        p: &AssignedInteger<C::Base, N>,
        sc: &AssignedValue<N>,
        g: usize,
        offset: &mut usize,
    ) {
        let limb_size = self.base_integer_chip().range_chip().info().limbs;
        for j in 0..limb_size as usize {
            self.select_chip()
                .assign_selected_value(&p.limbs_le[j], *offset, g, sc);
            *offset += 1;
        }
        self.select_chip()
            .assign_selected_value(&p.native, *offset, g, sc);
        *offset += 1;
    }

    fn assign_cache_point(&mut self, p: &AssignedPointWithCurvature<C, N>, g: usize, sc: usize) {
        let mut i = 0;
        self.assign_cache_integer(&p.x, sc, g, &mut i);
        self.assign_cache_integer(&p.y, sc, g, &mut i);
        self.select_chip().assign_cache_value(&p.z.0, i, g, sc);
        i += 1;
        self.assign_cache_integer(&p.curvature.0, sc, g, &mut i);
        self.select_chip()
            .assign_cache_value(&p.curvature.1 .0, i, g, sc);
    }

    fn assign_selected_point(
        &mut self,
        p: &AssignedPointWithCurvature<C, N>,
        sc: &AssignedValue<N>,
        g: usize,
    ) {
        let mut i = 0;
        self.assign_selected_integer(&p.x, sc, g, &mut i);
        self.assign_selected_integer(&p.y, sc, g, &mut i);
        self.select_chip().assign_selected_value(&p.z.0, i, g, sc);
        i += 1;
        self.assign_selected_integer(&p.curvature.0, sc, g, &mut i);
        self.select_chip()
            .assign_selected_value(&p.curvature.1 .0, i, g, sc);
    }

    fn pick_candidate(
        &mut self,
        candidates: &Vec<AssignedPointWithCurvature<C, N>>,
        group_bits: &Vec<AssignedCondition<N>>,
    ) -> (AssignedValue<N>, AssignedPointWithCurvature<C, N>) {
        let curr_candidates: Vec<_> = candidates.clone();
        let mut group_bits = group_bits.clone();
        group_bits.reverse();
        let index = group_bits
            .iter()
            .fold((0, 0), |(i, s), x| {
                if x.0.val == N::zero() {
                    (i * 2, s + 1)
                } else {
                    (i * 2 + 1, s + 1)
                }
            })
            .0;
        let integer_chip = self.base_integer_chip();
        let mut base_chip = integer_chip.base_chip();
        let value_cell = base_chip.assign_constant(N::zero());
        let one_cell = base_chip.assign_constant(N::one());
        let index_cell = group_bits.iter().fold(value_cell, |acc, x| {
            base_chip.mul_add(&x.0, &one_cell, N::one(), &acc, N::from(2u64))
        });
        //println!("index is: {:?}, cell is: {:?}", index, index_cell.val);
        let ci = &curr_candidates[index];
        (index_cell, ci.clone())
    }
}
