use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::pairing::group::ff::PrimeField;
use halo2_proofs::pairing::group::Curve;
use num_integer::Integer;

use super::base_chip::BaseChipOps;
use super::integer_chip::IntegerChipOps;
use crate::assign::{AssignedCondition, AssignedCurvature, AssignedPoint};
use crate::assign::{AssignedPointWithCurvature, AssignedValue};
use crate::context::{Context, EccContext};
use crate::pair;
use crate::utils::{bn_to_field, field_to_bn};

const WINDOW_SIZE: usize = 4usize;

pub trait EccChipOps<C: CurveAffine> {
    type AssignedScalar;
    fn assign_constant_point(&mut self, c: &C::CurveExt) -> AssignedPoint<C, C::ScalarExt>;
    fn assign_point(&mut self, c: &C::CurveExt) -> AssignedPoint<C, C::ScalarExt>;
    fn assign_identity(&mut self) -> AssignedPointWithCurvature<C, C::ScalarExt>;
    fn assign_constant_point_from_scalar(
        &mut self,
        scalar: &C::ScalarExt,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let p: C::CurveExt = C::generator() * scalar;
        self.assign_constant_point(&p)
    }
    fn assign_point_from_scalar(
        &mut self,
        scalar: &C::ScalarExt,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let p: C::CurveExt = C::generator() * scalar;
        self.assign_point(&p)
    }

    fn ecc_mul(
        &mut self,
        a: &AssignedPoint<C, C::ScalarExt>,
        s: &Self::AssignedScalar,
    ) -> AssignedPoint<C, C::ScalarExt>;
    fn msm(
        &mut self,
        points: &Vec<AssignedPoint<C, C::ScalarExt>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> AssignedPoint<C, C::ScalarExt>;
    fn bisec_point(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &AssignedPoint<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt>;
    fn bisec_curvature(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &AssignedCurvature<C, C::ScalarExt>,
        b: &AssignedCurvature<C, C::ScalarExt>,
    ) -> AssignedCurvature<C, C::ScalarExt>;
    fn to_point_with_curvature(
        &mut self,
        a: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPointWithCurvature<C, C::ScalarExt>;
    fn bisec_point_with_curvature(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
        b: &AssignedPointWithCurvature<C, C::ScalarExt>,
    ) -> AssignedPointWithCurvature<C, C::ScalarExt>;
    fn ecc_add(
        &mut self,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt>;
    fn ecc_double(
        &mut self,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt>;
    fn ecc_assert_equal(
        &mut self,
        a: &AssignedPoint<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    );
    fn ecc_neg(&mut self, a: &AssignedPoint<C, C::ScalarExt>) -> AssignedPoint<C, C::ScalarExt>;
    fn ecc_sub(
        &mut self,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let neg_b = self.ecc_neg(b);
        self.ecc_add(a, &neg_b)
    }
    fn ecc_reduce(&mut self, a: &AssignedPoint<C, C::ScalarExt>) -> AssignedPoint<C, C::ScalarExt>;
    fn lambda_to_point(
        &mut self,
        lambda: &AssignedCurvature<C, C::ScalarExt>,
        a: &AssignedPoint<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt>;
    fn decompose_scalar(
        &mut self,
        s: &AssignedValue<C::ScalarExt>,
    ) -> Vec<[AssignedCondition<C::ScalarExt>; WINDOW_SIZE]>;
}

impl<C: CurveAffine> EccChipOps<C> for EccContext<C> {
    type AssignedScalar = AssignedValue<C::ScalarExt>;

    fn assign_constant_point(&mut self, c: &C::CurveExt) -> AssignedPoint<C, C::ScalarExt> {
        let coordinates = c.to_affine().coordinates();
        let t: Option<_> = coordinates
            .map(|v| (v.x().clone(), v.y().clone(), C::ScalarExt::zero()))
            .into();
        let (x, y, z) = t.unwrap_or((C::Base::zero(), C::Base::zero(), C::ScalarExt::one()));

        let x = self.assign_int_constant(x);
        let y = self.assign_int_constant(y);
        let z = self.assign_constant(z);

        AssignedPoint::new(x, y, AssignedCondition(z))
    }

    fn assign_point(&mut self, c: &<C as CurveAffine>::CurveExt) -> AssignedPoint<C, C::ScalarExt> {
        let coordinates = c.to_affine().coordinates();
        let t: Option<_> = coordinates
            .map(|v| (v.x().clone(), v.y().clone(), C::ScalarExt::zero()))
            .into();
        let (_x, _y, z) = t.unwrap_or((C::Base::zero(), C::Base::zero(), C::ScalarExt::one()));

        let x = self.assign_w(&field_to_bn(&_x));
        let y = self.assign_w(&field_to_bn(&_y));
        let z = self.assign_bit(z);

        // Constrain y^2 = x^3 + b
        // TODO: Optimize b
        let b = self.assign_int_constant(C::b());
        let y2 = self.int_square(&y);
        let x2 = self.int_square(&x);
        let x3 = self.int_mul(&x2, &x);
        let right = self.int_add(&x3, &b);

        let eq = self.is_int_equal(&y2, &right);
        let eq_or_identity = self.or(&eq, &z);
        self.assert_true(&eq_or_identity);

        AssignedPoint::new(x, y, z)
    }

    fn assign_identity(&mut self) -> AssignedPointWithCurvature<C, C::ScalarExt> {
        let zero = self.assign_int_constant(C::Base::zero());
        let one = self.assign_constant(C::ScalarExt::one());

        AssignedPointWithCurvature::new(
            zero.clone(),
            zero.clone(),
            AssignedCondition(one),
            AssignedCurvature(zero, AssignedCondition(one)),
        )
    }

    fn ecc_mul(
        &mut self,
        a: &AssignedPoint<C, C::ScalarExt>,
        s: &Self::AssignedScalar,
    ) -> AssignedPoint<C, C::ScalarExt> {
        self.msm(&vec![a.clone()], &vec![s.clone()])
    }

    fn bisec_point(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &AssignedPoint<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let x = self.bisec_int(cond, &a.x, &b.x);
        let y = self.bisec_int(cond, &a.y, &b.y);
        let z = self.bisec_cond(cond, &a.z, &b.z);

        AssignedPoint::new(x, y, z)
    }

    fn bisec_curvature(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &AssignedCurvature<C, C::ScalarExt>,
        b: &AssignedCurvature<C, C::ScalarExt>,
    ) -> AssignedCurvature<C, C::ScalarExt> {
        let v = self.bisec_int(cond, &a.0, &b.0);
        let z = self.bisec_cond(cond, &a.1, &b.1);

        AssignedCurvature(v, z)
    }

    fn bisec_point_with_curvature(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
        b: &AssignedPointWithCurvature<C, C::ScalarExt>,
    ) -> AssignedPointWithCurvature<C, C::ScalarExt> {
        let x = self.bisec_int(cond, &a.x, &b.x);
        let y = self.bisec_int(cond, &a.y, &b.y);
        let z = self.bisec_cond(cond, &a.z, &b.z);

        let c = self.bisec_curvature(cond, &a.curvature, &b.curvature);

        AssignedPointWithCurvature::new(x, y, z, c)
    }

    fn lambda_to_point(
        &mut self,
        lambda: &AssignedCurvature<C, C::ScalarExt>,
        a: &AssignedPoint<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let l = &lambda.0;

        // cx = lambda ^ 2 - a.x - b.x
        let cx = {
            let l_square = self.int_square(l);
            let t = self.int_sub(&l_square, &a.x);
            let t = self.int_sub(&t, &b.x);
            t
        };

        let cy = {
            let t = self.int_sub(&a.x, &cx);
            let t = self.int_mul(&t, l);
            let t = self.int_sub(&t, &a.y);
            t
        };

        AssignedPoint::new(cx, cy, lambda.1)
    }

    fn ecc_add(
        &mut self,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let diff_x = self.int_sub(&a.x, &b.x);
        let diff_y = self.int_sub(&a.y, &b.y);
        let (x_eq, tangent) = self.int_div(&diff_y, &diff_x);

        let y_eq = self.is_int_zero(&diff_y);
        let eq = self.and(&x_eq, &y_eq);

        let tangent = AssignedCurvature(tangent, x_eq);
        let mut lambda = self.bisec_curvature(&eq, &a.curvature, &tangent);

        let p = self.lambda_to_point(&mut lambda, &a.to_point(), b);
        let p = self.bisec_point(&a.z, b, &p);
        let p = self.bisec_point(&b.z, &a.to_point(), &p);

        p
    }

    fn ecc_double(
        &mut self,
        a: &AssignedPointWithCurvature<C, C::ScalarExt>,
    ) -> AssignedPoint<C, C::ScalarExt> {
        let a_p = a.to_point();
        let mut p = self.lambda_to_point(&a.curvature, &a_p, &a_p);
        p.z = self.bisec_cond(&a.z, &a.z, &p.z);

        p
    }

    fn ecc_assert_equal(
        &mut self,
        a: &AssignedPoint<C, C::ScalarExt>,
        b: &AssignedPoint<C, C::ScalarExt>,
    ) {
        let eq_x = self.is_int_equal(&a.x, &b.x);
        let eq_y = self.is_int_equal(&a.y, &b.y);
        let eq_z = self.xnor(&a.z, &b.z);
        let eq_xy = self.and(&eq_x, &eq_y);
        let eq_xyz = self.and(&eq_xy, &eq_z);

        let is_both_identity = self.and(&a.z, &b.z);
        let eq = self.or(&eq_xyz, &is_both_identity);

        self.assert_true(&eq)
    }

    fn ecc_neg(&mut self, a: &AssignedPoint<C, C::ScalarExt>) -> AssignedPoint<C, C::ScalarExt> {
        let x = a.x.clone();
        let y = self.int_neg(&a.y);
        let z = a.z.clone();

        AssignedPoint::new(x, y, z)
    }

    fn ecc_reduce(&mut self, a: &AssignedPoint<C, C::ScalarExt>) -> AssignedPoint<C, C::ScalarExt> {
        let x = self.reduce(&a.x);
        let y = self.reduce(&a.y);
        let z = a.z;

        let identity = self.assign_identity();
        self.bisec_point(&z, &identity.to_point(), &AssignedPoint::new(x, y, z))
    }

    fn decompose_scalar(
        &mut self,
        s: &AssignedValue<C::ScalarExt>,
    ) -> Vec<[AssignedCondition<C::ScalarExt>; WINDOW_SIZE]> {
        let one = C::ScalarExt::one();
        let two = one + &one;
        let four = two + &two;

        let mut bits = vec![];

        let s_bn = field_to_bn(&s.val);
        let mut v = s.clone();
        for i in 0..<C::ScalarExt as PrimeField>::NUM_BITS as u64 / 2 {
            let b0 = if s_bn.bit(i * 2) {
                C::ScalarExt::one()
            } else {
                C::ScalarExt::zero()
            };
            let b1 = if s_bn.bit(i * 2 + 1) {
                C::ScalarExt::one()
            } else {
                C::ScalarExt::zero()
            };
            let b0 = self.assign_bit(b0);
            let b1 = self.assign_bit(b1);
            let v_next: C::ScalarExt = bn_to_field(&(&s_bn >> (i * 2 + 2)));

            let cells = self.one_line_with_last(
                vec![
                    pair!(v_next.clone(), four),
                    pair!(&b1.0, two),
                    pair!(&b0.0, one),
                ],
                pair!(&v, -one),
                None,
                (vec![], None),
            );

            v = cells.0[0];

            bits.push(b0);
            bits.push(b1);
        }

        if <C::ScalarExt as PrimeField>::NUM_BITS.is_odd() {
            self.assert_bit(&v);
            bits.push(AssignedCondition(v));
        } else {
            self.assert_constant(&v, C::ScalarExt::zero())
        }

        let rem = <C::ScalarExt as PrimeField>::NUM_BITS as usize % 4;
        if rem > 0 {
            let zero = self.assign_constant(C::ScalarExt::zero());
            for _ in 0..WINDOW_SIZE - rem {
                bits.push(AssignedCondition(zero));
            }
        }

        let mut res: Vec<_> = bits
            .chunks(WINDOW_SIZE)
            .into_iter()
            .map(|x| x.try_into().unwrap())
            .collect();
        res.reverse();
        res
    }

    fn msm(
        &mut self,
        points: &Vec<AssignedPoint<C, C::ScalarExt>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> AssignedPoint<C, C::ScalarExt> {
        assert!(WINDOW_SIZE >= 1usize);
        assert!(points.len() == scalars.len());

        // TODO: can be parallel
        let windows_in_be = scalars
            .into_iter()
            .map(|s| EccChipOps::<C>::decompose_scalar(self, s))
            .collect::<Vec<Vec<[AssignedCondition<C::ScalarExt>; WINDOW_SIZE]>>>();

        let identity = self.assign_identity();

        // TODO: can be parallel
        let point_candidates: Vec<Vec<AssignedPointWithCurvature<_, _>>> = points
            .iter()
            .map(|a| {
                let mut candidates = vec![identity.clone(), self.to_point_with_curvature(a)];
                for i in 2..(1 << WINDOW_SIZE) {
                    let ai = self.ecc_add(&candidates[i - 1], a);
                    let ai = self.to_point_with_curvature(&ai);
                    candidates.push(ai)
                }
                candidates
            })
            .collect::<Vec<_>>();

        let pick_candidate =
            |ops: &mut Context<_, _>,
             pi: usize,
             bits_in_le: &[AssignedCondition<C::ScalarExt>; WINDOW_SIZE]| {
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
                        let p = self.to_point_with_curvature(&_acc);
                        _acc = self.ecc_double(&p);
                    }
                    let p = self.to_point_with_curvature(&inner_acc.unwrap());
                    _acc = self.ecc_add(&p, &_acc);
                    acc = Some(_acc);
                }
            }
        }

        acc.unwrap()
    }

    fn to_point_with_curvature(
        &mut self,
        a: &AssignedPoint<C, C::ScalarExt>,
    ) -> AssignedPointWithCurvature<C, C::ScalarExt> {
        // 3 * x ^ 2 / 2 * y
        let x_square = self.int_square(&a.x);
        let numerator = self.int_mul_small_constant(&x_square, 3usize);
        let denominator = self.int_mul_small_constant(&a.y, 2usize);

        let (z, v) = self.int_div(&numerator, &denominator);
        AssignedPointWithCurvature::new(a.x, a.y, a.z, AssignedCurvature(v, z))
    }
}
