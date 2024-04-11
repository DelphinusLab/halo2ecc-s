use std::ops::Sub;

use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::pairing::group::Curve;
use halo2_proofs::pairing::group::Group;
use num_bigint::BigUint;
use num_integer::Integer;
use rayon::iter::*;

use super::integer_chip::IntegerChipOps;
use super::select_chip::SelectChipOps;
use crate::assign::AssignedNonZeroPoint;
use crate::assign::{AssignedCondition, AssignedCurvature, AssignedInteger, AssignedPoint};
use crate::assign::{AssignedPointWithCurvature, AssignedValue};
use crate::utils::{bn_to_field, field_to_bn};

pub const MSM_PREFIX_OFFSET: usize = 1 << 20;
pub const MSM_LIMIT: usize = (1 << 8) * MSM_PREFIX_OFFSET;

#[derive(Debug)]
pub enum UnsafeError {
    AddSameOrNegPoint,
    AddIdentity,
    AssignIdentity,
}

impl UnsafeError {
    pub fn can_retry(&self) -> bool {
        true
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct Offset {
    pub range_offset_diff: usize,
    pub base_offset_diff: usize,
    pub select_offset_diff: usize,
}

impl Sub<Offset> for Offset {
    type Output = Offset;

    fn sub(mut self, rhs: Offset) -> Self::Output {
        self.base_offset_diff -= rhs.base_offset_diff;
        self.range_offset_diff -= rhs.range_offset_diff;
        self.select_offset_diff -= rhs.select_offset_diff;
        return self;
    }
}

impl Offset {
    fn scale(&self, n: usize) -> Offset {
        Offset {
            range_offset_diff: self.range_offset_diff * n,
            base_offset_diff: self.base_offset_diff * n,
            select_offset_diff: self.select_offset_diff * n,
        }
    }
}

pub trait ParallelClone: Sized {
    fn clone_with_offset(&self, offset_diff: &Offset) -> Self;
    fn clone(&self) -> Self {
        self.clone_with_offset(&Offset {
            range_offset_diff: 0,
            base_offset_diff: 0,
            select_offset_diff: 0,
        })
    }
    fn offset(&self) -> Offset;
    fn merge(&self, other: Self);
}

pub trait EccChipScalarOps<C: CurveAffine, N: FieldExt>:
    EccChipBaseOps<C, N> + ParallelClone + Send + Sized
{
    type AssignedScalar: Clone;

    fn get_and_increase_msm_prefix(&mut self) -> usize;

    fn decompose_scalar<const WINDOW_SIZE: usize>(
        &mut self,
        s: &Self::AssignedScalar,
    ) -> Vec<[AssignedCondition<N>; WINDOW_SIZE]>;

    fn msm_batch_on_group_non_zero_without_select_chip(
        &mut self,
        points: &Vec<AssignedNonZeroPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
        rand_acc_point: C::Curve,
        rand_line_point: C::Curve,
    ) -> Result<AssignedPoint<C, N>, UnsafeError> {
        let rand_acc_point = self.assign_non_zero_point(&rand_acc_point);
        let rand_line_point = self.assign_non_zero_point(&rand_line_point);

        let rand_acc_point_neg = self.ecc_neg_non_zero(&rand_acc_point);
        let rand_line_point_neg = self.ecc_neg_non_zero(&rand_line_point);

        let best_group_size = 2;
        let n_group = (points.len() + best_group_size - 1) / best_group_size;
        let group_size = (points.len() + n_group - 1) / n_group;

        let mut candidates = vec![];

        for (group_index, chunk) in points.chunks(group_size).enumerate() {
            let init = if group_index.is_even() {
                &rand_line_point
            } else {
                &rand_line_point_neg
            };

            candidates.push(vec![init.clone()]);

            let cl = candidates.last_mut().unwrap();
            for i in 1..1u32 << chunk.len() {
                let pos = i.reverse_bits().leading_zeros(); // find the last bit-1 position
                let other = i - (1 << pos);
                let p = self.ecc_add_unsafe(&cl[other as usize], &chunk[pos as usize])?;
                cl.push(p);
            }
        }

        let bits = scalars
            .into_iter()
            .map(|s| self.decompose_scalar::<1>(s))
            .collect::<Vec<Vec<[AssignedCondition<_>; 1]>>>();

        let groups = bits.chunks(group_size).collect::<Vec<_>>();

        let mut acc = rand_acc_point.clone();

        let line_acc_arr = (0..bits[0].len())
            .map(|wi| -> Result<_, _> {
                let mut line_acc = rand_acc_point_neg.clone();
                for group_index in 0..groups.len() {
                    let group_bits = groups[group_index].iter().map(|bits| bits[wi][0]).collect();
                    let ci = self.bisec_candidate_non_zero(&candidates[group_index], &group_bits);

                    line_acc = self.ecc_add_unsafe(&ci, &line_acc)?;
                }
                Ok(line_acc)
            })
            .collect::<Result<Vec<_>, _>>()?;

        for wi in 0..bits[0].len() {
            acc = self.ecc_double_unsafe(&acc)?;
            acc = self.ecc_add_unsafe(&line_acc_arr[wi], &acc)?;
            if groups.len().is_odd() {
                acc = self.ecc_add_unsafe(&acc, &rand_line_point_neg)?;
            }
        }

        let acc = self.ecc_non_zero_point_downgrade(&acc);
        let acc = self.to_point_with_curvature(acc);
        let rand_acc_point_neg = self.ecc_non_zero_point_downgrade(&rand_acc_point_neg);

        Ok(self.ecc_add(&acc, &rand_acc_point_neg))
    }

    fn msm_batch_on_group_non_zero_with_select_chip(
        &mut self,
        points: &Vec<AssignedNonZeroPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
        rand_acc_point: C::Curve,
        rand_line_point: C::Curve,
    ) -> Result<AssignedPoint<C, N>, UnsafeError> {
        assert!(points.len() <= MSM_PREFIX_OFFSET);

        // Reduce points for parallel setup optimization.
        let _points = points
            .iter()
            .map(|p| self.ecc_reduce_non_zero(p))
            .collect::<Vec<_>>();
        let points = _points.iter().map(|p| p).collect::<Vec<_>>();

        let rand_acc_point = self.assign_non_zero_point(&rand_acc_point);
        let rand_line_point = self.assign_non_zero_point(&rand_line_point);

        let rand_acc_point_neg = self.ecc_neg_non_zero(&rand_acc_point);
        let rand_acc_point_neg = self.ecc_reduce_non_zero(&rand_acc_point_neg);
        let rand_line_point_neg = self.ecc_neg_non_zero(&rand_line_point);
        let rand_line_point_neg = self.ecc_reduce_non_zero(&rand_line_point_neg);

        let best_group_size = 5;
        let n_group = (points.len() + best_group_size - 1) / best_group_size;
        let group_size = (points.len() + n_group - 1) / n_group;

        // Prepare candidation points for each group.
        let mut candidates = vec![];
        let group_prefix = self.get_and_increase_msm_prefix();

        for (group_index, chunk) in points.chunks(group_size).enumerate() {
            let init = if group_index.is_even() {
                &rand_line_point
            } else {
                &rand_line_point_neg
            };

            candidates.push(vec![init.clone()]);
            self.assign_cache_point_non_zero(&init, group_prefix + group_index, 0 as usize);

            let cl = candidates.last_mut().unwrap();
            for i in 1..1u32 << chunk.len() {
                let pos = i.reverse_bits().leading_zeros(); // find the last bit-1 position
                let other = i - (1 << pos);
                let p = self.ecc_add_unsafe(&cl[other as usize], &chunk[pos as usize])?;
                let p = self.ecc_reduce_non_zero(&p);
                self.assign_cache_point_non_zero(&p, group_prefix + group_index, i as usize);
                cl.push(p);
            }
        }

        // Decompose to get bits of each (window, group).
        let bits = scalars
            .into_iter()
            .map(|s| self.decompose_scalar::<1>(s))
            .collect::<Vec<Vec<[AssignedCondition<_>; 1]>>>();

        let groups = bits.chunks(group_size).collect::<Vec<_>>();

        // Accumulate points of all groups in each window.
        let windows = bits[0].len();

        // For parallel setup, we first calculate the offset change on each window.
        // The diff should be same because all point are normalized.
        let offset_diff = {
            let mut predict_ops = self.clone();
            let offset_before = predict_ops.offset();
            let mut acc = rand_acc_point_neg.clone();
            for group_index in 0..groups.len() {
                let group_bits = groups[group_index].iter().map(|bits| bits[0][0]).collect();
                let (index_cell, ci) =
                    predict_ops.pick_candidate_non_zero(&candidates[group_index], &group_bits);
                let ci = predict_ops.assign_selected_point_non_zero(
                    &ci,
                    &index_cell,
                    group_index + group_prefix,
                );

                acc = predict_ops.ecc_add_unsafe(&ci, &acc)?;
            }
            let offset_after = predict_ops.offset();
            offset_after - offset_before
        };

        // prepare for parallel
        let mut cloned_ops = (0..windows)
            .into_iter()
            .map(|i| self.clone_with_offset(&offset_diff.scale(i)))
            .collect::<Vec<_>>();

        let line_acc_arr = cloned_ops
            .par_iter_mut()
            .enumerate()
            .map(|(wi, op)| {
                let offset_before = op.offset();
                let mut acc = rand_acc_point_neg.clone();
                for group_index in 0..groups.len() {
                    let group_bits = groups[group_index].iter().map(|bits| bits[wi][0]).collect();
                    let (index_cell, ci) =
                        op.pick_candidate_non_zero(&candidates[group_index], &group_bits);
                    let ci = op.assign_selected_point_non_zero(
                        &ci,
                        &index_cell,
                        group_index + group_prefix,
                    );

                    acc = op.ecc_add_unsafe(&ci, &acc)?;
                }
                let offset_after = op.offset();
                let _offset_diff = offset_after - offset_before;
                assert_eq!(offset_diff, _offset_diff);

                Ok(acc)
            })
            .collect::<Result<Vec<_>, _>>()?;

        // set self offset to the last
        *self = self.clone_with_offset(&offset_diff.scale(windows));

        for op in cloned_ops {
            self.merge(op);
        }

        // Accumulate points of all windows.
        let mut acc = rand_acc_point.clone();
        for wi in 0..windows {
            acc = self.ecc_double_unsafe(&acc)?;
            acc = self.ecc_add_unsafe(&line_acc_arr[wi], &acc)?;

            if groups.len().is_odd() {
                acc = self.ecc_add_unsafe(&acc, &rand_line_point_neg)?;
            }
        }

        // downgrade before add in case that result is identity
        let acc = self.ecc_non_zero_point_downgrade(&acc);
        let acc = self.to_point_with_curvature(acc);
        let carry = self.ecc_non_zero_point_downgrade(&rand_acc_point_neg);

        Ok(self.ecc_add(&acc, &carry))
    }

    fn msm_unsafe(
        &mut self,
        points: &Vec<AssignedPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> Result<AssignedPoint<C, N>, UnsafeError> {
        let r1 = C::generator() * C::Scalar::rand();
        let r2 = C::generator() * C::Scalar::rand();

        let mut non_zero_points = vec![];
        let mut normalized_scalars = vec![];
        let non_zero_p = self.assign_non_zero_point(&C::generator().to_curve());
        let s_zero = self.ecc_assign_zero_scalar();

        for (p, s) in points.iter().zip(scalars.iter()) {
            let s = self.ecc_bisec_scalar(&p.z, &s_zero, s);
            let p = self.ecc_bisec_to_non_zero_point(p, &non_zero_p);
            non_zero_points.push(p);
            normalized_scalars.push(s);
        }
        let p = if self.has_select_chip() {
            self.msm_batch_on_group_non_zero_with_select_chip(
                &non_zero_points,
                &normalized_scalars,
                r1,
                r2,
            )?
        } else {
            self.msm_batch_on_group_non_zero_without_select_chip(
                &non_zero_points,
                &normalized_scalars,
                r1,
                r2,
            )?
        };
        Ok(p)
    }

    fn msm(
        &mut self,
        points: &Vec<AssignedPoint<C, N>>,
        scalars: &Vec<Self::AssignedScalar>,
    ) -> AssignedPoint<C, N> {
        self.msm_unsafe(points, scalars).unwrap()
    }

    fn ecc_mul(&mut self, a: &AssignedPoint<C, N>, s: Self::AssignedScalar) -> AssignedPoint<C, N> {
        self.msm_unsafe(&vec![a.clone()], &vec![s.clone()]).unwrap()
    }

    fn ecc_bisec_scalar(
        &mut self,
        cond: &AssignedCondition<N>,
        a: &Self::AssignedScalar,
        b: &Self::AssignedScalar,
    ) -> Self::AssignedScalar;

    fn ecc_assign_zero_scalar(&mut self) -> Self::AssignedScalar;
}

pub trait EccBaseIntegerChipWrapper<W: BaseExt, N: FieldExt> {
    fn base_integer_chip(&mut self) -> &mut dyn IntegerChipOps<W, N>;
    fn select_chip(&mut self) -> &mut dyn SelectChipOps<W, N>;
    fn has_select_chip(&self) -> bool;
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

    fn assign_non_zero_point(
        &mut self,
        c: &<C as CurveAffine>::CurveExt,
    ) -> AssignedNonZeroPoint<C, N> {
        let coordinates = c.to_affine().coordinates();
        let t: Option<_> = coordinates.map(|v| (v.x().clone(), v.y().clone())).into();
        let (x, y) = t.unwrap();
        let is_identity: bool = c.is_identity().into();
        assert!(!is_identity);

        let x = self.base_integer_chip().assign_w(&field_to_bn(&x));
        let y = self.base_integer_chip().assign_w(&field_to_bn(&y));

        // Constrain y^2 = x^3 + b
        // TODO: Optimize b
        let b = self.base_integer_chip().assign_int_constant(C::b());
        let y2 = self.base_integer_chip().int_square(&y);
        let x2 = self.base_integer_chip().int_square(&x);
        let x3 = self.base_integer_chip().int_mul(&x2, &x);
        let right = self.base_integer_chip().int_add(&x3, &b);

        self.base_integer_chip().assert_int_equal(&y2, &right);
        AssignedNonZeroPoint::new(x, y)
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
    ) -> AssignedInteger<C::Base, N> {
        let mut limbs_le = vec![];

        let limb_size = self.base_integer_chip().range_chip().info().limbs;
        for j in 0..limb_size as usize {
            let v = self
                .select_chip()
                .assign_selected_value(&p.limbs_le[j], *offset, g, sc);
            limbs_le.push(v);
            *offset += 1;
        }

        let native = self
            .select_chip()
            .assign_selected_value(&p.native, *offset, g, sc);
        *offset += 1;

        AssignedInteger::new(limbs_le, native, 1)
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
    ) -> AssignedPointWithCurvature<C, N> {
        let mut i = 0;
        let x = self.assign_selected_integer(&p.x, sc, g, &mut i);
        let y = self.assign_selected_integer(&p.y, sc, g, &mut i);
        let z = self.select_chip().assign_selected_value(&p.z.0, i, g, sc);
        i += 1;
        let c_v = self.assign_selected_integer(&p.curvature.0, sc, g, &mut i);
        let c_z = self
            .select_chip()
            .assign_selected_value(&p.curvature.1 .0, i, g, sc);
        // skip checking x y relation cause they are selected from well formed values
        AssignedPointWithCurvature {
            x,
            y,
            z: AssignedCondition(z),
            curvature: AssignedCurvature(c_v, AssignedCondition(c_z)),
        }
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

    fn lambda_to_point_non_zero(
        &mut self,
        lambda: &AssignedInteger<C::Base, N>,
        a: &AssignedNonZeroPoint<C, N>,
        b: &AssignedNonZeroPoint<C, N>,
    ) -> AssignedNonZeroPoint<C, N> {
        let l = lambda;

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

        AssignedNonZeroPoint::new(cx, cy)
    }

    fn ecc_add_unsafe(
        &mut self,
        a: &AssignedNonZeroPoint<C, N>,
        b: &AssignedNonZeroPoint<C, N>,
    ) -> Result<AssignedNonZeroPoint<C, N>, UnsafeError> {
        let diff_x = self.base_integer_chip().int_sub(&a.x, &b.x);
        let diff_y = self.base_integer_chip().int_sub(&a.y, &b.y);
        let (x_eq, tangent) = self.base_integer_chip().int_div(&diff_y, &diff_x);

        // x cannot be same
        let succeed = self.base_integer_chip().base_chip().try_assert_false(&x_eq);
        let res = self.lambda_to_point_non_zero(&tangent, a, b);

        if succeed {
            Ok(res)
        } else {
            Err(UnsafeError::AddSameOrNegPoint)
        }
    }

    fn ecc_double_unsafe(
        &mut self,
        a: &AssignedNonZeroPoint<C, N>,
    ) -> Result<AssignedNonZeroPoint<C, N>, UnsafeError> {
        // 3 * x ^ 2 / 2 * y
        let x_square = self.base_integer_chip().int_square(&a.x);
        let numerator = self
            .base_integer_chip()
            .int_mul_small_constant(&x_square, 3);
        let denominator = self.base_integer_chip().int_mul_small_constant(&a.y, 2);

        let (z, v) = self.base_integer_chip().int_div(&numerator, &denominator);

        // This line is unnecessary, but keep it for security.
        let succeed = self.base_integer_chip().base_chip().try_assert_false(&z);
        let res = self.lambda_to_point_non_zero(&v, &a, &a);

        if succeed {
            Ok(res)
        } else {
            Err(UnsafeError::AddIdentity)
        }
    }

    fn ecc_neg_non_zero(&mut self, a: &AssignedNonZeroPoint<C, N>) -> AssignedNonZeroPoint<C, N> {
        let x = a.x.clone();
        let y = self.base_integer_chip().int_neg(&a.y);

        AssignedNonZeroPoint::new(x, y)
    }

    fn ecc_reduce_non_zero(
        &mut self,
        a: &AssignedNonZeroPoint<C, N>,
    ) -> AssignedNonZeroPoint<C, N> {
        let x = self.base_integer_chip().reduce(&a.x);
        let y = self.base_integer_chip().reduce(&a.y);

        AssignedNonZeroPoint::new(x, y)
    }

    fn ecc_bisec_non_zero_point(
        &mut self,
        cond: &AssignedCondition<N>,
        a: &AssignedNonZeroPoint<C, N>,
        b: &AssignedNonZeroPoint<C, N>,
    ) -> AssignedNonZeroPoint<C, N> {
        let x = self.base_integer_chip().bisec_int(cond, &a.x, &b.x);
        let y = self.base_integer_chip().bisec_int(cond, &a.y, &b.y);

        AssignedNonZeroPoint::new(x, y)
    }

    fn bisec_candidate_non_zero(
        &mut self,
        candidates: &Vec<AssignedNonZeroPoint<C, N>>,
        group_bits: &Vec<AssignedCondition<N>>,
    ) -> AssignedNonZeroPoint<C, N> {
        let mut curr_candidates: Vec<_> = candidates.clone();
        for bit in group_bits {
            let mut next_candidates = vec![];

            for it in curr_candidates.chunks(2) {
                let a0 = &it[0];
                let a1 = &it[1];

                let cell = self.ecc_bisec_non_zero_point(&bit, a1, a0);
                next_candidates.push(cell);
            }
            curr_candidates = next_candidates;
        }
        assert_eq!(curr_candidates.len(), 1);
        curr_candidates[0].clone()
    }

    fn pick_candidate_non_zero(
        &mut self,
        candidates: &Vec<AssignedNonZeroPoint<C, N>>,
        group_bits: &Vec<AssignedCondition<N>>,
    ) -> (AssignedValue<N>, AssignedNonZeroPoint<C, N>) {
        let curr_candidates: Vec<_> = candidates.clone();
        let index_vec = group_bits
            .iter()
            .enumerate()
            .map(|(i, x)| (&x.0, N::from(1u64 << i)))
            .collect();

        let mut base_chip = self.base_integer_chip().base_chip();
        let index = base_chip.sum_with_constant(index_vec, None);
        let index_i = (index.val.to_repr().as_ref())[0] as usize;

        let ci = &curr_candidates[index_i];
        (index, ci.clone())
    }

    fn assign_selected_point_non_zero(
        &mut self,
        p: &AssignedNonZeroPoint<C, N>,
        sc: &AssignedValue<N>,
        g: usize,
    ) -> AssignedNonZeroPoint<C, N> {
        let mut i = 0;
        let x = self.assign_selected_integer(&p.x, sc, g, &mut i);
        let y = self.assign_selected_integer(&p.y, sc, g, &mut i);

        // skip checking x y relation cause they are selected from well formed values
        AssignedNonZeroPoint { x, y }
    }

    fn assign_cache_point_non_zero(&mut self, p: &AssignedNonZeroPoint<C, N>, g: usize, sc: usize) {
        let mut i = 0;
        self.assign_cache_integer(&p.x, sc, g, &mut i);
        self.assign_cache_integer(&p.y, sc, g, &mut i);
    }

    fn ecc_assert_equal_non_zero(
        &mut self,
        a: &AssignedNonZeroPoint<C, N>,
        b: &AssignedNonZeroPoint<C, N>,
    ) {
        self.base_integer_chip().assert_int_equal(&a.x, &b.x);
        self.base_integer_chip().assert_int_equal(&a.y, &b.y);
    }

    fn ecc_assert_non_zero_point(
        &mut self,
        a: &AssignedPoint<C, N>,
    ) -> Result<AssignedNonZeroPoint<C, N>, UnsafeError> {
        let succeed = self.base_integer_chip().base_chip().try_assert_false(&a.z);

        if succeed {
            Ok(AssignedNonZeroPoint {
                x: a.x.clone(),
                y: a.y.clone(),
            })
        } else {
            Err(UnsafeError::AssignIdentity)
        }
    }

    fn ecc_non_zero_point_downgrade(
        &mut self,
        a: &AssignedNonZeroPoint<C, N>,
    ) -> AssignedPoint<C, N> {
        let zero = self
            .base_integer_chip()
            .base_chip()
            .assign_constant(N::zero());
        AssignedPoint {
            x: a.x.clone(),
            y: a.y.clone(),
            z: AssignedCondition(zero),
        }
    }

    fn ecc_bisec_to_non_zero_point(
        &mut self,
        a: &AssignedPoint<C, N>,
        b: &AssignedNonZeroPoint<C, N>,
    ) -> AssignedNonZeroPoint<C, N> {
        let x = self.base_integer_chip().bisec_int(&a.z, &b.x, &a.x);
        let y = self.base_integer_chip().bisec_int(&a.z, &b.y, &a.y);

        AssignedNonZeroPoint::new(x, y)
    }
}
