use std::cell::RefCell;
use std::rc::Rc;

use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::arithmetic::FieldExt;

use super::base_chip::BaseChipOps;
use super::ecc_chip::EccBaseIntegerChipWrapper;
use super::ecc_chip::EccChipScalarOps;
use super::ecc_chip::Offset;
use super::ecc_chip::ParallelClone;
use super::ecc_chip::MSM_LIMIT;
use super::ecc_chip::MSM_PREFIX_OFFSET;
use super::integer_chip::IntegerChipOps;
use super::select_chip::SelectChipOps;
use crate::assign::AssignedCondition;
use crate::assign::AssignedInteger;
use crate::circuit::ecc_chip::EccChipBaseOps;
use crate::context::GeneralScalarEccContext;
use crate::context::IntegerContext;
use crate::pair;
use crate::utils::field_to_bn;

impl<C: CurveAffine, N: FieldExt> EccBaseIntegerChipWrapper<C::Base, N>
    for GeneralScalarEccContext<C, N>
{
    fn base_integer_chip(&mut self) -> &mut dyn IntegerChipOps<C::Base, N> {
        &mut self.base_integer_ctx
    }
    fn select_chip(&mut self) -> &mut dyn SelectChipOps<C::Base, N> {
        &mut self.base_integer_ctx
    }
    fn has_select_chip(&self) -> bool {
        true
    }
}

impl<C: CurveAffine, N: FieldExt> EccChipBaseOps<C, N> for GeneralScalarEccContext<C, N> {}

unsafe impl<C: CurveAffine, N: FieldExt> Send for GeneralScalarEccContext<C, N> {}

impl<C: CurveAffine, N: FieldExt> ParallelClone for GeneralScalarEccContext<C, N> {
    fn clone_with_offset(&self, offset_diff: &Offset) -> Self {
        let mut ctx = (*(*self.native_ctx).borrow()).clone_without_permutation();
        ctx.base_offset += offset_diff.base_offset_diff;
        ctx.range_offset += offset_diff.range_offset_diff;
        ctx.select_offset += offset_diff.select_offset_diff;

        let ctx = Rc::new(RefCell::new(ctx));
        let base_integer_ctx = IntegerContext {
            info: self.base_integer_ctx.info.clone(),
            ctx: ctx.clone(),
        };
        let scalar_integer_ctx = IntegerContext {
            info: self.scalar_integer_ctx.info.clone(),
            ctx: ctx.clone(),
        };
        Self {
            base_integer_ctx,
            scalar_integer_ctx,
            native_ctx: ctx.clone(),
            msm_prefix: self.msm_prefix,
        }
    }

    fn offset(&self) -> Offset {
        Offset {
            base_offset_diff: self.native_ctx.borrow().base_offset,
            range_offset_diff: self.native_ctx.borrow().range_offset,
            select_offset_diff: self.native_ctx.borrow().select_offset,
        }
    }

    fn merge(&self, other: Self) {
        let record = &mut self.native_ctx.borrow_mut().records;
        let record_other = &mut other.native_ctx.borrow_mut().records;

        record.permutations.append(&mut record_other.permutations);

        record.base_height = record.base_height.max(record_other.base_height);
        record.range_height = record.select_height.max(record_other.range_height);
        record.select_height = record.select_height.max(record_other.select_height);
    }
}

impl<C: CurveAffine, N: FieldExt> EccChipScalarOps<C, N> for GeneralScalarEccContext<C, N> {
    type AssignedScalar = AssignedInteger<C::Scalar, N>;

    fn decompose_scalar<const WINDOW_SIZE: usize>(
        &mut self,
        s: &Self::AssignedScalar,
    ) -> Vec<[AssignedCondition<N>; WINDOW_SIZE]> {
        let zero = N::zero();
        let one = N::one();
        let two = one + one;
        let two_inv = two.invert().unwrap();

        let s = self.scalar_integer_ctx.reduce(&s);
        let mut bits = vec![];

        for l in s.limbs_le {
            let v = field_to_bn(&l.val);
            let mut rest = l.clone();
            for j in 0..self.scalar_integer_ctx.info.limb_bits {
                let b = self.native_ctx.borrow_mut().assign_bit(v.bit(j).into());
                let v = (rest.val - b.0.val) * two_inv;
                rest = self
                    .native_ctx
                    .borrow_mut()
                    .one_line_with_last(
                        vec![pair!(&rest, -one), pair!(&b.0, one)],
                        pair!(v, two),
                        None,
                        (vec![], None),
                    )
                    .1;
                bits.push(b);
            }

            self.native_ctx.borrow_mut().assert_constant(&rest, zero);
        }

        let padding = bits.len() % WINDOW_SIZE;
        if padding != 0 {
            let zero = self.native_ctx.borrow_mut().assign_constant(zero);
            for _ in 0..padding {
                bits.push(AssignedCondition(zero));
            }
        }

        let mut res = bits
            .chunks(WINDOW_SIZE)
            .map(|x| Vec::from(x).try_into().unwrap())
            .collect::<Vec<_>>();

        res.reverse();

        res
    }

    fn get_and_increase_msm_prefix(&mut self) -> usize {
        let ret = self.msm_prefix;
        assert!(ret < MSM_LIMIT);
        self.msm_prefix += MSM_PREFIX_OFFSET;
        ret
    }

    fn ecc_bisec_scalar(
        &mut self,
        cond: &AssignedCondition<N>,
        a: &Self::AssignedScalar,
        b: &Self::AssignedScalar,
    ) -> Self::AssignedScalar {
        self.scalar_integer_ctx.bisec_int(cond, a, b)
    }

    fn ecc_assign_zero_scalar(&mut self) -> Self::AssignedScalar {
        self.scalar_integer_ctx
            .assign_int_constant(C::ScalarExt::zero())
    }
}
