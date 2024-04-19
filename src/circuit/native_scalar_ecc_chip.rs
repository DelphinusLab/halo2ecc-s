use std::cell::RefCell;
use std::rc::Rc;

use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::pairing::group::ff::PrimeField;
use num_integer::Integer;

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
use crate::assign::AssignedValue;
use crate::circuit::ecc_chip::EccChipBaseOps;
use crate::context::IntegerContext;
use crate::context::NativeScalarEccContext;
use crate::pair;
use crate::utils::bn_to_field;
use crate::utils::field_to_bn;

impl<C: CurveAffine> EccBaseIntegerChipWrapper<C::Base, C::ScalarExt>
    for NativeScalarEccContext<C>
{
    fn base_integer_chip(
        &mut self,
    ) -> &mut dyn IntegerChipOps<<C as CurveAffine>::Base, C::ScalarExt> {
        &mut self.0
    }
    fn select_chip(&mut self) -> &mut dyn SelectChipOps<<C as CurveAffine>::Base, C::ScalarExt> {
        if self.1 != usize::MAX {
            &mut self.0
        } else {
            println!("ERROR: select chip is not available");
            unreachable!()
        }
    }
    fn has_select_chip(&self) -> bool {
        self.1 < usize::MAX
    }
}

impl<C: CurveAffine> EccChipBaseOps<C, C::ScalarExt> for NativeScalarEccContext<C> {}

impl<C: CurveAffine> ParallelClone for NativeScalarEccContext<C> {
    fn apply_offset_diff(&mut self, offset_diff: &Offset) {
        self.0.ctx.borrow_mut().base_offset += offset_diff.base_offset_diff;
        self.0.ctx.borrow_mut().range_offset += offset_diff.range_offset_diff;
        self.0.ctx.borrow_mut().select_offset += offset_diff.select_offset_diff;
    }

    fn clone_with_offset(&self, offset_diff: &Offset) -> Self {
        let info = self.0.info.clone();
        let mut ctx = (*(*self.0.ctx).borrow()).clone_without_permutation();
        ctx.base_offset += offset_diff.base_offset_diff;
        ctx.range_offset += offset_diff.range_offset_diff;
        ctx.select_offset += offset_diff.select_offset_diff;
        Self(
            IntegerContext {
                info,
                ctx: Rc::new(RefCell::new(ctx)),
            },
            self.1,
        )
    }

    fn offset(&self) -> Offset {
        Offset {
            base_offset_diff: self.0.ctx.borrow().base_offset,
            range_offset_diff: self.0.ctx.borrow().range_offset,
            select_offset_diff: self.0.ctx.borrow().select_offset,
        }
    }

    fn merge(&self, other: Self) {
        let record = &mut self.0.ctx.borrow_mut().records;
        let record_other = &mut other.0.ctx.borrow_mut().records;

        record.permutations.append(&mut record_other.permutations);

        record.base_height = record.base_height.max(record_other.base_height);
        record.range_height = record.select_height.max(record_other.range_height);
        record.select_height = record.select_height.max(record_other.select_height);
    }
}

unsafe impl<C: CurveAffine> Send for NativeScalarEccContext<C> {}

impl<C: CurveAffine> EccChipScalarOps<C, C::ScalarExt> for NativeScalarEccContext<C> {
    type AssignedScalar = AssignedValue<C::ScalarExt>;

    fn decompose_scalar<const WINDOW_SIZE: usize>(
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
            let b0 = self.0.ctx.borrow_mut().assign_bit(b0);
            let b1 = self.0.ctx.borrow_mut().assign_bit(b1);
            let v_next: C::ScalarExt = bn_to_field(&(&s_bn >> (i * 2 + 2)));

            let cells = self.0.ctx.borrow_mut().one_line_with_last(
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
            self.0.ctx.borrow_mut().assert_bit(&v);
            bits.push(AssignedCondition(v));
        } else {
            self.0
                .ctx
                .borrow_mut()
                .assert_constant(&v, C::ScalarExt::zero())
        }

        let rem = <C::ScalarExt as PrimeField>::NUM_BITS as usize % WINDOW_SIZE;
        if rem > 0 {
            let zero = self
                .0
                .ctx
                .borrow_mut()
                .assign_constant(C::ScalarExt::zero());
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

    fn get_and_increase_msm_prefix(&mut self) -> usize {
        let ret = self.1;
        assert!(ret < MSM_LIMIT);
        self.1 += MSM_PREFIX_OFFSET;
        ret
    }

    fn ecc_bisec_scalar(
        &mut self,
        cond: &AssignedCondition<C::ScalarExt>,
        a: &Self::AssignedScalar,
        b: &Self::AssignedScalar,
    ) -> Self::AssignedScalar {
        self.base_integer_chip().base_chip().bisec(cond, a, b)
    }

    fn ecc_assign_constant_zero_scalar(&mut self) -> Self::AssignedScalar {
        self.base_integer_chip()
            .base_chip()
            .assign_constant(C::ScalarExt::zero())
    }
}
