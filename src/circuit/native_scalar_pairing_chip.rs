use crate::assign::{AssignedFq, AssignedFq6};
use crate::circuit::integer_chip::IntegerChipOps;
use crate::context::Context;
use crate::{
    assign::{AssignedFq12, AssignedFq2, AssignedG1Affine},
    context::NativeScalarEccContext,
};
use halo2_proofs::arithmetic::{BaseExt, CurveAffine, FieldExt};

impl<W: BaseExt, N: FieldExt> Context<W, N> {
    fn fq2_add(&mut self, a: &AssignedFq2<W, N>, b: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        (self.int_add(&a.0, &b.0), self.int_add(&a.1, &b.1))
    }
    fn fq2_mul(&mut self, a: &AssignedFq2<W, N>, b: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        let ab00 = self.int_mul(&a.0, &b.0);
        let ab11 = self.int_mul(&a.1, &b.1);
        let c0 = self.int_sub(&ab00, &ab11);

        let a01 = self.int_add(&a.0, &a.1);
        let b01 = self.int_add(&b.0, &b.1);
        let c1 = self.int_mul(&a01, &b01);
        let c1 = self.int_sub(&c1, &ab00);
        let c1 = self.int_sub(&c1, &ab11);

        (c0, c1)
    }
    fn fq2_sub(&mut self, a: &AssignedFq2<W, N>, b: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        (self.int_sub(&a.0, &b.0), self.int_sub(&a.1, &b.1))
    }
    fn fq2_double(&mut self, a: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        (self.int_add(&a.0, &a.0), self.int_add(&a.1, &a.1))
    }
    fn fq2_squre(&mut self, a: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        self.fq2_mul(a, a)
    }
    fn fq2_neg(&mut self, a: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        (self.int_neg(&a.0), self.int_neg(&a.1))
    }
    fn fq2_conjugate(&mut self, a: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        (a.0, self.int_neg(&a.1))
    }
    fn mul_by_nonresidue(&mut self, a: &AssignedFq2<W, N>) -> AssignedFq2<W, N> {
        todo!()
    }
}

impl<W: BaseExt, N: FieldExt> Context<W, N> {
    fn fq6_mul_by_01(
        &mut self,
        x: &AssignedFq6<W, N>,
        c0: &AssignedFq2<W, N>,
        c1: &AssignedFq2<W, N>,
    ) -> AssignedFq6<W, N> {
        let a = self.fq2_mul(&x.0, c0);
        let b = self.fq2_mul(&x.1, c1);

        // ((x.1 + x.2) * c1 - b) * nonresidue + a
        todo!()
    }
}

impl<W: BaseExt, N: FieldExt> Context<W, N> {
    fn fq12_mul_by_034(
        &mut self,
        x: &AssignedFq12<W, N>,
        c0: &AssignedFq2<W, N>,
        c3: &AssignedFq2<W, N>,
        c4: &AssignedFq2<W, N>,
    ) -> AssignedFq12<W, N> {
        todo!()
    }
}

impl<C: CurveAffine> NativeScalarEccContext<C> {
    fn ell(
        &mut self,
        f: &AssignedFq12<C::Base, C::Scalar>,
        coeffs: &(
            AssignedFq2<C::Base, C::Scalar>,
            AssignedFq2<C::Base, C::Scalar>,
            AssignedFq2<C::Base, C::Scalar>,
        ),
        p: &AssignedG1Affine<C, C::Scalar>,
    ) -> AssignedFq12<C::Base, C::Scalar> {
        let c00 = &coeffs.0 .0;
        let c01 = &coeffs.0 .1;
        let c10 = &coeffs.1 .0;
        let c11 = &coeffs.1 .1;

        let c00 = self.0.int_mul(&c00, &p.y);
        let c01 = self.0.int_mul(&c01, &p.y);
        let c10 = self.0.int_mul(&c10, &p.x);
        let c11 = self.0.int_mul(&c11, &p.x);

        self.0
            .fq12_mul_by_034(f, &(c00, c01), &(c10, c11), &coeffs.2)
    }
}
