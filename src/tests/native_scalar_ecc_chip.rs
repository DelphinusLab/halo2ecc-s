use crate::assign::AssignedPoint;
use crate::circuit::base_chip::BaseChipOps;
use crate::circuit::ecc_chip::{EccChipBaseOps, EccChipScalarOps, UnsafeError};
use crate::context::IntegerContext;
use crate::context::{Context, NativeScalarEccContext};
use crate::tests::{random_fr, run_circuit_on_bn256, run_circuit_on_bn256_without_select_chip};
use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bn256::{Fr, G1Affine, G1};
use halo2_proofs::pairing::group::Group;
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn test_native_ecc_chip_with_select_chip() {
    let mut points = vec![];
    let mut scalars = vec![];
    let mut acc = G1::identity();

    for _ in 0..100 {
        let a = random_fr();
        let b = random_fr();
        let p = G1::generator() * a;
        acc = acc + p * b;
        points.push(p);
        scalars.push(b);
    }

    let timer = start_timer!(|| "setup");
    let build_circuit = |points: &Vec<G1>, scalars: &Vec<Fr>, acc: &G1| -> Result<_, UnsafeError> {
        let ctx = Rc::new(RefCell::new(Context::new()));
        let ctx = IntegerContext::<halo2_proofs::pairing::bn256::Fq, Fr>::new(ctx);
        let mut ctx = NativeScalarEccContext::new_with_select_chip(ctx);

        {
            let points = points
                .iter()
                .map(|x| ctx.assign_point(x))
                .collect::<Vec<_>>();
            let scalars = scalars
                .iter()
                .map(|x| ctx.0.ctx.borrow_mut().assign(*x))
                .collect::<Vec<_>>();

            let res = ctx.msm_unsafe(&points, &scalars)?;
            let res_expect: AssignedPoint<G1Affine, Fr> = ctx.assign_point(acc);
            ctx.ecc_assert_equal(&res, &res_expect);
        }

        Ok(ctx)
    };

    let mut final_ctx = None;
    let mut rest_tries = 10;
    while rest_tries > 0 && final_ctx.is_none() {
        final_ctx = build_circuit(&points, &scalars, &acc).ok();
        rest_tries -= 1;
    }
    end_timer!(timer);

    run_circuit_on_bn256(final_ctx.unwrap().into(), 22);
}

#[test]
fn test_native_ecc_chip_without_select_chip() {
    let mut points = vec![];
    let mut scalars = vec![];
    let mut acc = G1::identity();

    for _ in 0..100 {
        let a = random_fr();
        let b = random_fr();
        let p = G1::generator() * a;
        acc = acc + p * b;
        points.push(p);
        scalars.push(b);
    }

    let timer = start_timer!(|| "setup");
    let build_circuit = |points: &Vec<G1>, scalars: &Vec<Fr>, acc: &G1| -> Result<_, UnsafeError> {
        let ctx = Rc::new(RefCell::new(Context::new()));
        let ctx = IntegerContext::<halo2_proofs::pairing::bn256::Fq, Fr>::new(ctx);
        let mut ctx = NativeScalarEccContext::new_without_select_chip(ctx);
        {
            let points = points
                .iter()
                .map(|x| ctx.assign_point(x))
                .collect::<Vec<_>>();
            let scalars = scalars
                .iter()
                .map(|x| ctx.0.ctx.borrow_mut().assign(*x))
                .collect::<Vec<_>>();

            let res = ctx.msm_unsafe(&points, &scalars)?;
            let res_expect: AssignedPoint<G1Affine, Fr> = ctx.assign_point(acc);
            ctx.ecc_assert_equal(&res, &res_expect);
        }

        Ok(ctx)
    };

    let mut final_ctx = None;
    let mut rest_tries = 10;
    while rest_tries > 0 && final_ctx.is_none() {
        final_ctx = build_circuit(&points, &scalars, &acc).ok();
        rest_tries -= 1;
    }
    end_timer!(timer);

    run_circuit_on_bn256_without_select_chip(final_ctx.unwrap().into(), 22);
}
