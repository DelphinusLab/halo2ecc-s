use crate::assign::{AssignedCondition, AssignedFq2, AssignedG2Affine, AssignedG2OnProvePrepared};
use crate::circuit::base_chip::BaseChipOps;
use crate::circuit::ecc_chip::EccChipBaseOps;
use crate::circuit::fq12::{Fq12ChipOps, Fq2ChipOps};
use crate::circuit::pairing_chip::PairingChipOnProvePairingOps;
use crate::context::IntegerContext;
use crate::context::{Context, NativeScalarEccContext};
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::pairing::bn256::{Fr, G1Affine};
use halo2_proofs::pairing::group::cofactor::CofactorCurveAffine;
use rand::rngs::OsRng;
use std::cell::RefCell;
use std::rc::Rc;

use halo2_proofs::pairing::bn256;
use halo2_proofs::pairing::bn256::Fq;
use halo2_proofs::pairing::bn256::Fq12;
use num_bigint::BigUint;
use num_traits::Num;
use num_traits::ToPrimitive;
// use ark_ff::{One};
use ark_std::One;
use halo2_proofs::arithmetic::{BaseExt, Field, MillerLoopResult};
use halo2_proofs::pairing::group::{Curve, Group};
use std::str::FromStr;

use std::ops::Mul;
use std::ops::Neg;

#[test]
fn test_checkpairing_with_c_wi() {
    // exp = 6x + 2 + p - p^2 = lambda - p^3
    let fq_module = Fq::MODULUS;
    let hex_str = fq_module
        .strip_prefix("0x")
        .or_else(|| fq_module.strip_prefix("0X"))
        .unwrap_or(fq_module);
    let p_pow3 = &BigUint::from_str_radix(hex_str, 16).unwrap().pow(3_u32);

    //0x1baaa710b0759ad331ec15183177faf68148fd2e5e487f1c2421c372dee2ddcdd45cf150c7e2d75ab87216b02105ec9bf0519bc6772f06e788e401a57040c54eb9b42c6f8f8e030b136a4fdd951c142faf174e7e839ac9157f83d3135ae0c55
    let lambda = BigUint::from_str(
        "10486551571378427818905133077457505975146652579011797175399169355881771981095211883813744499745558409789005132135496770941292989421431235276221147148858384772096778432243207188878598198850276842458913349817007302752534892127325269"
    ).unwrap();

    let (exp, sign) = if lambda > *p_pow3 {
        (lambda - p_pow3, true)
    } else {
        (p_pow3 - lambda, false)
    };

    // prove e(P1, Q1) = e(P2, Q2)
    // namely e(-P1, Q1) * e(P2, Q2) = 1
    let p1 = bn256::G1::random(&mut OsRng);
    let q2 = bn256::G2::random(&mut OsRng);
    let factor = bn256::Fr::from_raw([3_u64, 0, 0, 0]);
    let p2 = p1.mul(&factor).to_affine();
    let q1 = q2.mul(&factor).to_affine();
    let q1_prepared = bn256::G2Prepared::from(q1);
    let q2_prepared = bn256::G2Prepared::from(q2.to_affine());

    // f^{lambda - p^3} * wi = c^lambda
    // equivalently (f * c_inv)^{lambda - p^3} * wi = c_inv^{-p^3} = c^{p^3}
    assert_eq!(
        Fq12::one(),
        bn256::multi_miller_loop(&[(&p1.neg().to_affine(), &q1_prepared), (&p2, &q2_prepared)])
            .final_exponentiation()
            .0,
    );

    let f =
        bn256::multi_miller_loop(&[(&p1.neg().to_affine(), &q1_prepared), (&p2, &q2_prepared)]).0;
    let (c, wi) = compute_c_wi(f);
    let c_inv = c.invert().unwrap();
    let hint = if sign {
        f * wi * (c_inv.pow_vartime(exp.to_u64_digits()))
    } else {
        f * wi * (c_inv.pow_vartime(exp.to_u64_digits()).invert().unwrap())
    };

    assert_eq!(hint, c.pow_vartime(p_pow3.to_u64_digits()));

    assert_eq!(
        Fq12::one(),
        bn256::multi_miller_loop_c_wi(
            &bn256::Gt(c),
            &bn256::Gt(wi),
            &[(&p1.neg().to_affine(), &q1_prepared), (&p2, &q2_prepared)]
        )
        .0,
    );
    println!("multi_miller_loop_c_wi verify done!");

    let ctx = Rc::new(RefCell::new(Context::new()));
    let ctx = IntegerContext::<halo2_proofs::pairing::bn256::Fq, Fr>::new(ctx);
    let mut ctx = NativeScalarEccContext::<G1Affine>(ctx, 0);

    let c_assign = ctx.fq12_assign_value(decode_fq12(&c));
    let wi_assign = ctx.fq12_assign_value(decode_fq12(&wi));

    let p1_assign = ctx.assign_point(&-p1);
    let p2_assign = ctx.assign_point(&p2.to_curve());

    let q1x = ctx.fq2_assign_constant((
        q1.coordinates().unwrap().x().c0,
        q1.coordinates().unwrap().x().c1,
    ));
    let q1y = ctx.fq2_assign_constant((
        q1.coordinates().unwrap().y().c0,
        q1.coordinates().unwrap().y().c1,
    ));
    let q1_assign = AssignedG2Affine::new(
        q1x,
        q1y,
        AssignedCondition(ctx.0.ctx.borrow_mut().assign_constant(Fr::zero())),
    );

    let q2_affine = q2.to_affine();
    let q2x = ctx.fq2_assign_constant((
        q2_affine.coordinates().unwrap().x().c0,
        q2_affine.coordinates().unwrap().x().c1,
    ));
    let q2y = ctx.fq2_assign_constant((
        q2_affine.coordinates().unwrap().y().c0,
        q2_affine.coordinates().unwrap().y().c1,
    ));
    let q2_assign = AssignedG2Affine::new(
        q2x,
        q2y,
        AssignedCondition(ctx.0.ctx.borrow_mut().assign_constant(Fr::zero())),
    );

    let timer = start_timer!(|| "setup");
    ctx.check_pairing_c_wi(
        &c_assign,
        &wi_assign,
        &[(&p1_assign, &q1_assign), (&p2_assign, &q2_assign)],
    );
    end_timer!(timer);
    println!(
        "check done,base_offset ={},range={}",
        ctx.0.ctx.borrow().base_offset,
        ctx.0.ctx.borrow().range_offset
    );
}

#[test]
fn test_on_prove_pairing() {
    // exp = 6x + 2 + p - p^2 = lambda - p^3
    let fq_module = Fq::MODULUS;
    let hex_str = fq_module
        .strip_prefix("0x")
        .or_else(|| fq_module.strip_prefix("0X"))
        .unwrap_or(fq_module);
    let p_pow3 = &BigUint::from_str_radix(hex_str, 16).unwrap().pow(3_u32);

    //0x1baaa710b0759ad331ec15183177faf68148fd2e5e487f1c2421c372dee2ddcdd45cf150c7e2d75ab87216b02105ec9bf0519bc6772f06e788e401a57040c54eb9b42c6f8f8e030b136a4fdd951c142faf174e7e839ac9157f83d3135ae0c55
    let lambda = BigUint::from_str(
        "10486551571378427818905133077457505975146652579011797175399169355881771981095211883813744499745558409789005132135496770941292989421431235276221147148858384772096778432243207188878598198850276842458913349817007302752534892127325269"
    ).unwrap();

    let (exp, sign) = if lambda > *p_pow3 {
        (lambda - p_pow3, true)
    } else {
        (p_pow3 - lambda, false)
    };

    // prove e(P1, Q1) = e(P2, Q2)
    // namely e(-P1, Q1) * e(P2, Q2) = 1
    let p1 = bn256::G1::random(&mut OsRng);
    let q2 = bn256::G2::random(&mut OsRng);
    let factor = bn256::Fr::from_raw([3_u64, 0, 0, 0]);
    let p2 = p1.mul(&factor).to_affine();
    let q1 = q2.mul(&factor).to_affine();
    let q1_on_prove_prepared = bn256::G2OnProvePrepared::from(q1);
    let q2_on_prove_prepared = bn256::G2OnProvePrepared::from(q2.to_affine());

    let f = bn256::multi_miller_loop_on_prove_pairing_prepare(&[
        (&p1.neg().to_affine(), &q1_on_prove_prepared),
        (&p2, &q2_on_prove_prepared),
    ]);

    assert_eq!(Fq12::one(), f.final_exponentiation().0);
    let f = f.0;

    let (c, wi) = compute_c_wi(f);
    let c_inv = c.invert().unwrap();
    let hint = if sign {
        f * wi * (c_inv.pow_vartime(exp.to_u64_digits()))
    } else {
        f * wi * (c_inv.pow_vartime(exp.to_u64_digits()).invert().unwrap())
    };
    assert_eq!(hint, c.pow_vartime(p_pow3.to_u64_digits()));

    let ctx = Rc::new(RefCell::new(Context::new()));
    let ctx = IntegerContext::<halo2_proofs::pairing::bn256::Fq, Fr>::new(ctx);
    let mut ctx = NativeScalarEccContext::<G1Affine>(ctx, 0);

    let c_assign = ctx.fq12_assign_value(decode_fq12(&c));
    let wi_assign = ctx.fq12_assign_value(decode_fq12(&wi));

    let mut coeffs_q1: Vec<[AssignedFq2<Fq, Fr>; 2]> = vec![];
    for v in bn256::get_g2_on_prove_prepared_coeffs(&q1_on_prove_prepared).iter() {
        coeffs_q1.push([
            ctx.fq2_assign_constant((v.0 .0, v.0 .1)),
            ctx.fq2_assign_constant((v.1 .0, v.1 .1)),
        ]);
    }
    let mut coeffs_q2: Vec<[AssignedFq2<Fq, Fr>; 2]> = vec![];
    for v in bn256::get_g2_on_prove_prepared_coeffs(&q2_on_prove_prepared).iter() {
        coeffs_q2.push([
            ctx.fq2_assign_constant((v.0 .0, v.0 .1)),
            ctx.fq2_assign_constant((v.1 .0, v.1 .1)),
        ]);
    }

    let p1_assign = ctx.assign_point(&-p1);
    let p2_assign = ctx.assign_point(&p2.to_curve());

    let q1x = ctx.fq2_assign_constant((
        q1.coordinates().unwrap().x().c0,
        q1.coordinates().unwrap().x().c1,
    ));
    let q1y = ctx.fq2_assign_constant((
        q1.coordinates().unwrap().y().c0,
        q1.coordinates().unwrap().y().c1,
    ));
    let q1_assign = AssignedG2Affine::new(
        q1x,
        q1y,
        AssignedCondition(ctx.0.ctx.borrow_mut().assign_constant(Fr::zero())),
    );

    let q2_affine = q2.to_affine();
    let q2x = ctx.fq2_assign_constant((
        q2_affine.coordinates().unwrap().x().c0,
        q2_affine.coordinates().unwrap().x().c1,
    ));
    let q2y = ctx.fq2_assign_constant((
        q2_affine.coordinates().unwrap().y().c0,
        q2_affine.coordinates().unwrap().y().c1,
    ));
    let q2_assign = AssignedG2Affine::new(
        q2x,
        q2y,
        AssignedCondition(ctx.0.ctx.borrow_mut().assign_constant(Fr::zero())),
    );
    let q1_prepared = AssignedG2OnProvePrepared::new(coeffs_q1, q1_assign);
    let q2_prepared = AssignedG2OnProvePrepared::new(coeffs_q2, q2_assign);
    let timer = start_timer!(|| "setup");
    ctx.check_pairing_on_prove_pairing(
        &c_assign,
        &wi_assign,
        &[(&p1_assign, &q1_prepared), (&p2_assign, &q2_prepared)],
    );
    end_timer!(timer);
    println!(
        "check done,base_offset ={},range={}",
        ctx.0.ctx.borrow().base_offset,
        ctx.0.ctx.borrow().range_offset
    );
}

fn decode_fq12(
    a: &Fq12,
) -> (
    ((Fq, Fq), (Fq, Fq), (Fq, Fq)),
    ((Fq, Fq), (Fq, Fq), (Fq, Fq)),
) {
    return (
        (
            (a.c0.c0.c0, a.c0.c0.c1),
            (a.c0.c1.c0, a.c0.c1.c1),
            (a.c0.c2.c0, a.c0.c2.c1),
        ),
        (
            (a.c1.c0.c0, a.c1.c0.c1),
            (a.c1.c1.c0, a.c1.c1.c1),
            (a.c1.c2.c0, a.c1.c2.c1),
        ),
    );
}

fn tonelli_shanks_cubic(a: Fq12, c: Fq12, s: u32, t: BigUint, k: BigUint) -> Fq12 {
    // let mut r = a.pow(t.to_u64_digits());
    let mut r = a.pow_vartime(t.to_u64_digits());
    let e = 3_u32.pow(s - 1);
    let exp = 3_u32.pow(s) * &t;

    // compute cubic root of (a^t)^-1, say h
    let (mut h, cc, mut c) = (
        Fq12::one(),
        // c.pow([e as u64]),
        c.pow_vartime([e as u64]),
        c.invert().unwrap(),
    );
    for i in 1..(s as i32) {
        let delta = (s as i32) - i - 1;
        let d = if delta < 0 {
            r.pow_vartime((&exp / 3_u32.pow((-delta) as u32)).to_u64_digits())
        } else {
            r.pow_vartime([3_u32.pow(delta as u32).to_u64().unwrap()])
        };
        if d == cc {
            (h, r) = (h * c, r * c.pow_vartime([3_u64]));
        } else if d == cc.pow_vartime([2_u64]) {
            (h, r) = (
                h * c.pow_vartime([2_u64]),
                r * c.pow_vartime([3_u64]).pow_vartime([2_u64]),
            );
        }
        c = c.pow_vartime([3_u64])
    }

    // recover cubic root of a
    r = a.pow_vartime(k.to_u64_digits()) * h;
    if t == 3_u32 * k + 1_u32 {
        r = r.invert().unwrap();
    }

    assert_eq!(r.pow_vartime([3_u64]), a);
    r
}

// refer from Algorithm 5 of "On Proving Pairings"(https://eprint.iacr.org/2024/640.pdf)
fn compute_c_wi(f: Fq12) -> (Fq12, Fq12) {
    // let p = BigUint::from_str_radix(Fq::MODULUS, 16).unwrap();
    let p = BigUint::from_str(
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
    )
    .unwrap();

    let r = BigUint::from_str(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    )
    .unwrap();
    let lambda = BigUint::from_str(
        "10486551571378427818905133077457505975146652579011797175399169355881771981095211883813744499745558409789005132135496770941292989421431235276221147148858384772096778432243207188878598198850276842458913349817007302752534892127325269"
    ).unwrap();
    let s = 3_u32;
    let exp = p.pow(12_u32) - 1_u32;
    let h = &exp / &r;
    let t = &exp / 3_u32.pow(s);
    let k = (&t + 1_u32) / 3_u32;
    let m = &lambda / &r;
    let d = 3_u32;
    let mm = &m / d;

    // let mut prng = ChaCha20Rng::seed_from_u64(0);
    let cofactor_cubic = 3_u32.pow(s - 1) * &t;

    // make f is r-th residue, but it's not cubic residue
    assert_eq!(f.pow_vartime(h.to_u64_digits()), Fq12::one());
    //todo sometimes  f is cubic residue
    // assert_ne!(f.pow_vartime(cofactor_cubic.to_u64_digits()), Fq12::one());

    // sample a proper scalar w which is cubic non-residue
    let w = {
        let (mut w, mut z) = (Fq12::one(), Fq12::one());
        while w == Fq12::one() {
            // choose z which is 3-th non-residue
            let mut legendre = Fq12::one();
            while legendre == Fq12::one() {
                z = Fq12::random(&mut OsRng);
                legendre = z.pow_vartime(cofactor_cubic.to_u64_digits());
            }
            // obtain w which is t-th power of z
            w = z.pow_vartime(t.to_u64_digits());
        }
        w
    };
    // make sure 27-th root w, is 3-th non-residue and r-th residue
    assert_ne!(w.pow_vartime(cofactor_cubic.to_u64_digits()), Fq12::one());
    assert_eq!(w.pow_vartime(h.to_u64_digits()), Fq12::one());

    let wi = if f.pow_vartime(cofactor_cubic.to_u64_digits()) == Fq12::one() {
        println!("f is fq12_one------------");
        Fq12::one()
    } else {
        // just two option, w and w^2, since w^3 must be cubic residue, leading f*w^3 must not be cubic residue
        let mut wi = w;
        if (f * wi).pow_vartime(cofactor_cubic.to_u64_digits()) != Fq12::one() {
            assert_eq!(
                (f * w * w).pow_vartime(cofactor_cubic.to_u64_digits()),
                Fq12::one()
            );
            wi = w * w;
        }
        wi
    };

    assert_eq!(wi.pow_vartime(h.to_u64_digits()), Fq12::one());

    assert_eq!(lambda, &d * &mm * &r);
    // f1 is scaled f
    let f1 = f * wi;

    // r-th root of f1, say f2
    let r_inv = r.modinv(&h).unwrap();
    assert_ne!(r_inv, BigUint::one());
    let f2 = f1.pow_vartime(r_inv.to_u64_digits());
    assert_ne!(f2, Fq12::one());

    // m'-th root of f, say f3
    let mm_inv = mm.modinv(&(r * h)).unwrap();
    assert_ne!(mm_inv, BigUint::one());
    let f3 = f2.pow_vartime(mm_inv.to_u64_digits());
    assert_eq!(f3.pow_vartime(cofactor_cubic.to_u64_digits()), Fq12::one());
    assert_ne!(f3, Fq12::one());

    // d-th (cubic) root, say c
    let c = tonelli_shanks_cubic(f3, w, s, t, k);
    assert_ne!(c, Fq12::one());
    assert_eq!(c.pow_vartime(lambda.to_u64_digits()), f * wi);

    (c, wi)
}
