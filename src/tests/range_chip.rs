use crate::circuit::range_chip::RangeChipOps;
use crate::context::{Context, IntegerContext};
use crate::tests::random_fq;
use crate::tests::run_circuit_on_bn256;
use crate::tests::run_circuit_on_bn256_expect_fail;
use crate::utils::field_to_bn;
use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bn256::{Fq, Fr};
use num_bigint::BigUint;
use num_integer::Integer;
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn test_range_chip() {
    let ctx = Context::new();

    let a = field_to_bn(&random_fq());
    let b = field_to_bn(&random_fq());
    let fq_modulus = field_to_bn(&-Fq::one()) + 1u64;
    let (d, r) = (&a * &b).div_rem(&fq_modulus);

    let timer = start_timer!(|| "setup");
    let mut ctx =
        IntegerContext::<halo2_proofs::pairing::bn256::Fq, Fr>::new(Rc::new(RefCell::new(ctx)));

    {
        let limbs = ctx.info().limbs;
        let non_leading_bits = (limbs - 1) * ctx.info().limb_bits;
        let common = &a & ((BigUint::from(1u64) << ctx.info().limbs) - 1u64);
        let a_leading = &a >> non_leading_bits;
        let b_leading = &b >> non_leading_bits;
        let d_leading = &d >> non_leading_bits;
        let r_leading = &r >> non_leading_bits;

        ctx.assign_nonleading_limb(&common);
        ctx.assign_w_ceil_leading_limb(&a_leading);
        ctx.assign_w_ceil_leading_limb(&b_leading);
        ctx.assign_w_ceil_leading_limb(&r_leading);
        ctx.assign_d_leading_limb(&d_leading);
    }

    end_timer!(timer);

    run_circuit_on_bn256(ctx.into(), 20);
}

#[test]
fn test_range_chip_full() {
    use crate::circuit::range_chip::decompose_bn;
    use crate::circuit::range_chip::COMMON_RANGE_BITS;
    {
        let mut ctx = Context::new();
        for bits_cap in 0..COMMON_RANGE_BITS * 6 {
            for bits in 0..bits_cap {
                if bits_cap > COMMON_RANGE_BITS && bits_cap < COMMON_RANGE_BITS * 2 {
                    // unreachable state
                    continue;
                }

                let v_bn = BigUint::from(1u64) << bits;
                let (v_n, v_vec) = decompose_bn(
                    &v_bn,
                    (bits_cap + COMMON_RANGE_BITS - 1) / COMMON_RANGE_BITS,
                    &BigUint::from((1 << COMMON_RANGE_BITS) - 1u64),
                );
                // println!("bits {} acc is {:?}, v_vec is {:?}", bits, v_n, v_vec);
                ctx.range_offset += ctx
                    .records
                    .assign_range_value(ctx.range_offset, v_vec, v_n, bits_cap)
                    .1;
            }
        }
        run_circuit_on_bn256(ctx.into(), 20);
        println!("pass success test");
    }

    for bits_cap in 1..=COMMON_RANGE_BITS * 6 {
        if bits_cap > COMMON_RANGE_BITS && bits_cap < COMMON_RANGE_BITS * 2 {
            // unreachable state
            continue;
        }

        for bits in bits_cap..=bits_cap + 1 {
            let mut ctx = Context::new();
            let v_bn = BigUint::from(1u64) << bits;
            let (v_n, v_vec) = decompose_bn(
                &v_bn,
                (bits + COMMON_RANGE_BITS - 1) / COMMON_RANGE_BITS,
                &BigUint::from(COMMON_RANGE_BITS),
            );
            ctx.range_offset += ctx
                .records
                .assign_range_value(ctx.range_offset, v_vec, v_n, bits_cap)
                .1;

            run_circuit_on_bn256_expect_fail(ctx.into(), 20);
            println!("pass failure test {} {}", bits_cap, bits);
        }
    }
}
