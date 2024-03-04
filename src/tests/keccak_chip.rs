use crate::circuit::keccak_chip::KeccakChipOps;
use crate::context::Context;
use crate::gate::base_chip::BaseChipOps;
use crate::tests::{random_fr, run_circuit_on_bn256};
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::pairing::bn256::G1Affine;
use halo2_proofs::transcript::Challenge255;
use halo2_proofs::transcript::EncodedChallenge;
use sha3::Digest;

#[test]
fn test_keccak_chip() {
    for i in (0..16).step_by(3) {
        let mut ctx = Context::<Fr>::new();
        {
            let timer = start_timer!(|| "setup");
            let mut hasher = sha3::Keccak256::new();
            let mut input = vec![];
            for _ in 0..i {
                let v = random_fr();

                let mut buf = vec![];
                v.write(&mut buf).unwrap();
                buf.resize(32, 0u8);
                buf.reverse();
                hasher.update(buf);

                input.push(ctx.assign(v));
            }

            let assigned_hash = ctx.hash(&input[..]);
            let mut bytes = hasher.finalize().as_slice().to_vec();
            bytes.reverse();
            bytes.resize(64, 0u8);
            let expected_hash =
                Challenge255::<G1Affine>::new(&bytes.try_into().unwrap()).get_scalar();
            let assigned_expected_hash = ctx.assign(expected_hash);

            ctx.assert_equal(&assigned_hash, &assigned_expected_hash);

            //println!("assigned_hash {:?}", assigned_hash);
            //println!("assigned_expected_hash {:?}", assigned_expected_hash);
            //println!("ctx {} {}", ctx.base_offset, ctx.range_offset);

            end_timer!(timer);
        }
        run_circuit_on_bn256(ctx, 20);
    }
}
