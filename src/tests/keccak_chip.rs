use crate::circuit::keccak_chip::KeccakChipOps;
use crate::context::Context;
use crate::gate::base_chip::BaseChipOps;
use crate::tests::{random_fr, run_circuit_on_bn256};
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::pairing::bn256::Fr;
use sha3::Digest;

#[test]
fn test_keccak_chip() {
    let mut ctx = Context::<Fr>::new();
    {
        let timer = start_timer!(|| "setup");
        let mut hasher = sha3::Keccak256::new();
        let mut input = vec![];
        for _ in 0..0 {
            let v = random_fr();

            let mut buf = vec![];
            v.write(&mut buf).unwrap();
            buf.resize(32, 0u8);
            buf.reverse();
            hasher.update(buf);

            input.push(ctx.assign(v));
        }

        let assigned_hash = ctx.hash(&input[..]);
        let result: [u8; 32] = hasher.finalize().as_slice().try_into().unwrap();
        println!("assigned_hash {:?}", assigned_hash);
        println!("result {:?}", result);
        println!("ctx {} {}", ctx.base_offset, ctx.range_offset);
        end_timer!(timer);
    }

    run_circuit_on_bn256(ctx, 20);
}
