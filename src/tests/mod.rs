use std::sync::Arc;

use ark_std::{end_timer, start_timer};
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{floor_planner::FlatFloorPlanner, Layouter},
    dev::MockProver,
    pairing::bn256::{Bn256, Fr, G1Affine},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error,
        SingleVerifier,
    },
    poly::commitment::{Params, ParamsVerifier},
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use rand::{rngs::OsRng, SeedableRng};
use rand_xorshift::XorShiftRng;

use crate::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
        select_chip::{SelectChip, SelectChipConfig},
    },
    context::{Context, Records},
};

pub mod base_chip;
pub mod general_scalar_ecc_chip;
pub mod general_scalar_pairing_chip;
pub mod integer_chip;
pub mod native_scalar_ecc_chip;
pub mod native_scalar_pairing_chip;
pub mod range_chip;

fn random<N: BaseExt>() -> N {
    let seed = chrono::offset::Utc::now()
        .timestamp_nanos()
        .try_into()
        .unwrap();
    let rng = XorShiftRng::seed_from_u64(seed);
    N::random(rng)
}

fn random_fr() -> halo2_proofs::pairing::bn256::Fr {
    random::<halo2_proofs::pairing::bn256::Fr>()
}

fn random_fq() -> halo2_proofs::pairing::bn256::Fq {
    random::<halo2_proofs::pairing::bn256::Fq>()
}

fn random_bls12_381_fr() -> halo2_proofs::pairing::bls12_381::Fr {
    random::<halo2_proofs::pairing::bls12_381::Fr>()
}

fn random_bls12_381_fq() -> halo2_proofs::pairing::bls12_381::Fq {
    random::<halo2_proofs::pairing::bls12_381::Fq>()
}

#[derive(Clone)]
struct TestChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
    select_chip_config: SelectChipConfig,
}

#[derive(Default, Clone)]
struct TestCircuit<N: FieldExt> {
    records: Records<N>,
}

impl<N: FieldExt> Circuit<N> for TestCircuit<N> {
    type Config = TestChipConfig;
    type FloorPlanner = FlatFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<N>::configure(meta);
        let select_chip_config = SelectChip::<N>::configure(meta);
        TestChipConfig {
            base_chip_config,
            range_chip_config,
            select_chip_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let base_chip = BaseChip::new(config.base_chip_config);
        let range_chip = RangeChip::<N>::new(config.range_chip_config);
        let select_chip = SelectChip::<N>::new(config.select_chip_config);

        range_chip.init_table(&mut layouter)?;

        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                self.records
                    .assign_all(&mut region, &base_chip, &range_chip, &select_chip)?;
                end_timer!(timer);
                Ok(())
            },
        )?;

        Ok(())
    }
}

pub fn run_circuit_on_bn256(ctx: Context<Fr>, k: u32) {
    println!(
        "offset {} {} {}",
        ctx.range_offset, ctx.base_offset, ctx.select_offset
    );

    let circuit = TestCircuit::<Fr> {
        records: Arc::try_unwrap(ctx.records).unwrap().into_inner().unwrap(),
    };

    let prover = match MockProver::run(k, &circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}

pub fn bench_circuit_on_bn256(ctx: Context<Fr>, k: u32) {
    println!("offset {} {}", ctx.range_offset, ctx.base_offset);

    let circuit = TestCircuit::<Fr> {
        records: Arc::try_unwrap(ctx.records).unwrap().into_inner().unwrap(),
    };

    let timer = start_timer!(|| format!("build params with K = {}", k));
    let params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(k);
    end_timer!(timer);

    let timer = start_timer!(|| "build vk");
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    end_timer!(timer);

    let vk_for_verify = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");

    let timer = start_timer!(|| "build pk");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    end_timer!(timer);

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let timer = start_timer!(|| "create proof");
    create_proof(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
        .expect("proof generation should not fail");
    end_timer!(timer);

    let proof = transcript.finalize();

    let params_verifier: ParamsVerifier<Bn256> = params.verifier(0).unwrap();

    let strategy = SingleVerifier::new(&params_verifier);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    let timer = start_timer!(|| "verify proof");
    verify_proof(
        &params_verifier,
        &vk_for_verify,
        strategy,
        &[&[]],
        &mut transcript,
    )
    .unwrap();
    end_timer!(timer);
}

// for circuit without select chip

#[derive(Clone)]
struct TestNoSelectChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
}

#[derive(Default, Clone)]
struct TestNoSelectCircuit<N: FieldExt> {
    records: Records<N>,
}

impl<N: FieldExt> Circuit<N> for TestNoSelectCircuit<N> {
    type Config = TestNoSelectChipConfig;
    type FloorPlanner = FlatFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<N>::configure(meta);
        TestNoSelectChipConfig {
            base_chip_config,
            range_chip_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let base_chip = BaseChip::new(config.base_chip_config);
        let range_chip = RangeChip::<N>::new(config.range_chip_config);

        range_chip.init_table(&mut layouter)?;

        layouter.assign_region(
            || "base",
            |region| {
                let timer = start_timer!(|| "assign");
                self.records.assign_all_with_optional_select_chip(
                    region,
                    &base_chip,
                    &range_chip,
                    None,
                )?;
                end_timer!(timer);
                Ok(())
            },
        )?;

        Ok(())
    }
}

pub fn run_circuit_on_bn256_without_select_chip(ctx: Context<Fr>, k: u32) {
    println!(
        "offset {} {} {}",
        ctx.range_offset, ctx.base_offset, ctx.select_offset
    );

    let circuit = TestNoSelectCircuit::<Fr> {
        records: Arc::try_unwrap(ctx.records).unwrap().into_inner().unwrap(),
    };

    let prover = match MockProver::run(k, &circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}

pub fn bench_circuit_on_bn256_without_select_chip(ctx: Context<Fr>, k: u32) {
    println!("offset {} {}", ctx.range_offset, ctx.base_offset);

    let circuit = TestNoSelectCircuit::<Fr> {
        records: Arc::try_unwrap(ctx.records).unwrap().into_inner().unwrap(),
    };

    let timer = start_timer!(|| format!("build params with K = {}", k));
    let params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(k);
    end_timer!(timer);

    let timer = start_timer!(|| "build vk");
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    end_timer!(timer);

    let vk_for_verify = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");

    let timer = start_timer!(|| "build pk");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    end_timer!(timer);

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let timer = start_timer!(|| "create proof");
    create_proof(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
        .expect("proof generation should not fail");
    end_timer!(timer);

    let proof = transcript.finalize();

    let params_verifier: ParamsVerifier<Bn256> = params.verifier(0).unwrap();

    let strategy = SingleVerifier::new(&params_verifier);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    let timer = start_timer!(|| "verify proof");
    verify_proof(
        &params_verifier,
        &vk_for_verify,
        strategy,
        &[&[]],
        &mut transcript,
    )
    .unwrap();
    end_timer!(timer);
}
