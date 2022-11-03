use crate::circuit::base_chip::{BaseChip, BaseChipConfig, MUL_COLUMNS, VAR_COLUMNS};
use crate::context::Context;
use crate::pair;
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::marker::PhantomData;

enum TestCase {
    OneLineSingleThread,
    OneLineMultiThread,
}

impl Default for TestCase {
    fn default() -> TestCase {
        TestCase::OneLineSingleThread
    }
}

#[derive(Clone)]
struct TestBaseChipConfig {
    base_chip_config: BaseChipConfig,
}

#[derive(Default)]
struct TestBaseChipCircuit<N: FieldExt> {
    test_case: TestCase,
    _phantom: PhantomData<N>,
}

impl<N: FieldExt> TestBaseChipCircuit<N> {
    fn random() -> N {
        let seed = chrono::offset::Utc::now()
            .timestamp_nanos()
            .try_into()
            .unwrap();
        let rng = XorShiftRng::seed_from_u64(seed);
        N::random(rng)
    }

    fn setup_test_one_line_single_thread(&self, base_chip: &BaseChip<N>, ctx: &Context<N>) {
        let vars = [(); VAR_COLUMNS].map(|_| Self::random());
        let coeffs = [(); VAR_COLUMNS].map(|_| Self::random());
        let muls_coeffs = [(); MUL_COLUMNS].map(|_| Self::random());
        let next_var = Self::random();
        let next_coeff = Self::random();

        let result = {
            let mut result = N::zero();
            for i in 0..VAR_COLUMNS {
                result = result + vars[i] * coeffs[i]
            }
            for i in 0..MUL_COLUMNS {
                result = result + muls_coeffs[i] * vars[i * 2] * vars[i * 2 + 1]
            }
            result + next_var * next_coeff
        };

        let record = &mut ctx.records.lock().unwrap();

        let timer = start_timer!(|| "setup");
        for i in 0..10000 {
            base_chip.one_line(
                record,
                i * 2,
                (0..VAR_COLUMNS)
                    .map(|i| pair!(vars[i], coeffs[i]))
                    .collect(),
                Some(-result),
                (muls_coeffs.to_vec(), Some(next_coeff)),
            );

            base_chip.one_line_with_last(
                record,
                i * 2 + 1,
                vec![],
                pair!(next_var, N::zero()),
                None,
                (vec![], None),
            );
        }
        end_timer!(timer);
    }

    fn setup_test_one_line_multi_thread(&self, base_chip: BaseChip<N>, ctx: &Context<N>) {
        let vars = [(); VAR_COLUMNS].map(|_| Self::random());
        let coeffs = [(); VAR_COLUMNS].map(|_| Self::random());
        let muls_coeffs = [(); MUL_COLUMNS].map(|_| Self::random());
        let next_var = Self::random();
        let next_coeff = Self::random();

        let result = {
            let mut result = N::zero();
            for i in 0..VAR_COLUMNS {
                result = result + vars[i] * coeffs[i]
            }
            for i in 0..MUL_COLUMNS {
                result = result + muls_coeffs[i] * vars[i * 2] * vars[i * 2 + 1]
            }
            result + next_var * next_coeff
        };

        let timer = start_timer!(|| "setup");

        let c = 10000;
        let n = 10;
        for i in 0..n {
            let record = std::sync::Arc::clone(&ctx.records);
            let base_chip = base_chip.clone();
            std::thread::spawn(move || {
                let record = &mut record.lock().unwrap();
                let step = c / n;
                let start = i * step;
                for i in start..start + step {
                    base_chip.one_line(
                        record,
                        i * 2,
                        (0..VAR_COLUMNS)
                            .map(|i| pair!(vars[i], coeffs[i]))
                            .collect(),
                        Some(-result),
                        (muls_coeffs.to_vec(), Some(next_coeff)),
                    );

                    base_chip.one_line_with_last(
                        record,
                        i * 2 + 1,
                        vec![],
                        pair!(next_var, N::zero()),
                        None,
                        (vec![], None),
                    );
                }
            })
            .join()
            .unwrap();
        }
        end_timer!(timer);
    }
}

impl<N: FieldExt> Circuit<N> for TestBaseChipCircuit<N> {
    type Config = TestBaseChipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        let base_chip_config = BaseChip::configure(meta);
        TestBaseChipConfig { base_chip_config }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let base_chip = BaseChip::new(config.base_chip_config);

        let mut ctx = Context::new();
        match self.test_case {
            TestCase::OneLineSingleThread => {
                self.setup_test_one_line_single_thread(&base_chip, &mut ctx);
            }
            TestCase::OneLineMultiThread => {
                self.setup_test_one_line_multi_thread(base_chip.clone(), &mut ctx);
            }
        }

        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                ctx.records
                    .lock()
                    .unwrap()
                    .assign_all(&mut region, &base_chip)?;
                end_timer!(timer);
                Ok(())
            },
        )?;

        Ok(())
    }
}

#[test]
fn test_one_line_st() {
    const K: u32 = 16;
    let circuit = TestBaseChipCircuit::<Fr> {
        test_case: TestCase::OneLineSingleThread,
        _phantom: PhantomData,
    };
    let prover = match MockProver::run(K, &circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}

#[test]
fn test_one_line_mt() {
    const K: u32 = 16;
    let circuit = TestBaseChipCircuit::<Fr> {
        test_case: TestCase::OneLineMultiThread,
        _phantom: PhantomData,
    };
    let prover = match MockProver::run(K, &circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}
