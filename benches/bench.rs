#![allow(non_snake_case)]

extern crate groth_sahai_wrappers;

use criterion::{criterion_group, criterion_main, Criterion};

use ark_bls12_381::Bls12_381 as F;
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::UniformRand;

use ark_groth16::{Proof, VerifyingKey};
use ark_std::test_rng;

use groth_sahai::{AbstractCrs, CRS as GS_CRS};
use groth_sahai_wrappers::groth16::{prove_canon_g16_equations, verify_canon_g16_equations};

type G1Projective = <F as PairingEngine>::G1Projective;
type G2Projective = <F as PairingEngine>::G2Projective;

fn bench_gs_over_groth16_one_prove(c: &mut Criterion) {
    let mut rng = test_rng();
    let crs = GS_CRS::<F>::generate_crs(&mut rng);

    // NOTE: This is a mock Groth16 setup to make the underlying equation trivially satisfiable.
    let mock_beta_g2 = G2Projective::rand(&mut rng).into_affine();
    let mock_g16_vk: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_prepared_public_input = G1Projective::rand(&mut rng);
    let mock_g16_pf: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input.into_affine(),
        b: mock_g16_vk.gamma_g2,
        c: mock_g16_vk.alpha_g1,
    };
    c.bench_function(
        "Prove satisfiability of 1 Groth16 verification equation using Groth-Sahai",
        |bench| {
            bench.iter(|| {
                let _ = prove_canon_g16_equations(
                    &[(&mock_g16_pf, &mock_g16_vk, &mock_prepared_public_input)],
                    &crs,
                    &mut rng,
                );
            });
        },
    );
}

fn bench_gs_over_groth16_one_verify(c: &mut Criterion) {
    let mut rng = test_rng();
    let crs = GS_CRS::<F>::generate_crs(&mut rng);

    // NOTE: This is a mock Groth16 setup to make the underlying equation trivially satisfiable.
    let mock_beta_g2 = G2Projective::rand(&mut rng).into_affine();
    let mock_g16_vk: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_prepared_public_input = G1Projective::rand(&mut rng);
    let mock_g16_pf: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input.into_affine(),
        b: mock_g16_vk.gamma_g2,
        c: mock_g16_vk.alpha_g1,
    };
    let (xcoms, ycoms, gs_proofs) = prove_canon_g16_equations(
        &[(&mock_g16_pf, &mock_g16_vk, &mock_prepared_public_input)],
        &crs,
        &mut rng,
    );

    c.bench_function(
        "Verify satisfiability of 1 Groth16 verification equation using Groth-Sahai",
        |bench| {
            bench.iter(|| {
                let _ = verify_canon_g16_equations::<F>(
                    &[(&mock_g16_vk, &mock_prepared_public_input)],
                    (&xcoms, &ycoms, &gs_proofs),
                    &crs,
                );
            });
        },
    );
}

fn bench_gs_over_groth16_three_prove(c: &mut Criterion) {
    let mut rng = test_rng();
    let crs = GS_CRS::<F>::generate_crs(&mut rng);

    // NOTE: This is a mock Groth16 setup to make the underlying equation trivially satisfiable.
    let mock_beta_g2_vk1 = G2Projective::rand(&mut rng).into_affine();
    let mock_beta_g2_vk2 = G2Projective::rand(&mut rng).into_affine();
    let mock_beta_g2_vk3 = G2Projective::rand(&mut rng).into_affine();
    let mock_g16_vk1: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2_vk1,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2_vk1,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_g16_vk2: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2_vk2,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2_vk2,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_g16_vk3: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2_vk3,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2_vk3,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_prepared_public_input1 = G1Projective::rand(&mut rng);
    let mock_prepared_public_input2 = G1Projective::rand(&mut rng);
    let mock_prepared_public_input3 = G1Projective::rand(&mut rng);
    let mock_g16_pf1: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input1.into_affine(),
        b: mock_g16_vk1.gamma_g2,
        c: mock_g16_vk1.alpha_g1,
    };
    let mock_g16_pf2: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input2.into_affine(),
        b: mock_g16_vk2.gamma_g2,
        c: mock_g16_vk2.alpha_g1,
    };
    let mock_g16_pf3: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input3.into_affine(),
        b: mock_g16_vk3.gamma_g2,
        c: mock_g16_vk3.alpha_g1,
    };

    c.bench_function(
        "Prove satisfiability of 3 Groth16 verification equations using Groth-Sahai",
        |bench| {
            bench.iter(|| {
                let _ = prove_canon_g16_equations(
                    &[
                        (&mock_g16_pf1, &mock_g16_vk1, &mock_prepared_public_input1),
                        (&mock_g16_pf2, &mock_g16_vk2, &mock_prepared_public_input2),
                        (&mock_g16_pf3, &mock_g16_vk3, &mock_prepared_public_input3),
                    ],
                    &crs,
                    &mut rng,
                );
            });
        },
    );
}

fn bench_gs_over_groth16_three_verify(c: &mut Criterion) {
    let mut rng = test_rng();
    let crs = GS_CRS::<F>::generate_crs(&mut rng);

    // NOTE: This is a mock Groth16 setup to make the underlying equation trivially satisfiable.
    let mock_beta_g2_vk1 = G2Projective::rand(&mut rng).into_affine();
    let mock_beta_g2_vk2 = G2Projective::rand(&mut rng).into_affine();
    let mock_beta_g2_vk3 = G2Projective::rand(&mut rng).into_affine();
    let mock_g16_vk1: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2_vk1,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2_vk1,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_g16_vk2: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2_vk2,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2_vk2,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_g16_vk3: VerifyingKey<F> = VerifyingKey::<F> {
        alpha_g1: G1Projective::rand(&mut rng).into_affine(),
        beta_g2: mock_beta_g2_vk3,
        gamma_g2: G2Projective::rand(&mut rng).into_affine(),
        delta_g2: -mock_beta_g2_vk3,
        gamma_abc_g1: vec![
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
            G1Projective::rand(&mut rng).into_affine(),
        ],
    };
    let mock_prepared_public_input1 = G1Projective::rand(&mut rng);
    let mock_prepared_public_input2 = G1Projective::rand(&mut rng);
    let mock_prepared_public_input3 = G1Projective::rand(&mut rng);
    let mock_g16_pf1: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input1.into_affine(),
        b: mock_g16_vk1.gamma_g2,
        c: mock_g16_vk1.alpha_g1,
    };
    let mock_g16_pf2: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input2.into_affine(),
        b: mock_g16_vk2.gamma_g2,
        c: mock_g16_vk2.alpha_g1,
    };
    let mock_g16_pf3: Proof<F> = Proof::<F> {
        a: mock_prepared_public_input3.into_affine(),
        b: mock_g16_vk3.gamma_g2,
        c: mock_g16_vk3.alpha_g1,
    };
    let (xcoms, ycoms, gs_proofs) = prove_canon_g16_equations(
        &[
            (&mock_g16_pf1, &mock_g16_vk1, &mock_prepared_public_input1),
            (&mock_g16_pf2, &mock_g16_vk2, &mock_prepared_public_input2),
            (&mock_g16_pf3, &mock_g16_vk3, &mock_prepared_public_input3),
        ],
        &crs,
        &mut rng,
    );

    c.bench_function(
        "Verify satisfiability of 3 Groth16 verification equations using Groth-Sahai",
        |bench| {
            bench.iter(|| {
                let _ = verify_canon_g16_equations::<F>(
                    &[
                        (&mock_g16_vk1, &mock_prepared_public_input1),
                        (&mock_g16_vk2, &mock_prepared_public_input2),
                        (&mock_g16_vk3, &mock_prepared_public_input3),
                    ],
                    (&xcoms, &ycoms, &gs_proofs),
                    &crs,
                );
            });
        },
    );
}

criterion_group! {
    name = gs_over_groth16;
    config = Criterion::default().sample_size(10);
    targets =
        bench_gs_over_groth16_one_prove,
        bench_gs_over_groth16_one_verify,
        bench_gs_over_groth16_three_prove,
        bench_gs_over_groth16_three_verify,
}

criterion_main!(gs_over_groth16);
