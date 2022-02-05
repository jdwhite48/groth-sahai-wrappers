//! **NOTE**: The Groth-Sahai CRS is meant to be generated as a part of trusted setup or trusted
//! computation. So, to avoid facilitating a dishonest prover in these wrappers,
//! CRS generation is left up to the user.
//! See [groth_sahai::generator](https://github.com/jdwhite88/groth-sahai-rs/blob/main/src/generator.rs) for more details.

use ark_ec::PairingEngine;
use ark_ff::{Zero, One};
use ark_groth16::{Proof, VerifyingKey};
use ark_std::rand::{CryptoRng, Rng};

use groth_sahai::{Matrix, CRS as GS_CRS};
use groth_sahai::statement::PPE;
use groth_sahai::prover::{Commit1, Commit2, EquProof, batch_commit_G1, batch_commit_G2, Provable};
use groth_sahai::verifier::Verifiable;

/// Prove that a list of canonical Groth16 verification equations are all satisfied by the provided
/// `Proof`.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
pub fn prove_canon_g16_equations<R, E>(g16_pf_elems: &Vec<(&Proof<E>, &VerifyingKey<E>, &E::G1Affine)>, gs_crs: &GS_CRS<E>, rng: &mut R) -> (Commit1<E>, Commit2<E>, Vec<EquProof<E>>)
where
    R: Rng + CryptoRng,
    E: PairingEngine
{

    let num_equ = g16_pf_elems.len();

    // TODO: destructure tuple vector in a saner way
    // Construct the GS statement, i.e. Groth16 verification equations
    let g16_ver_equs = prepare_canon_g16_equations::<E>(
        &g16_pf_elems.into_iter()
            .map(|(_, vk, pub_input)| (*vk, *pub_input))
            .collect::<Vec<(&VerifyingKey<E>, &E::G1Affine)>>()
    );

    // X = [ ..., A_p, C_p, ... ]
    let m = 2 * num_equ;
    let mut xvars: Vec<E::G1Affine> = Vec::with_capacity(m);
    for (_, (pf, _, _)) in g16_pf_elems.iter().enumerate() {
        xvars.append(&mut vec![pf.a, pf.c]);
    }
    // Y = [ ..., B_p, ... ]
    let _n = num_equ;
    let yvars: Vec<E::G2Affine> = g16_pf_elems.iter()
        .map(|(pf, _, _)| pf.b)
        .collect::<Vec<E::G2Affine>>();
    // Commit to these variables in GS
    let xcoms: Commit1<E> = batch_commit_G1(&xvars, gs_crs, rng);
    let ycoms: Commit2<E> = batch_commit_G2(&yvars, gs_crs, rng);

    (
        xcoms.clone(),
        ycoms.clone(),
        g16_ver_equs.iter().map(|equ|
            equ.prove(&xvars, &yvars, &xcoms, &ycoms, gs_crs, rng)
        ).collect::<Vec<EquProof<E>>>()
    )
}

/// Verify that a list of Groth16 verification equations are all satisfied by the Groth-Sahai
/// `EquProof`.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
pub fn verify_canon_g16_equations<E: PairingEngine>(
    g16_ver_elems: &Vec<(&VerifyingKey<E>, &E::G1Affine)>,
    gs_proofs: (&Commit1<E>, &Commit2<E>, &Vec<EquProof<E>>),
    gs_crs: &GS_CRS<E>) -> bool
{

    let num_equ = g16_ver_elems.len();
    if gs_proofs.2.len() != num_equ {
        return false;
    }

    // Reconstruct the GS statement (i.e. equations) the prover should have used
    let g16_ver_equs: Vec<PPE<E>> = prepare_canon_g16_equations::<E>(g16_ver_elems);
    if g16_ver_equs.len() != num_equ {
        return false;
    }

    let gs_xcoms: &Commit1<E> = gs_proofs.0;
    let gs_ycoms: &Commit2<E> = gs_proofs.1;
    for (i, g16_equ) in g16_ver_equs.iter().enumerate() {
        let gs_pf: &EquProof<E> = &gs_proofs.2[i];
        let verifies: bool = g16_equ.verify(&gs_pf, &gs_xcoms, &gs_ycoms, gs_crs);
        if !verifies {
            return false;
        }
    }
    // Don't allow an empty or trivial proof to verify
    if g16_ver_equs.len() == 0 || gs_proofs.2.len() == 0 {
        return false;
    }
    // If it's proceeded to this point, all GS-over-Groth16 equations successfully satisfied
    return true;
}

/// Expressed in the form of a GS statement, a canonical Groth16 verification equation has the form:
/// `e( C, -vk.delta_g2 ) * e(A, B) = e( vk.alpha_g1, vk.beta_g2 ) * e( prepared_pub_input,
/// vk.gamma_g2 )` where (A,B,C) are the Groth16 proof elements / GS witness variables, and the
/// rest are public constants.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
pub fn prepare_canon_g16_equations<E: PairingEngine>(g16_elems: &Vec<(&VerifyingKey<E>, &E::G1Affine)>) -> Vec<PPE<E>> {

    let num_equ = g16_elems.len();
    // The number of G1 variables: A, C in `Proof`
    let m = 2 * num_equ;
    // The number of G2 variables: B in `Proof`
    let n = num_equ;

    let mut gs_equs : Vec<PPE<E>> = Vec::with_capacity(num_equ);

    for (p, (vk, pub_input)) in g16_elems.iter().enumerate() {

        // `m` x `n` matrix defining how the variables `X = [..., A_p, C_p, ...]`, `Y = [..., B_p, ...]` are paired
        let mut gs_gamma: Matrix<E::Fr> = Vec::with_capacity(m);

        // not paired with previous equations' variables
        for _ in 0..p {
            gs_gamma.push(vec![ E::Fr::zero(); n ]);
            gs_gamma.push(vec![ E::Fr::zero(); n ]);
        } 

        // Add a 1 at (2p, p) corresponding to the variable pairing e(A_p, B_p) in equation
        let mut ab_row = vec![ E::Fr::zero(); n ];
        ab_row[p] = E::Fr::one();
        gs_gamma.push(ab_row);
        gs_gamma.push(vec![ E::Fr::zero(); n ]);

        // not paired with next equations' variables
        for _ in (p+1)..num_equ {
            gs_gamma.push(vec![ E::Fr::zero(); n ]);
            gs_gamma.push(vec![ E::Fr::zero(); n ]);
        }
        assert_eq!(gs_gamma.len(), m);
        assert_eq!(gs_gamma[0].len(), n);

        // Constants paired with none of the `n` variables in `G2`
        let gs_a_consts: Vec<E::G1Affine> = vec![ E::G1Affine::zero(); n ];
        // Constants paired with only second variable associated with each equation, i.e. e(C_p, - vk[p].delta_g2)
        let mut gs_b_consts: Vec<E::G2Affine> = vec![ E::G2Affine::zero(); m ];
        gs_b_consts[2*p+1] = - vk.delta_g2;

        let gs_rhs: E::Fqk = E::pairing::<E::G1Affine, E::G2Affine>(vk.alpha_g1, vk.beta_g2) * E::pairing::<E::G1Affine, E::G2Affine>(**pub_input, vk.gamma_g2);

        // Add the `p`th Groth16 verification equation to the list of Groth-Sahai equations
        gs_equs.push(PPE::<E>{
            a_consts: gs_a_consts,
            b_consts: gs_b_consts,
            gamma: gs_gamma,
            target: gs_rhs
        });
    }

    gs_equs
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use ark_bls12_381::{Bls12_381 as F};
    use ark_ec::{PairingEngine, ProjectiveCurve};
    use ark_ff::UniformRand;
    use ark_groth16::{Proof, VerifyingKey};
    use ark_std::test_rng;

    use groth_sahai::{CRS as GS_CRS, AbstractCrs};

    use crate::groth16::{prove_canon_g16_equations, verify_canon_g16_equations};

//    type G1Affine = <F as PairingEngine>::G1Affine;
//    type G2Affine = <F as PairingEngine>::G2Affine;
    type G1Projective = <F as PairingEngine>::G1Projective;
    type G2Projective = <F as PairingEngine>::G2Projective;

    #[test]
    // Tests well-formedness of Groth-Sahai representations of Groth16 equation structure ONLY. NOT an
    // end-to-end test with real Groth16 elements (TODO: complement or replace this with a proper Groth16 test)
    fn test_mock_GS_over_Groth16_verification() {

        let mut rng = test_rng();
        let crs = GS_CRS::<F>::generate_crs(&mut rng);

        // NOTE: This is a mock Groth16 setup to make the underlying equation trivially satisfiable.
        let mock_beta_g2 = G2Projective::rand(&mut rng).into_affine();
        let mock_g16_vk: VerifyingKey<F> = VerifyingKey::<F>{
            alpha_g1: G1Projective::rand(&mut rng).into_affine(),
            beta_g2: mock_beta_g2,
            gamma_g2: G2Projective::rand(&mut rng).into_affine(),
            delta_g2: - mock_beta_g2,
            gamma_abc_g1: vec![
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine()
            ]
        };
        let mock_prepared_public_input = G1Projective::rand(&mut rng).into_affine();
        let mock_g16_pf: Proof<F> = Proof::<F>{
            a: mock_prepared_public_input,
            b: mock_g16_vk.gamma_g2,
            c: mock_g16_vk.alpha_g1
        };
        let (xcoms, ycoms, gs_proofs) = prove_canon_g16_equations(&vec![(&mock_g16_pf, &mock_g16_vk, &mock_prepared_public_input)], &crs, &mut rng);
        assert!(verify_canon_g16_equations::<F>(&vec![(&mock_g16_vk, &mock_prepared_public_input)], (&xcoms, &ycoms, &gs_proofs), &crs));
    }

    #[test]
    // Tests well-formedness of GS representations of multiple Groth16 equations ONLY. NOT an
    // end-to-end test with real Groth16 elements (TODO: complement or replace this with a proper Groth16 test)
    fn test_mock_GS_over_Groth16_multi_verification() {

        let mut rng = test_rng();
        let crs = GS_CRS::<F>::generate_crs(&mut rng);

        // NOTE: This is a mock Groth16 setup to make the underlying equation trivially satisfiable.
        let mock_beta_g2_vk1 = G2Projective::rand(&mut rng).into_affine();
        let mock_beta_g2_vk2 = G2Projective::rand(&mut rng).into_affine();
        let mock_beta_g2_vk3 = G2Projective::rand(&mut rng).into_affine();
        let mock_g16_vk1: VerifyingKey<F> = VerifyingKey::<F>{
            alpha_g1: G1Projective::rand(&mut rng).into_affine(),
            beta_g2: mock_beta_g2_vk1,
            gamma_g2: G2Projective::rand(&mut rng).into_affine(),
            delta_g2: - mock_beta_g2_vk1,
            gamma_abc_g1: vec![
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine()
            ]
        };
        let mock_g16_vk2: VerifyingKey<F> = VerifyingKey::<F>{
            alpha_g1: G1Projective::rand(&mut rng).into_affine(),
            beta_g2: mock_beta_g2_vk2,
            gamma_g2: G2Projective::rand(&mut rng).into_affine(),
            delta_g2: - mock_beta_g2_vk2,
            gamma_abc_g1: vec![
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine()
            ]
        };
        let mock_g16_vk3: VerifyingKey<F> = VerifyingKey::<F>{
            alpha_g1: G1Projective::rand(&mut rng).into_affine(),
            beta_g2: mock_beta_g2_vk3,
            gamma_g2: G2Projective::rand(&mut rng).into_affine(),
            delta_g2: - mock_beta_g2_vk3,
            gamma_abc_g1: vec![
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine(),
                G1Projective::rand(&mut rng).into_affine()
            ]
        };
        let mock_prepared_public_input1 = G1Projective::rand(&mut rng).into_affine();
        let mock_prepared_public_input2 = G1Projective::rand(&mut rng).into_affine();
        let mock_prepared_public_input3 = G1Projective::rand(&mut rng).into_affine();
        let mock_g16_pf1: Proof<F> = Proof::<F>{
            a: mock_prepared_public_input1,
            b: mock_g16_vk1.gamma_g2,
            c: mock_g16_vk1.alpha_g1
        };
        let mock_g16_pf2: Proof<F> = Proof::<F>{
            a: mock_prepared_public_input2,
            b: mock_g16_vk2.gamma_g2,
            c: mock_g16_vk2.alpha_g1
        };
        let mock_g16_pf3: Proof<F> = Proof::<F>{
            a: mock_prepared_public_input3,
            b: mock_g16_vk3.gamma_g2,
            c: mock_g16_vk3.alpha_g1
        };
        let (xcoms, ycoms, gs_proofs) = prove_canon_g16_equations(&vec![
                                                                  (&mock_g16_pf1, &mock_g16_vk1, &mock_prepared_public_input1),
                                                                  (&mock_g16_pf2, &mock_g16_vk2, &mock_prepared_public_input2),
                                                                  (&mock_g16_pf3, &mock_g16_vk3, &mock_prepared_public_input3)
        ], &crs, &mut rng);
        assert!(verify_canon_g16_equations::<F>(&vec![
                                                (&mock_g16_vk1, &mock_prepared_public_input1),
                                                (&mock_g16_vk2, &mock_prepared_public_input2),
                                                (&mock_g16_vk3, &mock_prepared_public_input3)
        ], (&xcoms, &ycoms, &gs_proofs), &crs));
    }
}
