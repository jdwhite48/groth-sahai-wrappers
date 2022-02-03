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

/// Prove that a list of canonical Groth16 verification equations are all satisfied by the provided
/// `Proof`.
pub fn prove_canon_g16_equations<E, R>(g16_elems: &Vec<(Proof<E>, VerifyingKey<E>, E::G1Affine)>, gs_crs: &GS_CRS<E>, rng: &mut R) -> (Commit1<E>, Commit2<E>, Vec<EquProof<E>>)
where
    E: PairingEngine,
    R: Rng + CryptoRng
{

    let num_equ = g16_elems.len();
    let g16_ver_equs = prepare_canon_g16_equations::<E>(g16_elems);

    let m = 2 * num_equ;
    let mut xvars: Vec<E::G1Affine> = Vec::with_capacity(m);
    for (_, (pf, _, _)) in g16_elems.iter().enumerate() {
        xvars.append(&mut vec![pf.a, pf.c]);
    }
    let _n = num_equ;
    let yvars: Vec<E::G2Affine> = g16_elems.iter().map(|(pf, _, _)| pf.b)
        .collect::<Vec<E::G2Affine>>();
    let xcoms: Commit1<E> = batch_commit_G1(&xvars, gs_crs, rng);
    let ycoms: Commit2<E> = batch_commit_G2(&yvars, gs_crs, rng);

    (
        xcoms.clone(),
        ycoms.clone(),
        g16_ver_equs.iter().map(|equ| {
            equ.prove(&xvars, &yvars, &xcoms, &ycoms, gs_crs, rng)
        }).collect::<Vec<EquProof<E>>>()
    )
}

/// Expressed in the form of a GS statement, a canonical Groth16 verification equation has the form:
/// `e( C, -vk.delta_g2 ) * e(A, B) = e( vk.alpha_g1, vk.beta_g2 ) * e( prepared_pub_input,
/// vk.gamma_g2 )`.
///
/// The third element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
pub fn prepare_canon_g16_equations<E: PairingEngine>(g16_elems: &Vec<(Proof<E>, VerifyingKey<E>, E::G1Affine)>) -> Vec<PPE<E>> {

    let num_equ = g16_elems.len();
    // The number of G1 variables: A, C in `Proof`
    let m = 2 * num_equ;
    // The number of G2 variables: B in `Proof`
    let n = num_equ;

    let mut gs_equs : Vec<PPE<E>> = Vec::with_capacity(num_equ);

    for (p, (_, vk, pub_input)) in g16_elems.iter().enumerate() {

        // `m` x `n` matrix defining how the variables `X = [..., A_p, C_p, ...]`, `Y = [..., B_p, ...]`
        // are paired; add 1 at all (2p, p) corresponding to variable pairing e(A_p, B_p) in equation
        let mut gs_gamma: Matrix<E::Fr> = Vec::with_capacity(m);
        for _ in 0..p {
            gs_gamma.push(vec![ E::Fr::zero(); n ]);
            gs_gamma.push(vec![ E::Fr::zero(); n ]);
        } 

        let mut ab_row = vec![ E::Fr::zero(); n ];
        ab_row[p] = E::Fr::one();
        gs_gamma.push(ab_row);
        gs_gamma.push(vec![ E::Fr::zero(); n ]);

        for _ in p..num_equ {
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

        let gs_rhs: E::Fqk = E::pairing::<E::G1Affine, E::G2Affine>(vk.alpha_g1, vk.beta_g2) * E::pairing::<E::G1Affine, E::G2Affine>(*pub_input, vk.gamma_g2);

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
