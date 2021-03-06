//! **NOTE**: The Groth-Sahai CRS is meant to be generated as a part of trusted setup or trusted
//! computation. So, to avoid facilitating a dishonest prover in these wrappers,
//! CRS generation is left up to the user.
//! See [groth_sahai::generator](https://github.com/jdwhite88/groth-sahai-rs/blob/main/src/generator.rs) for more details.

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, PrimeField, Zero};
use ark_groth16::{Proof, VerifyingKey};
use ark_std::rand::{CryptoRng, Rng};

use core::ops::AddAssign;

use groth_sahai::prover::{batch_commit_G1, batch_commit_G2, Commit1, Commit2, EquProof, Provable};
use groth_sahai::statement::PPE;
use groth_sahai::verifier::Verifiable;
use groth_sahai::{Matrix, CRS as GS_CRS};

/// Prove that a list of canonical Groth16 verification equations are all satisfied by the provided
/// `Proof`.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
pub fn prove_canon_g16_equations<R, E>(
    g16_pf_elems: &[(&Proof<E>, &VerifyingKey<E>, &E::G1Projective)],
    gs_crs: &GS_CRS<E>,
    rng: &mut R,
) -> (Commit1<E>, Commit2<E>, Vec<EquProof<E>>)
where
    R: Rng + CryptoRng,
    E: PairingEngine,
{
    let num_equ = g16_pf_elems.len();

    // TODO: destructure tuple vector in a saner way
    // Construct the GS statement, i.e. Groth16 verification equations
    let g16_ver_equs = prepare_canon_g16_equations::<E>(
        &g16_pf_elems
            .iter()
            .map(|(_, vk, pub_input)| (*vk, *pub_input))
            .collect::<Vec<_>>(),
    );

    // X = [ ..., A_p, C_p, ... ]
    let m = 2 * num_equ;
    let mut xvars: Vec<E::G1Affine> = Vec::with_capacity(m);
    for (pf, _, _) in g16_pf_elems.iter() {
        xvars.append(&mut vec![pf.a, pf.c]);
    }
    // Y = [ ..., B_p, ... ]
    let yvars: Vec<E::G2Affine> = g16_pf_elems
        .iter()
        .map(|(pf, _, _)| pf.b)
        .collect::<Vec<E::G2Affine>>();
    // Commit to these variables in GS
    let xcoms: Commit1<E> = batch_commit_G1(&xvars, gs_crs, rng);
    let ycoms: Commit2<E> = batch_commit_G2(&yvars, gs_crs, rng);

    (
        xcoms.clone(),
        ycoms.clone(),
        g16_ver_equs
            .iter()
            .map(|equ| equ.prove(&xvars, &yvars, &xcoms, &ycoms, gs_crs, rng))
            .collect::<Vec<EquProof<E>>>(),
    )
}

/// Prove that a list of linked Groth16 verification equations are all satisfied by the provided
/// `Proof`.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=k}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]` and the `k` linked
/// inputs `a_0, a_1, ..., a_{k-1}` are provided as input.
pub fn prove_linked_g16_equations<R, E>(
    g16_pf_elems: &[(&Proof<E>, &VerifyingKey<E>, &E::G1Projective)],
    g16_linked_inputs: &[E::Fr],
    gs_crs: &GS_CRS<E>,
    rng: &mut R,
) -> (Commit1<E>, Commit2<E>, Vec<EquProof<E>>)
where
    R: Rng + CryptoRng,
    E: PairingEngine,
{
    let num_equ = g16_pf_elems.len();

    // TODO: destructure tuple vector in a saner way
    // Construct the GS statement, i.e. Groth16 verification equations
    let g16_ver_equs = prepare_linked_g16_equations::<E>(
        &g16_pf_elems
            .iter()
            .map(|(_, vk, pub_input)| (*vk, *pub_input))
            .collect::<Vec<_>>(),
    );

    // X = [ ..., A_p, C_p, S_p, ... ]
    let m = 3 * num_equ;
    let mut xvars: Vec<E::G1Affine> = Vec::with_capacity(m);
    for (pf, vk, _) in g16_pf_elems.iter() {
        assert!(g16_linked_inputs.len() + 1 <= vk.gamma_abc_g1.len());

        // Compute sum from i=0 to k-1 of a_p,i W_p,i (skipping first element in vk)
        let mut s_link_var = E::G1Projective::zero();
        for (i, ai) in g16_linked_inputs.iter().enumerate() {
            s_link_var.add_assign(&vk.gamma_abc_g1[i + 1].mul(ai.into_repr()));
        }
        xvars.append(&mut vec![pf.a, pf.c, s_link_var.into_affine()]);
    }
    // Y = [ ..., B_p, ... ]
    let yvars: Vec<E::G2Affine> = g16_pf_elems.iter().map(|(pf, _, _)| pf.b).collect();
    // Commit to these variables in GS
    let xcoms: Commit1<E> = batch_commit_G1(&xvars, gs_crs, rng);
    let ycoms: Commit2<E> = batch_commit_G2(&yvars, gs_crs, rng);

    (
        xcoms.clone(),
        ycoms.clone(),
        g16_ver_equs
            .iter()
            .map(|equ| equ.prove(&xvars, &yvars, &xcoms, &ycoms, gs_crs, rng))
            .collect(),
    )
}

/// Verify that a list of canonical Groth16 verification equations are all satisfied by the Groth-Sahai
/// `EquProof`.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
#[must_use]
pub fn verify_canon_g16_equations<E: PairingEngine>(
    g16_ver_elems: &[(&VerifyingKey<E>, &E::G1Projective)],
    gs_proofs: (&Commit1<E>, &Commit2<E>, &Vec<EquProof<E>>),
    gs_crs: &GS_CRS<E>,
) -> bool {
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
        let verifies: bool = g16_equ.verify(gs_pf, gs_xcoms, gs_ycoms, gs_crs);
        if !verifies {
            return false;
        }
    }
    // Don't allow an empty or trivial proof to verify. Otherwise, if it's proceeded to this point,
    // all GS-over-Groth16 equations successfully satisfied
    !g16_ver_equs.is_empty() && !gs_proofs.2.is_empty()
}

/// Verify that a list of linked Groth16 verification equations are all satisfied by the Groth-Sahai
/// `EquProof`.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=k}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
#[must_use]
pub fn verify_linked_g16_equations<E: PairingEngine>(
    g16_ver_elems: &[(&VerifyingKey<E>, &E::G1Projective)],
    gs_proofs: (&Commit1<E>, &Commit2<E>, &Vec<EquProof<E>>),
    gs_crs: &GS_CRS<E>,
) -> bool {
    let num_equ = g16_ver_elems.len();
    if gs_proofs.2.len() != num_equ {
        return false;
    }

    // Reconstruct the GS statement (i.e. equations) the prover should have used
    let g16_ver_equs: Vec<PPE<E>> = prepare_linked_g16_equations::<E>(g16_ver_elems);
    if g16_ver_equs.len() != num_equ {
        return false;
    }

    let gs_xcoms: &Commit1<E> = gs_proofs.0;
    let gs_ycoms: &Commit2<E> = gs_proofs.1;
    for (i, g16_equ) in g16_ver_equs.iter().enumerate() {
        let gs_pf: &EquProof<E> = &gs_proofs.2[i];
        let verifies: bool = g16_equ.verify(gs_pf, gs_xcoms, gs_ycoms, gs_crs);
        if !verifies {
            return false;
        }
    }
    // Don't allow an empty or trivial proof to verify. Otherwise, if it's proceeded to this point,
    // all GS-over-Groth16 equations successfully satisfied.
    !g16_ver_equs.is_empty() && !gs_proofs.2.is_empty()
}

/// Expressed in the form of a GS statement, a canonical Groth16 verification equation has the form:
/// `e( C, -vk.delta_g2 ) * e(A, B) = e( vk.alpha_g1, vk.beta_g2 ) * e( prepared_pub_input,
/// vk.gamma_g2 )` where (A,B,C) are the Groth16 proof elements / GS witness variables, and the
/// rest are public constants.
///
/// The G1 element, `prepared_pub_input`, is expected to be `Σ_{i=0}^{\ell [p]} a_p,i W_p,i`
/// where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]`.
pub fn prepare_canon_g16_equations<E: PairingEngine>(
    g16_elems: &[(&VerifyingKey<E>, &E::G1Projective)],
) -> Vec<PPE<E>> {
    let num_equ = g16_elems.len();
    // The number of G1 variables: A, C in `Proof`
    let m = 2 * num_equ;
    // The number of G2 variables: B in `Proof`
    let n = num_equ;

    let mut gs_equs: Vec<PPE<E>> = Vec::with_capacity(num_equ);

    for (p, (vk, pub_input)) in g16_elems.iter().enumerate() {
        // `m` x `n` matrix defining how the variables `X = [..., A_p, C_p, ...]`, `Y = [..., B_p, ...]` are paired
        let mut gs_gamma: Matrix<E::Fr> = Vec::with_capacity(m);

        // not paired with previous equations' variables
        for _ in 0..p {
            gs_gamma.push(vec![E::Fr::zero(); n]);
            gs_gamma.push(vec![E::Fr::zero(); n]);
        }

        // Add a 1 at (2p, p) corresponding to the variable pairing e(A_p, B_p) in equation
        let mut ab_row = vec![E::Fr::zero(); n];
        ab_row[p] = E::Fr::one();
        gs_gamma.push(ab_row);
        gs_gamma.push(vec![E::Fr::zero(); n]);

        // not paired with next equations' variables
        for _ in (p + 1)..num_equ {
            gs_gamma.push(vec![E::Fr::zero(); n]);
            gs_gamma.push(vec![E::Fr::zero(); n]);
        }
        assert_eq!(gs_gamma.len(), m);
        assert_eq!(gs_gamma[0].len(), n);

        // Constants paired with none of the `n` variables in `G2`
        let gs_a_consts: Vec<E::G1Affine> = vec![E::G1Affine::zero(); n];
        // Constants paired with only second variable associated with each equation, i.e. e(C_p, - vk[p].delta_g2)
        let mut gs_b_consts: Vec<E::G2Affine> = vec![E::G2Affine::zero(); m];
        gs_b_consts[2 * p + 1] = -vk.delta_g2;

        let gs_rhs: E::Fqk = E::pairing::<E::G1Affine, E::G2Affine>(vk.alpha_g1, vk.beta_g2)
            * E::pairing::<E::G1Affine, E::G2Affine>(pub_input.into_affine(), vk.gamma_g2);

        // Add the `p`th Groth16 verification equation to the list of Groth-Sahai equations
        gs_equs.push(PPE::<E> {
            a_consts: gs_a_consts,
            b_consts: gs_b_consts,
            gamma: gs_gamma,
            target: gs_rhs,
        });
    }

    gs_equs
}

/// Expressed in the form of a GS statement, a linked Groth16 verification equation has the form:
/// `e( C, -vk.delta ) * e( S, -vk.gamma ) * e(A, B) =
/// = e( vk.alpha, vk.beta ) * e( prepared_pub_input, vk.gamma_g2 )`
/// where (A,B,C) are the Groth16 proof elements and are GS witness variables along with
/// `linked_inputs`, and the rest are public constants.
///
/// Given `k` linked inputs `a_0, ..., a_{k-1}`, the linked inputs become the GS variable `S = Σ_{i=0}^{k-1} a_p,i W_p,i`.
/// Furthermore, `prepared_pub_input` is expected to incorporate the remaining Groth16 (canonically) public inputs as
/// `Σ_{i=k}^{\ell [p]} a_p,i W_p,i`, where `W_p,i` corresponds to the `p`th `VerifyingKey`'s `gamma_abc_g1[i]` in both.
pub fn prepare_linked_g16_equations<E: PairingEngine>(
    g16_elems: &[(&VerifyingKey<E>, &E::G1Projective)],
) -> Vec<PPE<E>> {
    let num_equ = g16_elems.len();
    // The number of G1 variables: A, C, S in `Proof`
    let m = 3 * num_equ;
    // The number of G2 variables: B in `Proof`
    let n = num_equ;

    let mut gs_equs: Vec<PPE<E>> = Vec::with_capacity(num_equ);

    for (p, (vk, pub_input)) in g16_elems.iter().enumerate() {
        // `m` x `n` matrix defining how the variables `X = [..., A_p, C_p, S_p, ...]`, `Y = [..., B_p, ...]` are paired
        let mut gs_gamma: Matrix<E::Fr> = Vec::with_capacity(m);

        // not paired with previous equations' variables
        for _ in 0..p {
            gs_gamma.push(vec![E::Fr::zero(); n]);
            gs_gamma.push(vec![E::Fr::zero(); n]);
            gs_gamma.push(vec![E::Fr::zero(); n]);
        }

        // Add a 1 at (3p, p) corresponding to the variable pairing e(A_p, B_p) in equation
        let mut ab_row = vec![E::Fr::zero(); n];
        ab_row[p] = E::Fr::one();
        gs_gamma.push(ab_row);
        gs_gamma.push(vec![E::Fr::zero(); n]);
        gs_gamma.push(vec![E::Fr::zero(); n]);

        // not paired with next equations' variables
        for _ in (p + 1)..num_equ {
            gs_gamma.push(vec![E::Fr::zero(); n]);
            gs_gamma.push(vec![E::Fr::zero(); n]);
            gs_gamma.push(vec![E::Fr::zero(); n]);
        }
        assert_eq!(gs_gamma.len(), m);
        assert_eq!(gs_gamma[0].len(), n);

        // Constants paired with none of the `n` variables in `G2`
        let gs_a_consts: Vec<E::G1Affine> = vec![E::G1Affine::zero(); n];
        // Constants paired with e(C_p, - vk[p].delta_g2) * e(S_p, - vk[p].gamma_g2)
        let mut gs_b_consts: Vec<E::G2Affine> = vec![E::G2Affine::zero(); m];
        gs_b_consts[3 * p + 1] = -vk.delta_g2;
        gs_b_consts[3 * p + 2] = -vk.gamma_g2;

        let gs_rhs: E::Fqk = E::pairing::<E::G1Affine, E::G2Affine>(vk.alpha_g1, vk.beta_g2)
            * E::pairing::<E::G1Affine, E::G2Affine>(pub_input.into_affine(), vk.gamma_g2);

        // Add the `p`th Groth16 verification equation to the list of Groth-Sahai equations
        gs_equs.push(PPE::<E> {
            a_consts: gs_a_consts,
            b_consts: gs_b_consts,
            gamma: gs_gamma,
            target: gs_rhs,
        });
    }

    gs_equs
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_bls12_381::Bls12_381 as F;
    use ark_crypto_primitives::prf::{
        blake2s::{constraints::Blake2sGadget, Blake2s},
        PRFGadget, PRF,
    };
    use ark_ec::PairingEngine;
    use ark_ff::{BigInteger, Field, PrimeField};
    use ark_groth16::{Proof as Groth16Proof, ProvingKey as Groth16ProvingKey};
    use ark_r1cs_std::{
        alloc::AllocVar, bits::ToBytesGadget, eq::EqGadget, fields::fp::FpVar, uint8::UInt8,
    };
    use ark_relations::{
        ns,
        r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, ToConstraintField},
    };
    use groth_sahai::{AbstractCrs, CRS as GS_CRS};
    type Fr = <F as PairingEngine>::Fr;

    /// Depending on use_ki, this circuit will do one of three things:
    ///   If use_ki = 1 this circuit proves `H(domain_str, k1) = digest`, where
    ///     all variables are public input.
    ///   If use_ki = 2 this circuit proves `H(domain_str, k2) = digest`, where
    ///     all variables are public input.
    ///   If use_ki = 3 is set, this circuit proves `H(H(domain_str, k1), k2) = digest`, where
    ///     all variables are public input.
    /// Later, we will make `k1` and `k2` hidden by the Groth-Sahai proof.
    #[derive(Clone)]
    struct HashPreimageCircuit<ConstraintF: Field> {
        use_ki: usize,
        k1: ConstraintF,
        k2: ConstraintF,
        domain_str: [u8; 32],
        digest: [u8; 32],
    }

    impl<ConstraintF: PrimeField> ConstraintSynthesizer<ConstraintF>
        for HashPreimageCircuit<ConstraintF>
    {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<ConstraintF>,
        ) -> Result<(), SynthesisError> {
            // Get k1,k2 as PUBLIC input
            let k1 = FpVar::<ConstraintF>::new_input(ns!(cs, "preimage"), || Ok(self.k1))?;
            let k2 = FpVar::<ConstraintF>::new_input(ns!(cs, "preimage"), || Ok(self.k2))?;

            // Get the domain str and hash as well
            let domain_str: Vec<UInt8<ConstraintF>> =
                UInt8::new_input_vec(ns!(cs, "domain_str"), &self.domain_str)?;
            let expected_digest = UInt8::new_input_vec(ns!(cs, "digest"), &self.digest)?;

            let computed_digest = match self.use_ki {
                1 => {
                    // Compute `H(domain_str, k1)`
                    Blake2sGadget::evaluate(&domain_str, &k1.to_bytes()?)?
                }
                2 => {
                    // Compute `H(domain_str, k2)`
                    Blake2sGadget::evaluate(&domain_str, &k2.to_bytes()?)?
                }
                3 => {
                    // Compute `H(H(domain_str, k1), k2)`
                    let inner_digest = Blake2sGadget::evaluate(&domain_str, &k1.to_bytes()?)?;
                    Blake2sGadget::evaluate(&inner_digest.0, &k2.to_bytes()?)?
                }
                _ => panic!("use_ki must be 1, 2, or 3"),
            };
            // Enforce that the provided digest equals the computed one
            expected_digest.enforce_equal(&computed_digest.0)
        }
    }

    impl<ConstraintF: PrimeField> HashPreimageCircuit<ConstraintF> {
        /// Generates a proving key for this circuit for a specific choice of use_ki
        fn gen_crs<E, R>(rng: &mut R, use_ki: usize) -> Groth16ProvingKey<E>
        where
            E: PairingEngine<Fr = ConstraintF>,
            R: Rng,
        {
            let placeholder_bytes = *b"XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX";
            let placeholder_circuit = HashPreimageCircuit {
                use_ki,
                k1: E::Fr::zero(),
                k2: E::Fr::zero(),
                domain_str: placeholder_bytes,
                digest: placeholder_bytes,
            };
            ark_groth16::generate_random_parameters::<E, _, _>(placeholder_circuit, rng).unwrap()
        }

        /// Proves this circuit with the given inputs. Returns the serialized public inputs and the
        /// Groth16 proof.
        fn prove<E, R>(
            rng: &mut R,
            pk: &Groth16ProvingKey<E>,
            use_ki: usize,
            k1: E::Fr,
            k2: E::Fr,
            domain_str: [u8; 32],
        ) -> (Vec<ConstraintF>, Groth16Proof<E>)
        where
            E: PairingEngine<Fr = ConstraintF>,
            R: Rng,
        {
            // Compute the digest we need to prove
            let mut k1_bytes = [0u8; 32];
            let mut k2_bytes = [0u8; 32];
            k1_bytes.copy_from_slice(&k1.into_repr().to_bytes_le());
            k2_bytes.copy_from_slice(&k2.into_repr().to_bytes_le());
            let digest = match use_ki {
                1 => {
                    // H(domain_str, k1)
                    Blake2s::evaluate(&domain_str, &k1_bytes).unwrap()
                }
                2 => {
                    // H(domain_str, k2)
                    Blake2s::evaluate(&domain_str, &k2_bytes).unwrap()
                }
                3 => {
                    // H(H(domain_str, k1), k2)
                    let inner_digest = Blake2s::evaluate(&domain_str, &k1_bytes).unwrap();
                    Blake2s::evaluate(&inner_digest, &k2_bytes).unwrap()
                }
                _ => {
                    panic!("use_ki must be 1, 2, or 3");
                }
            };

            // Make the circuit and prove it
            let circuit = HashPreimageCircuit {
                use_ki,
                k1,
                k2,
                domain_str,
                digest,
            };
            let proof = ark_groth16::create_random_proof::<E, _, _>(circuit, pk, rng).unwrap();

            // Serialize all the public inputs
            let public_inputs = [
                k1.to_field_elements().unwrap(),
                k2.to_field_elements().unwrap(),
                domain_str.to_field_elements().unwrap(),
                digest.to_field_elements().unwrap(),
            ]
            .concat();

            (public_inputs, proof)
        }
    }

    /// We test the preimage circuit here
    #[test]
    fn test_preimage_circuit_correctness() {
        let mut rng = ark_std::test_rng();

        // Set the parameters of this circuit. Do the full double-hash, i.e., use_ki = 3
        let use_ki = 3;
        let domain_str = *b"goodbye my coney island babyyyyy";
        let k1 = Fr::from(1337u32);
        let k2 = Fr::from(0xdeadbeefu32);

        // Generate the CRS and then prove on the above parameters
        let pk = HashPreimageCircuit::gen_crs::<F, _>(&mut rng, use_ki);
        let (public_inputs, proof) =
            HashPreimageCircuit::prove(&mut rng, &pk, use_ki, k1, k2, domain_str);

        // Now verify the proof
        let pvk = ark_groth16::prepare_verifying_key(&pk.vk);
        assert!(ark_groth16::verify_proof(&pvk, &proof, &public_inputs).unwrap());
    }

    /// In this test we make three circuits. One computes `H(domain_str1, k1)`. One computes
    /// `H(H(domain_str2, k1), k2)`. One computes `H(domain_str1, k2)`. We then prove that all of
    /// these circuits share the same `k1,k2`.
    #[test]
    fn test_preimage_circuit_linkage() {
        let mut rng = ark_std::test_rng();

        // Set the parameters of this circuit
        let k1 = Fr::from(1337u32);
        let k2 = Fr::from(0xdeadbeefu32);
        let domain_str1 = *b"goodbye my coney island babyyyyy";
        let domain_str2 = *b"goodbye my one true loveeeeeeeee";

        // Generate the CRSs and then prove on the above parameters. single1 is the circuit that
        // computes `H(domain_str1, k1)`. single2 computes `H(domain_str1, k2)`. double computes
        // `H(H(domain_str2, k1), k2)`.
        let pk_single1 = HashPreimageCircuit::gen_crs::<F, _>(&mut rng, 1);
        let pk_single2 = HashPreimageCircuit::gen_crs::<F, _>(&mut rng, 2);
        let pk_double = HashPreimageCircuit::gen_crs::<F, _>(&mut rng, 3);
        let (mut public_inputs_single1, proof_single1) =
            HashPreimageCircuit::prove(&mut rng, &pk_single1, 1, k1, k2, domain_str1);
        let (mut public_inputs_single2, proof_single2) =
            HashPreimageCircuit::prove(&mut rng, &pk_single2, 2, k1, k2, domain_str1);
        let (mut public_inputs_double, proof_double) =
            HashPreimageCircuit::prove(&mut rng, &pk_double, 3, k1, k2, domain_str2);

        // Verify the proofs
        let pvk_single1 = ark_groth16::prepare_verifying_key(&pk_single1.vk);
        let pvk_single2 = ark_groth16::prepare_verifying_key(&pk_single2.vk);
        let pvk_double = ark_groth16::prepare_verifying_key(&pk_double.vk);
        assert!(
            ark_groth16::verify_proof(&pvk_single1, &proof_single1, &public_inputs_single1)
                .unwrap()
        );
        assert!(
            ark_groth16::verify_proof(&pvk_single2, &proof_single2, &public_inputs_single2)
                .unwrap()
        );
        assert!(
            ark_groth16::verify_proof(&pvk_double, &proof_double, &public_inputs_double).unwrap()
        );

        // Now do a GS-over-canon-Groth16 and verify that. This does not hide k1 or k2
        let crs = GS_CRS::<F>::generate_crs(&mut rng);
        let prepared_input_single1 =
            ark_groth16::prepare_inputs(&pvk_single1, &public_inputs_single1).unwrap();
        let prepared_input_single2 =
            ark_groth16::prepare_inputs(&pvk_single2, &public_inputs_single2).unwrap();
        let prepared_input_double =
            ark_groth16::prepare_inputs(&pvk_double, &public_inputs_double).unwrap();
        let (xcoms, ycoms, gs_proofs) = prove_canon_g16_equations(
            &[
                (&proof_single1, &pk_single1.vk, &prepared_input_single1),
                (&proof_single2, &pk_single2.vk, &prepared_input_single2),
                (&proof_double, &pk_double.vk, &prepared_input_double),
            ],
            &crs,
            &mut rng,
        );
        assert!(verify_canon_g16_equations::<F>(
            &[
                (&pk_single1.vk, &prepared_input_single1),
                (&pk_single2.vk, &prepared_input_single2),
                (&pk_double.vk, &prepared_input_double)
            ],
            (&xcoms, &ycoms, &gs_proofs),
            &crs
        ));

        // Now link the proofs along the hidden `k1,k2`. Prepare the inputs excluding `k1,k2`. We
        // exclude `k1,k2` by setting them to 0 (this works because input preparation is just Σ
        // aᵢWᵢ where aᵢ are the inputs and Wᵢ are the group elements representing input wires)
        public_inputs_single1[0] = Fr::zero();
        public_inputs_single1[1] = Fr::zero();
        public_inputs_single2[0] = Fr::zero();
        public_inputs_single2[1] = Fr::zero();
        public_inputs_double[0] = Fr::zero();
        public_inputs_double[1] = Fr::zero();
        let prepared_input_single1 =
            ark_groth16::prepare_inputs(&pvk_single1, &public_inputs_single1).unwrap();
        let prepared_input_single2 =
            ark_groth16::prepare_inputs(&pvk_single2, &public_inputs_single2).unwrap();
        let prepared_input_double =
            ark_groth16::prepare_inputs(&pvk_double, &public_inputs_double).unwrap();

        // Do a linking G-S proof along k1, k2
        let crs = GS_CRS::<F>::generate_crs(&mut rng);
        let (xcoms, ycoms, gs_proofs) = prove_linked_g16_equations(
            &[
                (&proof_single1, &pk_single1.vk, &prepared_input_single1),
                (&proof_single2, &pk_single2.vk, &prepared_input_single2),
                (&proof_double, &pk_double.vk, &prepared_input_double),
            ],
            &[k1, k2],
            &crs,
            &mut rng,
        );

        // Verify the linked proof
        assert!(verify_linked_g16_equations::<F>(
            &[
                (&pk_single1.vk, &prepared_input_single1),
                (&pk_single2.vk, &prepared_input_single2),
                (&pk_double.vk, &prepared_input_double)
            ],
            (&xcoms, &ycoms, &gs_proofs),
            &crs
        ));
    }
}
