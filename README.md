<h1 align="center">Groth-Sahai Wrappers</h1>
<p align="center">
    <a href="https://github.com/jdwhite88/groth-sahai-wrappers/blob/main/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/jdwhite88/groth-sahai-wrappers/blob/main/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/jdwhite88/groth-sahai-wrappers"><img src="https://deps.rs/repo/github/jdwhite88/groth-sahai-wrappers/status.svg"></a>
</p>

A Rust library containing wrappers that facilitate the construction of non-interactive witness-indistinguishable and zero-knowledge proofs about various equations over bilinear groups [[1]](https://eprint.iacr.org/eprint-bin/getfile.pl?entry=2007/155&version=20160411:065033&file=155.pdf). See the corresponding [Groth-Sahai library](https://github.com/jdwhite88/groth-sahai-rs/) for more details about how Groth-Sahai has been implemented.

This library is distributed under the MIT License and the Apache v2 License (see [License](#license)).

## ⚠ Disclaimer ⚠

* This library, including many dependencies it relies on, are academic proof-of-concepts only that have NOT been thoroughly reviewed for production use. **Do NOT use this implementation in production code.**
* **Your choice of bilinear group (G1, G2, GT, e) MUST be secure under the SXDH assumption**, must be equipped with a Type-III pairing, and must be implemented in Arkworks. For example, [Bls12_381](https://docs.rs/ark-bls12-381/0.3.0/ark_bls12_381/) is amenable to this implementation.

## Getting Started

### Installation

First, install the latest version of Rust using `rustup`:
```bash
rustup install stable
```
After that, use Rust's `cargo` to compile the library:
```bash
git clone https://github.com/jdwhite88/groth-sahai-wrappers.git
cd groth-sahai-wrappers
cargo build
```

### Test

To run the unit tests (in each source file) and integration tests (in `tests`):
```bash
cargo test
```
To run the benchmark tests (in `benches`):
```bash
cargo bench
```

## Supported Wrappers

* **[Groth16](https://github.com/arkworks-rs/groth16/)** -- For constructing variants of GS-over-Groth16 proofs, given a `Proof` and other components of the zk-SNARK's circuit [[3]](https://eprint.iacr.org/eprint-bin/getfile.pl?entry=2016/260&version=20160308:201152&file=260.pdf).

## Dependencies

* **[Groth-Sahai](https://github.com/jdwhite88/groth-sahai-rs/)** - An implementation of the Groth-Sahai proof system in Rust.
* **[Arkworks](https://github.com/arkworks-rs/)** - A Rust ecosystem for developing and programming with zkSNARKs as well as finite field and elliptic curve arithmetic.


## Contributing

If you notice a bug, would like to ask a question, or want to propose a new wrapper, feel free to open an issue!

If you would like to contribute, but have not been invited as a direct collaborator to the project, follow the procedure below (keeping in mind [these instructions](https://docs.github.com/en/issues/tracking-your-work-with-issues/linking-a-pull-request-to-an-issue) if you are attempting to resolve an open issue):

1. Fork the project
3. Create your feature branch (`git checkout -b feature-branch main`)
4. Commit your changes (`git commit -m 'Resolves #i; commit message'`)
5. Push to the branch (`git push origin feature-branch`)
6. Open a pull request to merge with this repo (preferably linked to an issue)

## References

**[1]** Jens Groth and Amit Sahai. **Efficient Non-interactive Proof Systems for Bilinear Groups**, *Advances in Cryptology -- EUROCRYPT 2008: 27th Annual International Conference on the Theory and Applications of Cryptographic Techniques*, Istanbul, Turkey. Springer Berlin Heidelberg, vol 4965: 415–432, 2008.

**[2]** Essam Ghadafi, Nigel P. Smart, and Bogdan Warinschi. **Groth-Sahai proofs revisited**. In Phong Q. Nguyen and David Pointcheval, editors, *PKC 2010, volume 6056 of LNCS*, pages 177–192. Springer, Heidelberg, May 2010.

**[3]** Jens Groth. **On the size of pairing-based non-interactive arguments**. In Marc Fischlin and Jean-Sébastien Coron, editors, *EUROCRYPT 2016, Part II, volume 9666 of LNCS*, pages 305-326. Springer, Heidelberg, May 2016.

## License

 This library is distributed under either of the following licenses:
 
 * Apache License v2.0 ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT License ([LICENSE-MIT](LICENSE-MIT))
 
Unless explicitly stated otherwise, any contribution made to this library shall be dual-licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.

## Authors

* Jacob White - white570@purdue.edu
