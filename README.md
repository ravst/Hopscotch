# HOPSCOTCH

HOPSCOTCH is a framework for formalizing game-hopping proofs in Lean. It is a
joint project by S. Dziembowski, G. Fabiański, D. Micciancio, and R. Stefański.
A preprint of an accompanying paper will shortly be available online.

The goal of the framework is to facilitate the formalization of cryptographic proofs
structured as sequences of games, also known as game-hopping or state-separation
proofs [1]. This proof style is employed throughout the textbook [4]. ProofFrog [2]
provides a purpose-built, standalone tool for verifying such proofs. HOPSCOTCH
aims to bring a similarly intuitive proof style into Lean, combining it with the
correctness guarantees and flexibility of a general-purpose theorem prover. It
provides definitions and tactics for oracle implementations, observational
equivalence, reductions, sequences of hybrid games, and computational
indistinguishability.

The project is being developed with assistance from the LLM-based tools Codex from
OpenAI and Aristotle from Harmonic.

## Project status

HOPSCOTCH is an active, experimental research project.
Its APIs and tactics may change as the framework develops. The
repository includes complete examples covering PRGs, PRFs, symmetric and public-key encryption, MACs, GGM, and ElGamal.

The project currently builds without `sorry` declarations in active code.

## Requirements

The current version of the project requires Lean `v4.28.0`.
Apart from Mathlib (commit `8f9d9cff`), its main dependency is VCVio (commit `e7f4c8d`).

## Building (verifying)

Clone the repository and build it with Lake:

```bash
git clone https://github.com/ravst/Hopscotch.git
cd Hopscotch
lake build
```

## Using the library

In a typical proof:

1. Define the two oracle implementations that should be indistinguishable,
   and a number of oracle implementations that are assumed to be indistinguishable.
2. Express the proof as a sequence of oracle implementations.
3. Prove adjacent games equivalent using observational equivalence or a reduction to
   an indistinguishability assumption.
4. Assemble the sequence with the `game_hopping` tactic.

The example directory provides a few examples:

- [`Examples/SecurityDefinitions`](Hopscotch/Examples/SecurityDefinitions)
  contains examples of oracle implementations (that will be either proven or assumed indistinguishable).
- [`Examples/Proofs`](Hopscotch/Examples/Proofs) contains complete
  game-hopping proofs.

## Repository structure

- **Comp**: Computational layer, including oracle implementations, reductions, and
  composition of reductions with implementations.
- **ObservationalEq**: Observational equivalence (`ObsEq`) and the abstraction
  technique used to prove it.
- **Indistinguishability**: The `IndistinguishableI` proof type and assumptions.
- **ComputationalIndistinguishability**: Computational semantics, adversarial
  advantage, and the soundness theorem.
- **Tactic**: Tactics and simplification infrastructure used in game-hopping proofs.
- **Examples**: Security definitions, constructions, and complete proofs.

## License

This project is available under the [MIT License](LICENSE).

## References

1. V. Shoup, ["Sequences of Games: A Tool for Taming Complexity in Security
   Proofs"](https://eprint.iacr.org/2004/332), Cryptology ePrint Archive, 2004.
2. R. Evans, M. McKague, and D. Stebila, ["ProofFrog: A Tool For Verifying
   Game-Hopping Proofs"](https://eprint.iacr.org/2025/418), Cryptology ePrint
   Archive, 2025.
3. D. Tuma and N. Hopper, ["VCVio: A Formally Verified Forking Lemma and
   Fiat-Shamir Transform, via a Flexible and Expressive Oracle
   Representation"](https://eprint.iacr.org/2024/1819), Cryptology ePrint Archive,
   2024.
4. M. Rosulek, [*The Joy of Cryptography: An Undergraduate Course in Provable
   Security*](https://joyofcryptography.com/), MIT Press, 2026.
