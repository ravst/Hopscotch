# GameHoppingInLean

The goal of this project is to implement a game hopping framework in Lean.
We are inspired by the tool ProofFrog, and we try to combine ProofFrog's
intuitive user interface, with Lean's correctness guarantees and flexibility.

The project is being developed using the LLM-based tool Codex from OpenAI and Aristotle from harmonic.

## Documentation
 Documentation for how to use this project can be found in [game-hopping-intro/SKILL.md](game-hopping-intro/SKILL.md).

## Internal Structure
 Below we describe content of various directories:
  * **Comp**: Computational layer. Definition of oracle implementation, reduction, composition of reduction with implementation.
  * **ObservationalEq**: Definition of observational equality (ObsEq). Definition of abstraction technique (used to prove ObsEq). Proof of correctness of abstraction.
  * **Indistinguishability**: Definition of `IndistinguishabilityI`: type of indistinguishability proof.
  * **ComputationalIndistinguishibility**: Definition and proof of soundness theorem. Definition of computational semantics (adversarial advantage).
  * **Tactic**: Useful tactics. 

## Dependencies

This project depends on the VCVio library.

## References

[1] Shoup, V. "Sequences of games: a tool for taming complexity in security proofs." (https://eprint.iacr.org/2004/332)

[2] Evans, R., McKague, M., & Stebila, D. (2025). ProofFrog: A Tool For Verifying Game-Hopping Proofs. Cryptology ePrint Archive. (https://eprint.iacr.org/2025/418)

[3] Tuma, D., & Hopper, N. (2024). VCVio: A Formally Verified Forking Lemma and Fiat-Shamir Transform, via a Flexible and Expressive Oracle Representation. Cryptology ePrint Archive. (https://eprint.iacr.org/2024/1819).
