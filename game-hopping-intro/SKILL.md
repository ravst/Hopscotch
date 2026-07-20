---
name: game-hopping-intro
description: Framework for writing cryptographic proofs using game-hopping
category: Proof Strategy
tags: [game-hopping, proofs, indistinguishability]
---

# Game-Hopping Proofs in Lean

This skill provides an introduction to writing cryptographic proofs using the game-hopping framework in Lean.

## Overview

To use this library, follow these steps:

1. **Formulate indistinguishability statement**: Formulate the cryptographic statement you want to prove as an indistinguishability (IND) statement: define two oracle implementations that no adversary can distinguish from each other. Also formulate all assumptions as indistinguishability assumptions (they have the same form: a pair of oracle implementations).
   
   For more information on defining oracle implementations, see the [oracle implementation reference](./references/oracle-implementation.md).

2. **Sequence of Hybrids**: Formulate the proof as a sequence of hybrids. Prove that each pair of consecutive hybrids are IND. For each pair, one of the following should hold:

   - **Behavioral Equivalence**: They induce the same distribution on outputs for any sequence of queries. Proofs are usually carried out via the abstraction technique. See [observational equivalence reference](./references/observational-equivalence.md).
   
   - **Reduction Step**: The left hybrid has the syntactic form of a reduction `r` applied to the left side of assumption `X`. The right hybrid is equal to the same reduction applied to the right side of the same assumption `X`. See [reductions reference](./references/reductions.md).

Use the `game_hopping` tactic to write sequence of hybrids.

## Key tactics
- **game_hopping** is used to create an IndistinguishableI proof from a sequence of hybrids.
- **by_abstraction** is used to create an IndistinguishableI proof by providing abstraction. It has variant **obs_eq_by_abstraction** that proves ObsEq.
- simp [X] where X is:
   - **sRState** - to simplify RState monad term to PMF monad.
   - **sStateT** - to unfold StateT.get/set/map
   - **sPMF** - to simplify term in PMF monad (result is still in PMF, never unfold PMF definitions!)
   - **sReduction** - simplify OracleImpl expressed as composition reduction \Diamond implementation.

## Key Concepts

- **Indistinguishability (IND)**: Two oracles cannot be distinguished by any adversary
- **Oracle Implementation**: Concrete definition of oracle behavior with state and queries
- **Hybrid**: An intermediate oracle implementation in the proof sequence
- **Abstraction**: A technique to prove observational equivalence
- **Reduction**: A structured way to transform one oracle implementation into another. They are involved when using an assumption in the proof.

## References

For detailed information on each component:

- [Oracle Implementation](./references/oracle-implementation.md) – How to define oracle specifications and implementations
- [Observational Equivalence](./references/observational-equivalence.md) – Techniques for proving behavioral equivalence
- [Reductions](./references/reductions.md) – Defining and composing oracle reductions
