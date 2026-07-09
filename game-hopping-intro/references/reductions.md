# Oracle Reductions Reference

## Definition

A reduction from specification `O₁` to `O₂` is an object of type `OracleReduction O₁ O₂`. It is a structure with:

### Fields

- **`stateType`** – the type of internal state kept by the reduction

- **`initialState : OracleComp (withPMFSpec O₁) stateType`** – distribution on initial state
  - During initialization, you can already make queries to `O₂`
  - That's why `initialState` is an `OracleComp` over `withPMFSpec O₁`

- **`queries : QueryImpl O₂ (OracleComp (withPMFAndStateSpec stateType O₁))`** – process queries
  - For each query `q : O₂.Domain`, return an `OracleComp` computation of type `O₂.Range q`
  - `OracleComp` is over `withPMFAndStateSpec stateType O₁`, allowing:
    - Access to state of type `stateType` via queries
    - Sample from `PMF` (via queries)
    - Query the oracle specified by `O₁`

## Key Difference from Oracle Implementations

- **Oracle implementations** (`OracleImpl`): Implement queries directly in `RState`
- **Reductions** (`OracleReduction`): Must sample randomness and access state via queries
  - This is necessary to reactively combine these operations

## Reduction Composition

Given:
- `R : OracleReduction O₁ O₂` (a reduction)
- `x : OracleImpl O₂` (an implementation)

You obtain a new implementation: `R.apply x : OracleImpl O₁`. Also written as shorthand: `R ◇ x`

## Use in Game-Hopping Proofs

Reductions appear in hybrid sequences as follows:

1. Analyze an implementation `A` and want to use assumption `H`
2. Rewrite `A` as a reduction `R` composed with `H.left`
3. Perform a hop to `R` composed with `H.right`

**Practical Tip**: Define the reduction after you have an explicit implementation of `A` (for example, by replacing some operation with a call to `H.left`).

* Proving Indistinguishability After Reduction  
After applying `game_hopping`, you typically must prove indistinguishability between `A` and `R ◇ x`. Usually you use `by_abstraction`.

* Abstraction Over Compositions  
The internal state space of `R ◇ x` is `R.stateType × x.stateType`. Define an abstraction between this product and `A.stateType`.

* Special Case: Unit State
When `x.stateType` is `Unit`, the abstraction is trivial. The `game_hopping` tactic automatically handles such cases.

* Simplifying Reductions
When proving correct abstraction, a "diagram commutativity" goal is generated about `(R ◇ x).queries`. To guarantee good simp, add the names of `R` and `x` to the attribute:
```lean
attribute [local game_hopping_unfold] R x
```

This helps `by_abstraction` simplify away the composition implementation.

### Handling Stuck Simplification

Sometimes `by_abstraction` cannot fully simplify `simulateQ` (e.g., gets stuck on pattern matches in reduction code). Use the reduction-simplification tactic (TODO) to simplify further.

The simplification tactic works when the reduction is:
- A `bind` expression
- A `pure` expression
- A query (`roll`)
- Another directly exposed fragment of `OracleComp (withPMFAndStateSpec _ _)`
