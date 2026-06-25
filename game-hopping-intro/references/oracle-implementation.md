# Oracle Implementation Reference

## Oracle Specification

Before defining an oracle implementation, define its specification (`OracleSpec I`):
- The specification describes the set of queries `I` that can be asked
- Define a function `f : I → Type _` that specifies the type of answers to query `q : I`

For `x : OracleSpec I`:
- `x.Domain := I` (the query type)
- `x.Range := x` (the answer type function)

## Oracle Implementation Structure

An oracle implementation (`RStateOracle O`) is a record with:

- **`stateType`** – the internal state type that the implementation keeps between processed queries

- **`initialState`** – the initial state, sampled from a distribution

- **`queries : QueryImpl O (RState stateType)`** – how to process queries
  - This is `(x : spec.Domain) → RState stateType (spec.Range x)`
  - For query `x` of type `spec.Domain`, returns a computation in the `RState` monad
  - Produces a value of type `spec.Range x` (the expected return type)
  - The `RState` monad allows:
    - Access to the state via `getState` and `setState`
    - Sampling of randomness

## Building RState Computations

Use `do`-notation to build computations in `RState`:

```lean
-- Sample from a probability distribution
let x ← (D : PMF α)

-- Access the current state
state ← getState

-- Modify the state
setState newState
```

The `PMF` type is automatically lifted to `RState` for convenience.

## Key Concepts

- **State-based Computation**: Track internal state across multiple queries
- **Probabilistic**: Support random sampling via `PMF`
- **Monad**: Compose operations cleanly with `do`-notation
