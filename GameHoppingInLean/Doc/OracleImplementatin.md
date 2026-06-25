When we talk about an oracle implementation, we first have to define its specification.  
The specification (of type `OracleSpec I`) describes the set of queries `I` that we can ask.  
We also define a function `f : I → Type _` that specifies that answers to a query `q : I` have type `f q`.  

Technically, for `x : OracleSpec I`, `x` is just such a function. We have:

- `x.Domain := I`
- `x.Range := x`

An oracle implementation (`RStateOracle O`) is a record consisting of:

- `stateType` – the internal state that the implementation keeps to remember information between processed queries;
- `initialState` – the initial state, sampled from this distribution;
- `queries : QueryImpl O (RState stateType)` – how to process queries.  

The type of the `queries` field is an alias for  
`(x : spec.Domain) → RState stateType (spec.Range x)`.  
It is a function that, for a query `x` of type `spec.Domain` (`I`), returns a computation in the monad `RState` that produces a value of type `spec.Range x` (the expected return type, as described by `spec`). The monad `RState` allows access to the state and sampling of randomness.

To build computations in `RState`, use `do`-notation.  
Sample using `let x ← (D : PMF α)` (there is an automatic lifting of `PMF` to `RState`), and access or modify the state using `getState` and `setState`.