A reduction from a specification `O₁` to a specification `O₂` is an object of type `OracleReduction O₁ O₂`. It is a structure with the following fields:

- `stateType` – the type of the internal state kept by the reduction;
- `initialState : OracleComp (withPMFSpec O₁) stateType` – a distribution on the initial state. In fact, during initialization we are already allowed to make queries to `O₂`. For that reason, `initialState` is an `OracleComp` over the specification `withPMFSpec O₁`;
- `queries : QueryImpl O₂ (OracleComp (withPMFAndStateSpec stateType O₁))` –  
  for each query `q : O₂.Domain`, we return an `OracleComp` computation (a value in this monad) of type `O₂.Range q`.  
  Here `OracleComp` is over the specification `withPMFAndStateSpec stateType O₁`, which allows us to:
  - access the state of type `stateType` via queries,
  - sample values from a `PMF` (via queries),
  - and query the oracle specified by `O₁`.  

Crucially, while an oracle implementation (`RStateOracle`) implements queries directly in `RState`, a reduction must sample randomness and access state via queries. This is necessary to be able to reactively combine all these operations.

Reductions are used in proofs by composing them with implementations.  
Given a reduction `R : OracleReduction O₁ O₂` and `x : RStateOracle O₂`, we obtain a new implementation `R.apply x : RStateOracle O₁`.  
We also write `R ◇ x` as shorthand for this composition.

How do reductions appear in a sequence of game-hopping hybrids?  
Suppose we analyze an implementation `A` and want to use an assumption `H`. Then we rewrite `A` as a reduction `R` composed with `H.left`, and then perform a hop to `R` composed with `H.right`. Therefore, it is convenient to define the reduction after we have an explicit implementation of `A`, for example by replacing some operation with a call to `H.left`.

After applying `game_hopping`, it is common that we must prove indistinguishability between `A` and `R ◇ x`. Usually we use `by_abstraction` to prove this. The internal state space of the composition `R ◇ x` is the product `R.stateType × x.stateType`, and we need to define an abstraction between this product and `A.stateType`.

When `x.stateType` is `Unit`, the abstraction function is trivial. The tactic TODO deals with such cases, and `game_hopping` automatically tries this tactic.

When proving correct abstraction, a “diagram commutativity” goal will be generated that talks about `(R ◇ x).queries`. After adding the names of `R` and `x` to  
`attribute [local game_hopping_unfold]`, the `by_abstraction` tactic should simplify away the implementation of the composition. Sometimes, it will not be able to fully simplify `simulateQ` (it analyzes the reduction implementation and, for example, may get stuck on pattern matches). In such cases, use the TODO tactic to simplify the reduction code further.  

In general, TODO simplifies `simulateQ` when the reduction is a `bind`, `pure`, a query (`roll`), or another directly exposed fragment of `OracleComp (withPMFAndStateSpec _ _)`.