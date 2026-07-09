# Observational Equivalence Reference

## Definition

Two oracle implementations `A` and `B` (of type `OracleImpl O`) are **observation-indistinguishable with length** `l` (written `ObsEqBounded A B l`) if:
- For any list of queries of length up to `l`
- Both `A` and `B` respond with outputs having the same distribution
- The parameter `l` is an `ENat`; `+∞` (i.e. `none`) means this holds for lists of any length

## Proof Strategy

To prove observational equivalence, almost always use `correctAbstraction` or `correctAbstractionBind`.

You must define a function `f : A.stateType → B.stateType` that is preserved by the transition function:

**Commutativity Requirement**: For any state `a ∈ A.stateType` and query `q`, it must be equivalent to:
- First process `q` in `A` then project the resulting state via `f`, OR
- First project `a` via `f` then process `q` in `B`

### Randomized Abstraction

`correctAbstractionBind` allows `f` to be randomized, i.e. of type:
```
A.stateType → PMF B.stateType
```

## Common Abstraction Patterns

### 1. Natural Isomorphism
When `A.stateType` is naturally isomorphic to `B.stateType`, use the isomorphism as `f` (provided it preserves query processing).

### 2. Forgetting Unimportant Variables
When `A.stateType` has variables that don't affect execution, let `f` forget them.

### 3. Invariant-Based Abstraction
When `A.stateType` satisfies some invariant:
```
f : { a : A.stateType // inv a } → A.stateType
```
This function forgets the invariant (it's just the inclusion). The main work is defining the oracle implementation over the subtype `{ A.stateType // inv }`.

### 4. Deferred Randomness
Sometimes `B.stateType` samples randomness early but doesn't use it until later. To move sampling to a later stage:
- Let `A` be the implementation that samples only when needed
- Define nondeterministic `f`: on states where the value is undefined in `A` but defined in `B`, sample a random value and assign it

## Deriving ObsEq

Convert to the simpler `ObsEq` form:
- From `correctAbstraction` use: `correctAbstractionImpliesObsEq`
- From `correctAbstractionBind` use: `correctAbstractionBindImpliesObsEq`
