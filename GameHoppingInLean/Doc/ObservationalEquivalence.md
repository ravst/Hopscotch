We say that two oracle implementations `A` and `B` (of type `RStateOracle O`) are *observation-indistinguishable with length* `l` (written `ObsEqBounded A B l`) if, for any list of queries of length up to `l`, both `A` and `B` respond to these queries with outputs having the same distribution.  
The parameter `l` is an `ENat`; the value `+∞` (i.e. `none`) means that this holds for lists of queries of any length.

To prove this, we almost always use `correctAbstraction` or `correctAbstractionBind`.  
We must define a function `f : A.stateType → B.stateType` that is preserved by the transition function. More precisely, for any state `a ∈ A.stateType` and any query `q`, it should be equivalent to:

- first process `q` in `A` and then project the resulting state via `f`, or  
- first project `a` via `f` and then process `q` in `B`.

`correctAbstractionBind` allows the function `f` to be randomized, i.e. of type  
`A.stateType → PMF B.stateType`.

These are the main cases when we can define such a function `f`:

- When `A.stateType` is naturally isomorphic to `B.stateType`, we can take the isomorphism as `f` (provided it preserves query processing).
- When `A.stateType` has some unimportant variables (that do not affect execution), the function `f` can simply forget them.
- If `A.stateType` satisfies some invariant, we can define  
  `f : { a : A.stateType // inv a } → A.stateType`  
  which forgets the invariant (this function is the inclusion). In such a case, the main work is in defining the oracle implementation (`RStateOracle`) over the subtype `{ A.stateType // inv }`.
- Sometimes `B.stateType` keeps fresh randomness in a variable `t`, because it samples far before it needs to use it. To move the sampling to a later stage, we proceed as follows. Let `A` be the implementation that samples the value of `t` only when it is actually needed. Then we define a nondeterministic `f` as follows: on states where the value of `t` is undefined in `A.stateType` but defined in `B.stateType`, the function `f` samples a random value and assigns it to `t` in `B.stateType`.

We derive `ObsEq` from `correctAbstraction` using the lemma `correctAbstractionImpliesObsEq`, and from `correctAbstractionBind` using `correctAbstractionBindImpliesObsEq`.