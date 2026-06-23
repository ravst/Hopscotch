
We say that two Oracle Implemetation A and B (of type RStateOracle O) are Observation indistiginshable with length l  (ObsEqBounded A B l) if for any list of queries of length up to l, both A B repond to this queires with outputs of the same distribution. The l is ENat, value +inf (=none) mean that this holds for lists of queries of any length.

To prove this we almost always use correctAbstraction or correctAbstractionBind. We have to define function f : A.stateType -> B.stateType that should be preserved by the transition function. In more detail, if we take state a \in A.stateType it is the same to first process query q and the project via f or to project via f first and then process query.

correctAbstractionBind allow for function f to be randomized, ie. it is of type A.stateType -> PMF B.stateType.

These are main cases when we can define such fucntion:
* when A.stateType is naturally isomorphic to B.stateType we could take the ismorphism (if it preserves query processing)
* When A.stateType have some uninportant varaibles (that does not affect execution), then function f could just forget them.
* If A.stateType satifies some invariant, we could define f : {A.stateType // inv} -> A.stateType which forgot the invariant (this function is inclusion). In such case, the main work is in defining oracle implementation (RStateOracle) over type {A.stateType // inv}.
* Sometimes B.stateType keeps fresh randomness in variable t, because it samples much before it need to use it. To move the moment if sampling to later stage we do the following. Let A by implmentation that samples value of t when it is actually needed. Then we  we define nondetministc f as follows. On states when value of t is undefined in A.stateType but defined in B.stateType function f samples random value and put it to t in B.stateType.

We infer ObsEq from correctAbstraction using lemma correctAbstractionImpliesObsEq and from correctAbstractionBind using correctAbstractionBindImpliesObsEq.

