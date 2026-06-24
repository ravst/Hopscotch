
We talk about Oracle implementation we first have to define its specification. THe pecification (of type OracleSpec I) specifies set of queries I we could ask. We also define function f : I -> Type _ that speicifes to ansers to query q : I have type (f q). Technicly, for x : OracleSpec I, x is just f, we have functions x.Domian := i, x.Range := x

Oracle implementatin (RStateOracle O) is a record of:
* stateType -- the internal state that implementation keep to rember ifnormation between procesed queires.
* initialState -- initial state is sampled form this distribution
* queries : QueryImpl O (RState stateType) -- how to prcess queires.  
   The type of queries field is alies to (x : spec.Domain) → RState stateType (spec.Range x) . It is a function that for query x of type spec.Domain (I) return computation in monad RState that return spec.Range x (expected returned types, as described by spec). Monad RState allow to acces state and sample randomness.

T build computation in RState use do notation. Sample using let x <- (D : PMF a) (autmatic lifting of PMF to RState) and access state using getState and setState.
