

Reudction form spec O1 to spec O2 is an objet of type OracleReduction O1 O2. It is struct with fileds:
* stateType -- type of internal state kept be reduction
* initialState : OracleComp (withPMFSpec O₁) stateType -- distribuition on inital state. In fact, during initialiation we can start making queires to O2. For that reason, it is OraceComp over speicfication (withPMFSpec O₁).
* queries : QueryImpl O₂ (OracleComp (withPMFAndStateSpec stateType O1)) --
    for each query q : O1.Domain, we return OrclaComp computation (value in this monad) of type O1.Range q.
    OracleComp is over spec  (withPMFAndStateSpec stateType O1) -- this allows to access state stateType via queries, sample a value from PMF (via query) and query O1 spec.
    Crucailly, while Oracle implementation (RStateOracle) implements queries diretly in RState, here we have to sample and acess state via query. That is necessery to be able to reactivly combine all this operations.

Reductins are used in proofs by combining them with implementations. GIven reduction R : OracleReduction O1 O2 and x : RStateOracle O1 by R.apply x to have RStateOracle O1. We also write R ◇ x as shorthend.

How reduction appear in sequence of game hopping hybrids? Let say we analyze implemenation A  and want to use assumption H. Then we rewrite A as reduction R composed with H.left, and then make a hop into R composed with H.right.  Therefore, it is convinent to write reduction after having explicit implementation of A, for example by replacing some operation via call to H.left.

After applciation of game_hopping it is common that we have to prove Indistinguishability between A and R ◇ x. Usually we use by_abstraction to prove this. The internal state space of composition R ◇ x is equal to product R.stateType × x.stateType, we have to write abstraction between it and A.stateType.

When x.stateType is unit,  abstractin function is tirvial. The tactic TODO delas with such cases. game_hopping autmatically tries this tactic.

When proving correct abstraction, the 'diagram commutativity' goal will be genrated, that take about (R ◇ x).queries. After adding names of R and x into  `attribute [local game_hopping_unfold]`, the tactic by_abstraction should simplify  away that implemtation of composition. Sometimes, it will not be be aply to simplify simulateQ completly (it analyzes reduction implmentation, and for example could be stack on matchings). In such cases use TODO tactic to simplify the reduction code more. Generally, TODO simplifes simulateQ when reduction is a bind, pure, making query (roll) or other directly expose fragment of OracleComp (withPMFAndStateSpec _ _).

