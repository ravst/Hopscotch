import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.StatefulRandomOracle

structure QueryS {I : Type} (O : OracleSpec I) where
  index : I
  input : O.domain index

def QueryS.toQuery {I : Type} {O : OracleSpec I} (q : QueryS O) :
  OracleSpec.OracleQuery O (O.range q.index) :=
  OracleSpec.query q.index q.input

structure QueryResult {I : Type} (O : OracleSpec I) where
  index : I
  output : O.range index

noncomputable def runQueriesAux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl O (RState S)) (queries : List (QueryS O)) :
  RState S (List (QueryResult O)) :=
  match queries with
  | [] => pure []
  | q :: qs => do
    let o ← impl.impl (q.toQuery)
    (fun os =>  ({index := q.index, output := o} :: os)) <$> runQueriesAux impl qs

noncomputable def runQueries {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF (List (QueryResult O)) :=
  (runQueriesAux ro.queries queries).eval ro.initialState


noncomputable def runQueries2Aux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl O (RState S)) (queries : List (QueryS O)) (init : S):
  PMF (List (QueryResult O) × S) :=
  match queries with
  | [] => pure ([], init)
  | q :: qs => do
    let (out, s) <- StateT.run (impl.impl (q.toQuery)) init
    let (outL, sF) <- runQueries2Aux impl qs s
    return ({index := q.index, output := out}::outL, sF)

noncomputable def runQueries2 {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF ((List (QueryResult O)) × ro.stateType) :=
  ro.initialState >>= runQueries2Aux ro.queries queries

lemma runQueriesEquiv {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : runQueries ro queries =
   (runQueries2 ro queries).map Prod.fst
 := sorry

/-- Two stateful random oracles are observationally equal if, after any finite replay
context of prior queries, they induce the same output distribution on every next query. -/
def ObsEq (ro₁ ro₂ : RStateOracle O) : Prop :=
  ∀ queriesList, runQueries ro₁ queriesList = runQueries ro₂ queriesList

-- def ObsEqStr (ro₁ ro₂ : RStateOracle O) : Prop :=
  -- ∀ queriesList, runQueries2 ro₁ queriesList = (runQueries2 ro₂ queriesList).map (fun (x,y) => )


-- The simples suffictient condition of ObsEq is simple equality:

def obsEqReflexive (ro₁ ro₂ : RStateOracle O) (hEq : ro₁ = ro₂) :
  ObsEq ro₁ ro₂ := by
    rw [hEq]
    simp [ObsEq]

-- In more complicated passes, e.g. thoose that change states, we may need more flexible cryterions,
-- such as the correct abstraction explained below. But for now the simple equality has been working
-- fine.

-- Now, we would like to show a sufficient condition for two oracles to be observationally equivalent.
-- Suppose that we have a a pair of functions `f₁ : S₁ → S` and `f₂ : S₂ → S` where `S` is some "abstract state space" that captures
-- all the relevant information. Then, if the initial states induce the same distribution on `s`, and the query imlementation
-- if each oracle is compatible with the abstraction, i.e. if two states `f₁(s₁) = f₂(s₂)` then the implementation of each
-- query on `S₁` and `S₂` induces the same distribution on (Output × S), then the two oracles are observationally equivalent.
-- This is a kind of "bisimulation" condition, and is often easier to check than the full definition of observational equivalence.

-- I think I need an aux function that takes a function, a pair and applies this function to the second element of the pair, and leaves the first element alone.

def mapSecond {α β γ} (f : β → γ) (p : α × β) : α × γ :=
  (p.1, f p.2)

def correctAbstraction {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) : Prop :=
  ro₁.initialState.map f = ro₂.initialState ∧
  ∀ (s₁ : ro₁.stateType) i (query : O.OracleQuery (O.range i)),
      (mapSecond f) <$> (StateT.run (ro₁.queries.impl query) s₁) =
      (StateT.run (ro₂.queries.impl query) (f s₁))


def correctAbstractionImpliesObsEqInner {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType)
    (HCor : correctAbstraction ro₁ ro₂ f) queriesList :
    forall   (init : ro₁.stateType),
      (runQueries2Aux ro₁.queries queriesList init).map (fun (x,y) => (x, f y))  = (runQueries2Aux ro₂.queries queriesList (f init)) := by
    induction queriesList
    simp [runQueries2Aux, PMF.map]
    case cons head tail Hind =>
      intro init
      simp [runQueries2Aux]
      simp [correctAbstraction] at HCor
      rw [<- HCor.2]
      simp [StateT.run, mapSecond, Functor.map, PMF.map]
      conv =>
        rhs
        arg 2
        intro a
        arg 1
        rw [<- Hind]
      -- rw [<- Hind]
      simp []
      congr


def correctAbstractionImpliesObsEq {I : Type} {O : OracleSpec I} {S : Type} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType)
    (HCor : correctAbstraction ro₁ ro₂ f) queriesList:

      (runQueries2 ro₁ queriesList).map (fun (x,y) => (x, f y)) = (runQueries2 ro₂ queriesList) := by
    simp [runQueries2]
    rw [<- HCor.1]
    simp [PMF.map]
    conv =>
      rhs
      arg 2
      intro a
      rw [<- correctAbstractionImpliesObsEqInner _ _ _ HCor]
    simp [PMF.map]
