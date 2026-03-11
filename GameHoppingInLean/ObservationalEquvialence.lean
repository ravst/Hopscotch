import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.StatefulRandomOracle

structure QueryS {I : Type} (O : OracleSpec I) where
  index : I
  input : O.domain index

-- def QueryS.toQuery {I : Type} {O : OracleSpec I} (q : QueryS O) :
--   OracleSpec.OracleQuery O (O.range q.index) :=
--   OracleSpec.query q.index q.input

structure QueryResult {I : Type} (O : OracleSpec I) where
  index : I
  output : O.range index

noncomputable def runQueriesAux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl3 O (RState S)) (queries : List (QueryS O)) :
  RState S (List (QueryResult O)) :=
  match queries with
  | [] => pure []
  | q :: qs => do
    let o ← impl.impl q.index q.input
    (fun os =>  ({index := q.index, output := o} :: os)) <$> runQueriesAux impl qs

noncomputable def runQueries {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF (List (QueryResult O)) :=
  (runQueriesAux ro.queries queries).eval ro.initialState


/-- Two stateful random oracles are observationally equal if, after any finite replay
context of prior queries, they induce the same output distribution on every next query. -/
def ObsEq (ro₁ ro₂ : RStateOracle O) : Prop :=
  ∀ queriesList, runQueries ro₁ queriesList = runQueries ro₂ queriesList

-- The simples suffictient condition of ObsEq is simple equality:

def obsEqReflexive (ro₁ ro₂ : RStateOracle O) (hEq : ro₁ = ro₂) :
  ObsEq ro₁ ro₂ := by
    rw [hEq]
    simp [ObsEq]

-- In more complicated hops, i.e. thoose that change states, we need a more flexible cryterion,
-- for observational equivalece. We start with the "correct abstraction", explained below.

-- Suppose we have a pair of oracles O₁ and O₂, which operates on states S₁ and S₂.
-- We say that a function f : S₁ → S₂ is a correct abstraction from O₁ to O₂, if
-- (a) After applying f to the initial state distribution of O₁, we get the initial state distribution of O₂
-- (b) The function `f` commutes with each query (see `correctAbstraction` below).
-- This is a kind of "bisimulation" condition, and is often easier to check than
-- the full definition of observational equivalence.

def mapSecond {α β γ} (f : β → γ) (p : α × β) : α × γ :=
  (p.1, f p.2)

def correctAbstraction {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) : Prop :=
  ro₁.initialState.map f = ro₂.initialState ∧
  ∀ (s₁ : ro₁.stateType) i (query : O.domain i),
      (StateT.run (ro₁.queries.impl i query) s₁).map (mapSecond f) =
      (StateT.run (ro₂.queries.impl i query) (f s₁))

-- We now want to prove that existence of a correctAbstraction impliesObsEq.
-- This is shown as correctAbstractionImpliesObsEq, but before that we need
-- a few auxiliary lemma, starting with an alternative definition of runQueries.

noncomputable def runQueries2Aux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl3 O (RState S)) (queries : List (QueryS O)) (init : S):
  PMF (List (QueryResult O) × S) :=
  match queries with
  | [] => pure ([], init)
  | q :: qs => do
    let (out, s) <- StateT.run (impl.impl q.index q.input) init
    let (outL, sF) <- runQueries2Aux impl qs s
    return ({index := q.index, output := out}::outL, sF)

noncomputable def runQueries2 {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF ((List (QueryResult O)) × ro.stateType) :=
  ro.initialState >>= runQueries2Aux ro.queries queries

lemma runQueriesEquiv {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : runQueries ro queries =
   (runQueries2 ro queries).map Prod.fst
 := by
  have hAux :
      ∀ (queries : List (QueryS O)) (init : ro.stateType),
        StateT.run (runQueriesAux ro.queries queries) init =
          runQueries2Aux ro.queries queries init := by
    intro queries
    induction queries with
    | nil =>
        intro init
        simp [runQueriesAux, runQueries2Aux]
    | cons q qs ih =>
        intro init
        simp [runQueriesAux, runQueries2Aux, ih, map_eq_bind_pure_comp, bind_assoc]
  simp [runQueries, runQueries2, RState.eval, RState.run, PMF.map_bind, hAux]

def correctAbstractionImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType) (HCor : correctAbstraction ro₁ ro₂ f) queriesList
  : forall (init : ro₁.stateType),
      (runQueries2Aux ro₁.queries queriesList init).map (fun (x,y) => (x, f y)) =
      (runQueries2Aux ro₂.queries queriesList (f init))
  := by
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
      simp []
      congr

def correctAbstractionImpliesObsEq {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType) (HCor : correctAbstraction ro₁ ro₂ f)
  : ObsEq ro₁ ro₂ := by
    intro queriesList
    rw [runQueriesEquiv (ro := ro₁) (queries := queriesList)]
    rw [runQueriesEquiv (ro := ro₂) (queries := queriesList)]
    have hRun2 :
        (runQueries2 ro₁ queriesList).map (fun (x, y) => (x, f y)) =
          (runQueries2 ro₂ queriesList) := by
      simp [runQueries2]
      rw [<- HCor.1]
      simp [PMF.map]
      conv =>
        rhs
        arg 2
        intro a
        rw [<- correctAbstractionImpliesObsEqInner _ _ _ HCor]
      simp [PMF.map]
    simpa [PMF.map_comp, Function.comp] using
      congrArg (fun p => p.map Prod.fst) hRun2
