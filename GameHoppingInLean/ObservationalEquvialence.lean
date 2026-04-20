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

def ObsEqBounded (ro₁ ro₂ : RStateOracle O) (q_b : ENat): Prop :=
  ∀ queriesList, queriesList.length <= q_b  -> runQueries ro₁ queriesList = runQueries ro₂ queriesList

lemma ObsEq_from_none (ro₁ ro₂ : RStateOracle O):
  ObsEq ro₁ ro₂ <-> ObsEqBounded ro₁ ro₂ none := by
    constructor
    · intro H
      intro ql _trash
      apply H
    · intro H
      intro ql
      apply H
      exact right_eq_inf.mp rfl

lemma ObsEqBounded_monotone (ro₁ ro₂ : RStateOracle O) (qb1 qb2 : ENat)
  (H : ObsEqBounded ro₁ ro₂ qb2) (Hle : qb1 ≤ qb2) : ObsEqBounded ro₁ ro₂ qb1 := by
    intro ql Hq
    apply H
    exact Preorder.le_trans (↑ql.length) qb1 qb2 Hq Hle

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

def mapInputState (f : S₁ → S₂) (m : RState S₂ α) (s : S₁) : PMF (α × S₂) :=
  StateT.run m (f s)

noncomputable
def mapOutputState (f : S₁ → S₂) (m : RState S₁ α) (s : S₁) : PMF (α × S₂) :=
  (StateT.run m s).map (mapSecond f)

def correctAbstraction {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) : Prop :=
  ro₁.initialState.map f = ro₂.initialState ∧
  ∀ i (query : O.domain i),
      mapOutputState f (ro₁.queries.impl i query) =
      mapInputState f (ro₂.queries.impl i query)

lemma mapStateBijImpliesCorrectAbstraction {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType ≃ ro₂.stateType)
    (hInit : ro₁.initialState.map f = ro₂.initialState)
    (hStep : ∀ i (query : O.domain i),
      RState.mapStateBij f (ro₁.queries.impl i query) = ro₂.queries.impl i query) :
    correctAbstraction ro₁ ro₂ (f : ro₁.stateType → ro₂.stateType) := by
  refine ⟨hInit, ?_⟩
  intro i query
  funext s
  have hRun :
      StateT.run (RState.mapStateBij f (ro₁.queries.impl i query)) (f s) =
        StateT.run (ro₂.queries.impl i query) (f s) := by
    simpa using (congrArg (fun m => StateT.run m (f s)) (hStep i query))
  have hMap :
      mapOutputState (f : ro₁.stateType → ro₂.stateType) (ro₁.queries.impl i query) s =
        StateT.run (RState.mapStateBij f (ro₁.queries.impl i query)) (f s) := by
    change PMF.map (fun p : O.range i × ro₁.stateType => (p.1, f p.2))
      (StateT.run (ro₁.queries.impl i query) s) =
      PMF.map (fun p : O.range i × ro₁.stateType => (p.1, f p.2))
        (StateT.run (ro₁.queries.impl i query) (f.invFun (f s)))
    simp [f.left_inv]
  calc
    mapOutputState (f : ro₁.stateType → ro₂.stateType) (ro₁.queries.impl i query) s =
        StateT.run (RState.mapStateBij f (ro₁.queries.impl i query)) (f s) := hMap
    _ = StateT.run (ro₂.queries.impl i query) (f s) := hRun
    _ = mapInputState (f : ro₁.stateType → ro₂.stateType) (ro₂.queries.impl i query) s := by
          rfl

-- def correctAbstraction2 {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
--     [Nonempty ro₁.stateType]
--     (f : ro₁.stateType → ro₂.stateType) : Prop :=
--   ro₁.initialState.map f = ro₂.initialState ∧
--   ∀ i (query : O.domain i),
--       RState.mapState f (ro₁.queries.impl i query) = ro₂.queries.impl i query

-- /-- If two concrete states collapse to the same abstract state through `f`,
-- then one query step induces the same abstracted transition law. -/
-- def stepCongr {I : Type} {O : OracleSpec I} (ro : RStateOracle O)
--     {S' : Type} (f : ro.stateType → S') : Prop :=
--   ∀ (s s' : ro.stateType) i (query : O.domain i),
--       f s = f s' →
--       mapOutputState f (ro.queries.impl i query) s =
--       mapOutputState f (ro.queries.impl i query) s'

-- lemma correctAbstraction_implies_correctAbstraction2 {I : Type} {O : OracleSpec I}
--     (ro₁ ro₂ : RStateOracle O) [Nonempty ro₁.stateType]
--     (f : ro₁.stateType → ro₂.stateType) (hf : Function.Surjective f) :
--     correctAbstraction ro₁ ro₂ f → correctAbstraction2 ro₁ ro₂ f := by
--   intro h
--   rcases h with ⟨hInit, hStep⟩
--   refine ⟨hInit, ?_⟩
--   intro i query
--   funext s₂
--   have hStepAt :
--       (StateT.run (ro₁.queries.impl i query) (Function.invFun f s₂)).map (mapSecond f) =
--         StateT.run (ro₂.queries.impl i query) (f (Function.invFun f s₂)) := by
--     simpa [mapOutputState, mapInputState] using
--       congrArg (fun g => g (Function.invFun f s₂)) (hStep i query)
--   calc
--     StateT.run (RState.mapState f (ro₁.queries.impl i query)) s₂ =
--         (StateT.run (ro₁.queries.impl i query) (Function.invFun f s₂)).map (mapSecond f) := by
--           rfl
--     _ = StateT.run (ro₂.queries.impl i query) (f (Function.invFun f s₂)) := hStepAt
--     _ = StateT.run (ro₂.queries.impl i query) s₂ := by
--           have hs : f (Function.invFun f s₂) = s₂ := Function.rightInverse_invFun hf s₂
--           simpa [hs]

-- lemma correctAbstraction2_implies_correctAbstraction {I : Type} {O : OracleSpec I}
--     (ro₁ ro₂ : RStateOracle O) [Nonempty ro₁.stateType]
--     (f : ro₁.stateType → ro₂.stateType) (hf : Function.Injective f) :
--     correctAbstraction2 ro₁ ro₂ f → correctAbstraction ro₁ ro₂ f := by
--   intro h
--   rcases h with ⟨hInit, hStep⟩
--   refine ⟨hInit, ?_⟩
--   intro i query
--   funext s₁
--   have hRun :
--       StateT.run (RState.mapState f (ro₁.queries.impl i query)) (f s₁) =
--         StateT.run (ro₂.queries.impl i query) (f s₁) := by
--     exact congrArg (fun m => StateT.run m (f s₁)) (hStep i query)
--   have hs : Function.invFun f (f s₁) = s₁ := Function.leftInverse_invFun hf s₁
--   have hRun' :
--       mapOutputState f (ro₁.queries.impl i query) (Function.invFun f (f s₁)) =
--         mapInputState f (ro₂.queries.impl i query) s₁ := by
--     simpa [RState.mapState, mapSecond, mapOutputState, mapInputState] using hRun
--   calc
--     mapOutputState f (ro₁.queries.impl i query) s₁ =
--         mapOutputState f (ro₁.queries.impl i query) (Function.invFun f (f s₁)) := by
--           simpa [hs]
--     _ = mapInputState f (ro₂.queries.impl i query) s₁ := hRun'

-- lemma correctAbstraction2_implies_correctAbstraction_of_stepCongr
--     {I : Type} {O : OracleSpec I}
--     (ro₁ ro₂ : RStateOracle O) [Nonempty ro₁.stateType]
--     (f : ro₁.stateType → ro₂.stateType) (hf : Function.Surjective f)
--     (hCongr : stepCongr ro₁ f) :
--     correctAbstraction2 ro₁ ro₂ f → correctAbstraction ro₁ ro₂ f := by
--   intro h
--   rcases h with ⟨hInit, hStep⟩
--   refine ⟨hInit, ?_⟩
--   intro i query
--   funext s₁
--   have hRun :
--       StateT.run (RState.mapState f (ro₁.queries.impl i query)) (f s₁) =
--         StateT.run (ro₂.queries.impl i query) (f s₁) := by
--     exact congrArg (fun m => StateT.run m (f s₁)) (hStep i query)
--   have hRun' :
--       mapOutputState f (ro₁.queries.impl i query) (Function.invFun f (f s₁)) =
--         mapInputState f (ro₂.queries.impl i query) s₁ := by
--     simpa [RState.mapState, mapSecond, mapOutputState, mapInputState] using hRun
--   have hEq : f s₁ = f (Function.invFun f (f s₁)) := by
--     symm
--     exact Function.rightInverse_invFun hf (f s₁)
--   calc
--     mapOutputState f (ro₁.queries.impl i query) s₁ =
--         mapOutputState f (ro₁.queries.impl i query) (Function.invFun f (f s₁)) := by
--           exact hCongr s₁ (Function.invFun f (f s₁)) i query hEq
--     _ = mapInputState f (ro₂.queries.impl i query) s₁ := hRun'

-- lemma correctAbstraction_iff_correctAbstraction2 {I : Type} {O : OracleSpec I}
--     (ro₁ ro₂ : RStateOracle O) [Nonempty ro₁.stateType]
--     (f : ro₁.stateType → ro₂.stateType) (hf : Function.Bijective f) :
--     correctAbstraction ro₁ ro₂ f ↔ correctAbstraction2 ro₁ ro₂ f := by
--   constructor
--   · exact correctAbstraction_implies_correctAbstraction2 ro₁ ro₂ f hf.surjective
--   · exact correctAbstraction2_implies_correctAbstraction ro₁ ro₂ f hf.injective

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

lemma correctAbstractionImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType) (HCor : correctAbstraction ro₁ ro₂ f) queriesList
  : forall (init : ro₁.stateType),
      (runQueries2Aux ro₁.queries queriesList init).map (fun (x,y) => (x, f y)) =
      (runQueries2Aux ro₂.queries queriesList (f init))
  := by
    induction queriesList
    simp [runQueries2Aux, PMF.map]
    case cons head tail Hind =>
      intro init
      have hStep :
          mapOutputState f (ro₁.queries.impl head.index head.input) init =
            mapInputState f (ro₂.queries.impl head.index head.input) init := by
        exact congrArg (fun g => g init) (HCor.2 head.index head.input)
      have hStep' :
          StateT.run (ro₂.queries.impl head.index head.input) (f init) =
            (StateT.run (ro₁.queries.impl head.index head.input) init).map (mapSecond f) := by
        simpa [mapInputState, mapOutputState] using hStep.symm
      simp [runQueries2Aux]
      rw [hStep']
      simp [mapInputState, mapOutputState, StateT.run, mapSecond, Functor.map, PMF.map]
      conv =>
        rhs
        arg 2
        intro a
        arg 1
        rw [<- Hind]
      simp []
      congr

lemma correctAbstractionImpliesObsEq {I : Type} {O : OracleSpec I}
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

lemma mapStateBijImpliesObsEq {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType ≃ ro₂.stateType)
    (hInit : ro₁.initialState.map f = ro₂.initialState)
    (hStep : ∀ i (query : O.domain i),
      RState.mapStateBij f (ro₁.queries.impl i query) = ro₂.queries.impl i query) :
    ObsEq ro₁ ro₂ := by
  exact correctAbstractionImpliesObsEq ro₁ ro₂ (f := (f : ro₁.stateType → ro₂.stateType))
    (mapStateBijImpliesCorrectAbstraction ro₁ ro₂ f hInit hStep)

lemma existsMapStateBijImpliesObsEq {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O)
    (h :
      ∃ f : ro₁.stateType ≃ ro₂.stateType,
        ro₁.initialState.map f = ro₂.initialState ∧
        (∀ i (query : O.domain i),
          RState.mapStateBij f (ro₁.queries.impl i query) = ro₂.queries.impl i query)) :
    ObsEq ro₁ ro₂ := by
  rcases h with ⟨f, hInit, hStep⟩
  exact mapStateBijImpliesObsEq ro₁ ro₂ f hInit hStep
