import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.Misc.PMFLemmas


-- def QueryS.toQuery {I : Type} {O : OracleSpec I} (q : QueryS O) :
--   OracleSpec.OracleQuery O (O.range q.index) :=
--   OracleSpec.query q.index q.input


noncomputable def runQueriesAux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl3 O (RState S)) (queries : List (QueryS O)) :
  RState S (List (QueryResult O)) :=
  match queries with
  | [] => pure []
  | q :: qs => do
    let o ← impl.impl q.index q.input
    (fun os =>  ({index := q.index, output := o} :: os)) <$> runQueriesAux impl qs

noncomputable def runQueries {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF (List (QueryResult O)) :=
  (runQueriesAux ro.queries queries).eval ro.initialState

lemma runQueriesEquiv {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : runQueries ro queries =
   (RStateOracle.runQueriesOnlyOut ro queries)
 := by
  have hAux :
      ∀ (queries : List (QueryS O)) (init : ro.stateType),
        StateT.run (runQueriesAux ro.queries queries) init =
          RStateOracle.runQueries2Aux ro.queries queries init := by
    intro queries
    induction queries with
    | nil =>
        intro init
        simp [runQueriesAux, RStateOracle.runQueries2Aux]
    | cons q qs ih =>
        intro init
        simp [runQueriesAux, RStateOracle.runQueries2Aux, ih, map_eq_bind_pure_comp, bind_assoc]
  simp [RStateOracle.runQueriesOnlyOut, runQueries, RStateOracle.runQueries2, RState.eval, RState.run, PMF.map_bind, hAux]

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

lemma obsEq_trans {I : Type} {O : OracleSpec I}
    {ro₁ ro₂ ro₃ : RStateOracle O} (h₁₂ : ObsEq ro₁ ro₂) (h₂₃ : ObsEq ro₂ ro₃) :
    ObsEq ro₁ ro₃ := by
  intro queriesList
  rw [h₁₂ queriesList, h₂₃ queriesList]

lemma ObsEq.symm {ro₁ ro₂ : RStateOracle O} (h : ObsEq ro₁ ro₂) :
    ObsEq ro₂ ro₁ := by
  intro queriesList
  exact (h queriesList).symm

lemma ObsEqBounded.symm {ro₁ ro₂ : RStateOracle O} {q_b : ENat}
    (h : ObsEqBounded ro₁ ro₂ q_b) :
    ObsEqBounded ro₂ ro₁ q_b := by
  intro queriesList hBound
  exact (h queriesList hBound).symm

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

@[simp] lemma mapSecond_mk {α β γ} (f : β → γ) (x : α) (y : β) :
    mapSecond f (x, y) = (x, f y) := rfl

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


-- We now want to prove that existence of a correctAbstraction impliesObsEq.
-- This is shown as correctAbstractionImpliesObsEq, but before that we need
-- a few auxiliary lemma, starting with an alternative definition of runQueries.





--bind version of correct abstraction
noncomputable def bindInputState (f : S₁ → PMF S₂) (m : RState S₂ α) (s : S₁) : PMF (α × S₂) :=
  do
    let x : S₂ <- f s
    StateT.run m x


noncomputable def bindSecond {α β γ} (f : β → PMF γ) (p : α × β) : PMF (α × γ) :=
  do
    let y <- f p.2
    return (p.1, y)

noncomputable def bindOutputState (f : S₁ → PMF S₂) (m : RState S₁ α) (s : S₁) : PMF (α × S₂) :=
  (StateT.run m s).bind (bindSecond f)

def correctAbstractionBindDiag {I : Type _} {stateType₁ stateType₂ : Type _} {O : OracleSpec I}
  (ro₁ : QueryImpl3 O (RState stateType₁)) (ro₂ : QueryImpl3 O (RState stateType₂))
    (f : stateType₁ → PMF stateType₂) : Prop :=
  ∀ i (query : O.domain i),
      bindOutputState f (ro₁.impl i query) =
      bindInputState f (ro₂.impl i query)


def correctAbstractionBind {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → PMF ro₂.stateType) : Prop :=
  ro₁.initialState.bind f = ro₂.initialState ∧
  ∀ i (query : O.domain i),
      bindOutputState f (ro₁.queries.impl i query) =
      bindInputState f (ro₂.queries.impl i query)


lemma correctAbstractionImpliesObsEqInnerBind {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType) (HCor : correctAbstractionBind ro₁ ro₂ f) queriesList
  : forall (init : ro₁.stateType),
      (RStateOracle.runQueries2Aux ro₁.queries queriesList init).bind (bindSecond f) =
      (f init).bind (RStateOracle.runQueries2Aux ro₂.queries queriesList)
  := by
    induction queriesList
    simp [RStateOracle.runQueries2Aux, PMF.map]
    case cons head tail Hind =>
      intro init
      have hStep :
          bindOutputState f (ro₁.queries.impl head.index head.input) init =
            bindInputState f (ro₂.queries.impl head.index head.input) init := by
        exact congrArg (fun g => g init) (HCor.2 head.index head.input)
      have hStep' :
          (f init).bind (StateT.run (ro₂.queries.impl head.index head.input)) =
            (StateT.run (ro₁.queries.impl head.index head.input) init).bind (bindSecond f) := by
        simpa [mapInputState, mapOutputState] using hStep.symm
      simp [RStateOracle.runQueries2Aux]
      -- simp only [GameHoppingSimplifyPMF]
      -- simp []
      rw [<-PMF.bind_bind]
      rw [hStep']
      simp [mapInputState, mapOutputState, StateT.run, mapSecond, Functor.map, PMF.map]
      congr
      ext1 q
      conv =>
        rhs
        simp [bindSecond]
        rw [<-PMF.bind_bind]
        rw [<- Hind]
      simp [bindSecond]
    case nil =>
      simp [bindSecond]


lemma correctAbstractionBindImpliesObsEq {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType) (HCor : correctAbstractionBind ro₁ ro₂ f)
  : ObsEq ro₁ ro₂ := by
    intro queriesList
    rw [runQueriesEquiv (ro := ro₁) (queries := queriesList)]
    rw [runQueriesEquiv (ro := ro₂) (queries := queriesList)]
    have hRun2 :
        (RStateOracle.runQueries2 ro₁ queriesList).bind (bindSecond f) =
          (RStateOracle.runQueries2 ro₂ queriesList) := by
      simp [RStateOracle.runQueries2]
      rw [<- HCor.1]
      simp [PMF.map]
      conv =>
        rhs
        arg 2
        intro a
        rw [<- correctAbstractionImpliesObsEqInnerBind _ _ _ HCor]
    simp [RStateOracle.runQueriesOnlyOut]
    rw [<-hRun2]
    simp [PMF.map]
    congr
    ext1 a
    simp [Function.comp, bindSecond]

--end of bind version

--relating bind version to map version

lemma mapInputState2Bind :  mapInputState f x = bindInputState (PMF.pure ∘ f) x := by
  ext1 a
  simp [mapInputState, bindInputState]

lemma mapOutputState2Bind :  mapOutputState f x = bindOutputState (PMF.pure ∘ f) x := by
  ext1 a
  simp [mapOutputState, bindOutputState]
  simp [PMF.map]
  congr
  ext1 b
  simp [Function.comp, mapSecond, bindSecond]

lemma mapSecond2bind {A X Y} {f : X -> Y} : (PMF.pure ∘ (mapSecond (α := A) f)) = bindSecond (PMF.pure ∘ f) := by
  ext1
  simp [bindSecond, mapSecond]

lemma correctAbstration2Bind  {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) :
      correctAbstraction ro₁ ro₂ f <-> correctAbstractionBind ro₁ ro₂ (PMF.pure ∘ f)
:= by
  simp [correctAbstraction, correctAbstractionBind]
  simp [PMF.map]
  intro H
  conv =>
    lhs
    intro I q
    rw [mapInputState2Bind, mapOutputState2Bind]

-- we use bind version to prove obsEq from map version

-- this lemma is probably unused, but nice
lemma correctAbstractionImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType) (HCor : correctAbstraction ro₁ ro₂ f) queriesList
  : forall (init : ro₁.stateType),
      (RStateOracle.runQueries2Aux ro₁.queries queriesList init).map (mapSecond f) =
      (RStateOracle.runQueries2Aux ro₂.queries queriesList (f init))
  := by
    intro init
    have H := correctAbstractionImpliesObsEqInnerBind ro₁ ro₂ (PMF.pure ∘ f)
      (by rw [<-correctAbstration2Bind]; assumption) queriesList init
    simp at H
    rw [<-H]
    simp [PMF.map, mapSecond2bind]

lemma correctAbstractionImpliesObsEq {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType) (HCor : correctAbstraction ro₁ ro₂ f)
  : ObsEq ro₁ ro₂ := by
    apply correctAbstractionBindImpliesObsEq (f := (PMF.pure ∘ f))
    rw [<-correctAbstration2Bind]
    assumption

-- MAP STATE section
--map state => correctAbstraction => obsEq
lemma mapStateBijImpliesCorrectAbstraction {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType ≃ ro₂.stateType)
    (hInit : ro₁.initialState.map f = ro₂.initialState)
    (hStep : ∀ i (query : O.domain i),
      RState.mapStateBij f (ro₁.queries.impl i query) = ro₂.queries.impl i query) :
    correctAbstraction ro₁ ro₂ (f : ro₁.stateType → ro₂.stateType)
    := by
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


  --- Now, we need a version of the correct abstraction for the bounded obs eq,
  --- this time the abstraction is also parametrized by a natural number, which
  --- decreases by at most one in each step.

-- version with bind.


-- def correctAbstractionBindLine {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
--     (f g : ro₁.stateType → PMF ro₂.stateType)
--     (i : I) (query : O.domain i) : Prop :=
--       bindOutputState f (ro₁.queries.impl i query) =
--       bindInputState g (ro₂.queries.impl i query)

def goodValuation {I : Type _} {O : OracleSpec I} (ro : RStateOracle O) (val : ro.stateType -> ENat)
  : Prop :=
  ∀ i (query : O.domain i) (s : ro.stateType),
  (ro.queries.impl i query s).support ⊆ {x | val x.2 >= val s - 1}

def correctAbstractionBindBound_step {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ro₁.stateType → PMF ro₂.stateType)
  (val : ro₁.stateType → ENat)
  : Prop :=
∀ i (query : O.domain i) (s : ro₁.stateType),
    (val s > 0) ->
    bindOutputState f (ro₁.queries.impl i query) s =
    bindInputState f (ro₂.queries.impl i query) s

def correctAbstractionBindBound {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ro₁.stateType → PMF ro₂.stateType) (val : ro₁.stateType → ENat) : Prop :=
ro₁.initialState.bind f = ro₂.initialState ∧
goodValuation ro₁ val ∧
correctAbstractionBindBound_step ro₁ ro₂ f val


def correctAbstractionBindBound2 {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ro₁.stateType → PMF ro₂.stateType) (val : ro₁.stateType → ENat) (b : ENat): Prop :=
  correctAbstractionBindBound ro₁ ro₂ f val ∧
  ro₁.initialState.support ⊆ {x | val x >= b}

-- inductive correctAbstractionBiindBound2_ind {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
--   (f : ro₁.stateType → PMF ro₂.stateType)
--   : (s : ro₁.stateType) -> (Nat) -> Prop :=
-- | zero s : correctAbstractionBiindBound2_ind ro₁ ro₂ f s 0
-- | next s n :
--   (forall i (query : O.domain i) so',
--     so' ∈ ((ro₁.queries.impl i query s).support) ->
--     correctAbstractionBiindBound2_ind ro₁ ro₂ f so'.2 n) ->
--   correctAbstractionBiindBound2_ind ro₁ ro₂ f s (n+1)

lemma bindCongrOnSupport (x : PMF A) (Hf : forall y (_ : y ∈ x.support), f y = g y)
  : x.bind f = x.bind g :=
by
  rw [<-PMF.bindOnSupport_eq_bind]
  rw [<-PMF.bindOnSupport_eq_bind]
  congr 1
  ext1 a
  ext1 Ha
  apply Hf
  assumption

lemma correctAbstractionBind_bound_ImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
  (val : ro₁.stateType → ENat) (Hval : goodValuation ro₁ val)
  (HStep : correctAbstractionBindBound_step ro₁ ro₂ f val) (queriesList : List (QueryS O))
  :  ∀ (init : ro₁.stateType), (hq : queriesList.length ≤  val init) ->
  (do
    let (x, y) <- (RStateOracle.runQueries2Aux ro₁.queries queriesList init)
    let z <- (f y)
    return (x, z)
   ) =
      (f init).bind (RStateOracle.runQueries2Aux ro₂.queries queriesList)
  := by
  induction queriesList with
  | nil =>
      intro init
      simp [RStateOracle.runQueries2Aux, PMF.map]
  | cons head tail ih =>
          intro init Hinit
          simp at Hinit
          have hStep := HStep head.index head.input init (by
            suffices ¬ (val init = 0) from pos_of_ne_zero this
            intro Hval
            simp [Hval] at Hinit
          )
          simp [bindOutputState, bindInputState, bindSecond] at hStep
          simp [RStateOracle.runQueries2Aux, PMF.map]
          conv =>
            rhs
            rw [<-PMF.bind_bind]
            arg 1
            rw [← hStep]
          simp [bindSecond]
          apply bindCongrOnSupport
          intro a
          intro Ha
          rw [<-PMF.bind_bind]
          rw [← ih]
          simp []
          suffices val init-1 <= val a.2 by
            have X : tail.length+1-1  <= val init -1 := by
              exact tsub_le_tsub_right Hinit 1
            have X' :  tail.length <= val init -1 := by
              exact X
            exact Preorder.le_trans (↑tail.length) (val init - 1) (val a.2) X this
          have X := Hval head.index head.input init Ha
          apply X


lemma correctAbstractionBindBoundImpliesObsEqBounded2 {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
  (val : ro₁.stateType → ENat)
  (b : ℕ)
  (HB : correctAbstractionBindBound2 ro₁ ro₂ f val b) :
  ObsEqBounded ro₁ ro₂ b := by
  intro queriesList hq
  simp [runQueriesEquiv, RStateOracle.runQueries2, RStateOracle.runQueriesOnlyOut]
  simp at hq
  obtain ⟨HCor, Hinit⟩ := HB
  have hRun2Aux := correctAbstractionBind_bound_ImpliesObsEqInner ro₁ ro₂ f val HCor.2.1 HCor.2.2 queriesList
  have hRun2AuxFst := fun init Hinit =>  congrArg (fun p => PMF.map Prod.fst p) (hRun2Aux init Hinit)
  simp at hRun2AuxFst
  simp only [GameHoppingSimplifyPMF]
  simp only [GameHoppingSimplifyPMF] at hRun2AuxFst
  simp at hRun2AuxFst
  simp [← HCor.1]
  apply bindCongrOnSupport
  intro y Hy
  apply hRun2AuxFst y
  have X := Hinit Hy
  simp at X
  apply Preorder.le_trans
  · exact ENat.coe_le_coe.mpr hq
  · apply X


-- version with map
def correctAbstractionB {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ) : Prop :=
ro₁.initialState.map (f b) = ro₂.initialState ∧
∀ i (query : O.domain i) (k : Fin b),
    mapOutputState (f k) (ro₁.queries.impl i query) =
    mapInputState (f (k + 1)) (ro₂.queries.impl i query) ∨
    mapOutputState (f (k+1)) (ro₁.queries.impl i query) =
    mapInputState (f (k+1)) (ro₂.queries.impl i query)

def correctAbstractionBStep {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ) : Prop :=
∀ i (query : O.domain i) (k : Fin b),
    mapOutputState (f k) (ro₁.queries.impl i query) =
    mapInputState (f (k + 1)) (ro₂.queries.impl i query) ∨
    mapOutputState (f (k+1)) (ro₁.queries.impl i query) =
    mapInputState (f (k+1)) (ro₂.queries.impl i query)

lemma correctAbstractionBStep_monotone {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ℕ → ro₁.stateType → ro₂.stateType)
  {b₁ b₂ : ℕ} (HCor : correctAbstractionBStep ro₁ ro₂ f b₂) (hle : b₁ ≤ b₂) :
  correctAbstractionBStep ro₁ ro₂ f b₁ := by
  intro i query k
  exact HCor i query ⟨k, lt_of_lt_of_le k.2 hle⟩

lemma correctAbstractionBImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ)
  (HStep : correctAbstractionBStep ro₁ ro₂ f b) (queriesList : List (QueryS O))
  (hq : queriesList.length ≤  b): ∃ k' ≤ b, ∀ (init : ro₁.stateType),
  (RStateOracle.runQueries2Aux ro₁.queries queriesList init).map (fun (x,y) => (x, f k' y)) =
        (RStateOracle.runQueries2Aux ro₂.queries queriesList (f b init))
  := by
  induction queriesList generalizing b with
  | nil =>
      exists b
      constructor
      · exact le_rfl
      · intro init
        simp [RStateOracle.runQueries2Aux, PMF.map]
  | cons head tail ih =>
      cases b with
      | zero =>
          simp at hq
      | succ b =>
          obtain hStep := HStep head.index head.input ⟨b, by omega⟩
          have hq_tail_b : tail.length ≤ b := by
            simpa using Nat.succ_le_succ_iff.mp hq
          have hq_tail_succ : tail.length ≤ b + 1 := by
            omega
          cases hStep with
          | inl hStepDrop =>
              have HStep_b : correctAbstractionBStep ro₁ ro₂ f b :=
                correctAbstractionBStep_monotone ro₁ ro₂ f HStep (by omega)
              obtain ⟨k', hk', ih'⟩ := ih b HStep_b hq_tail_b
              exists k'
              constructor
              · omega
              · intro init
                have hStepDropInit := congrFun hStepDrop init
                simp [mapOutputState, mapInputState, mapSecond] at hStepDropInit
                simp [RStateOracle.runQueries2Aux, PMF.map]
                simp only [GameHoppingSimplifyPMF, mapSecond] at hStepDropInit
                simp [← hStepDropInit, ← ih']
                simp only [GameHoppingSimplifyPMF]
                simp
          | inr hStepKeep =>
              obtain ⟨k', hk', ih'⟩ := ih (b + 1) HStep hq_tail_succ
              exists k'
              constructor
              · exact hk'
              · intro init
                have hStepKeepInit := congrFun hStepKeep init
                simp [mapOutputState, mapInputState, mapSecond] at hStepKeepInit
                simp [RStateOracle.runQueries2Aux, PMF.map]
                simp only [GameHoppingSimplifyPMF, mapSecond] at hStepKeepInit
                simp [← hStepKeepInit, ← ih']
                simp only [GameHoppingSimplifyPMF]
                simp

lemma correctAbstractionBImpliesObsEqBounded {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ)
  (HCor : correctAbstractionB ro₁ ro₂ f b) :
  ObsEqBounded ro₁ ro₂ b := by
  intro queriesList hq
  simp [runQueriesEquiv, RStateOracle.runQueries2, RStateOracle.runQueriesOnlyOut]
  simp at hq
  obtain ⟨k', hk', hRun2Aux⟩ := correctAbstractionBImpliesObsEqInner ro₁ ro₂ f b HCor.2 queriesList hq
  have hRun2AuxFst : ∀ init : ro₁.stateType,
      PMF.map Prod.fst
        (PMF.map (fun x => match x with | (x, y) => (x, f k' y))
          (RStateOracle.runQueries2Aux ro₁.queries queriesList init)) =
      PMF.map Prod.fst
        (RStateOracle.runQueries2Aux ro₂.queries queriesList (f b init)) := by
    intro init
    exact congrArg (fun p => PMF.map Prod.fst p) (hRun2Aux init)
  simp at hRun2AuxFst
  simp only [GameHoppingSimplifyPMF]
  simp only [GameHoppingSimplifyPMF] at hRun2AuxFst
  simp at hRun2AuxFst
  simp [← HCor.1]
  simp [hRun2AuxFst]
  simp only [GameHoppingSimplifyPMF]
  simp



lemma rState2Rstate_correct_abstraction_bind2 {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : Nat):
  exists (f : (rState2Rstate q_b o).stateType -> PMF o.stateType)
    (val : (rState2Rstate none o).stateType -> ENat),
    correctAbstractionBindBound2 (rState2Rstate q_b o) o f val q_b := by sorry

-- also true. It is a bit problematic that implication from correctAbstractionBindBound2 f val none (for some val) to
--  correctAbstractionBind f (the same f) is nontrivial/false. It is implied that diagram commutes on rechable states, but it could not commute elsewhere (val have to be infty on rechable states and could be zero otherwise)
-- lemma rState2Rstate_correct_abstraction_bind {I : Type} {O : OracleSpec I} (o : RStateOracle O):
--   exists
--     (f : (rState2Rstate none o).stateType -> PMF o.stateType),
--     correctAbstractionBind (rState2Rstate none o) o f := by sorry
