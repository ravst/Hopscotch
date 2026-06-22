import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.BitVec.Simprocs

/- # Observational Equivalence -/

/- In this file, we define the notion of observational equivalence for stateful random oracles,
   which is the main notion of equivalence used in our game-hopping proofs.
   It is basically the extensional equality of the two oracles as seen from the outside,
   and is define in terms of the distributions on query outputs:
   two oracles are observationally equivalent if for every finite list of queries,
   the distribution of the lists of of outputs they produce in response to those queries is the same.

   In particular, the internal state of the oracles is not being observed, so it is possible for two oracles
   even if their internal states are represented by different types.
-/

-- noncomputable def runQueriesAux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl O (RState S)) (queries : List (QueryS O)) :
--   RState S (List (QueryResult O)) :=
--   match queries with
--   | [] => pure []
--   | q :: qs => do
--     let o ← impl.impl q.index q.input
--     (fun os =>  ({index := q.index, output := o} :: os)) <$> runQueriesAux impl qs

-- noncomputable def runQueries {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF (List (QueryResult O)) :=
--   (runQueriesAux ro.queries queries).eval ro.initialState

-- lemma runQueriesEquiv {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : runQueries ro queries =
--    (RStateOracle.runQueriesOnlyOut ro queries)
--  := by
--   have hAux :
--       ∀ (queries : List (QueryS O)) (init : ro.stateType),
--         StateT.run (runQueriesAux ro.queries queries) init =
--           runQueries2Aux ro.queries queries init := by
--     intro queries
--     induction queries with
--     | nil =>
--         intro init
--         simp [runQueriesAux, runQueries2Aux]
--     | cons q qs ih =>
--         intro init
--         simp [runQueriesAux, runQueries2Aux, ih, map_eq_bind_pure_comp, bind_assoc]
--   simp [RStateOracle.runQueriesOnlyOut, runQueries, RStateOracle.runQueries2, RState.eval, RState.run, PMF.map_bind, hAux]

/-- Two stateful random oracles are observationally equal when every finite replay of
concrete queries induces the same distribution on observable query/output transcripts. -/
def ObsEq (ro₁ ro₂ : RStateOracle O) : Prop :=
  ∀ queriesList, runQueriesOnlyOut ro₁ queriesList = runQueriesOnlyOut ro₂ queriesList


/- ## Bounded Observational Equivalence -/

/-- A version of observational equivalence with an bound on how many queries are we allowed to ask -/
def ObsEqBounded (ro₁ ro₂ : RStateOracle O) (q_b : ENat) : Prop :=
  ∀ queriesList, queriesList.length <= q_b  ->
    runQueriesOnlyOut ro₁ queriesList = runQueriesOnlyOut ro₂ queriesList

lemma ObsEq_from_none (ro₁ ro₂ : RStateOracle O) :
  ObsEq ro₁ ro₂ <-> ObsEqBounded ro₁ ro₂ none := by
    constructor
    · intro H ql _trash
      apply H
    · intro H ql
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

/-- In our proofs the main tool for showing observational equivalence is abstraction, i.e.
    a function mapping the internal states of one oracle to the internal states of another oracle, such that
    the initial states are mapped to each other, and the output distributions of queries commute with the mapping.
-/
def mapSecond {α β γ} (f : β → γ) (p : α × β) : α × γ :=
  (p.1, f p.2)

@[simp] lemma mapSecond_mk {α β γ} (f : β → γ) (x : α) (y : β) :
    mapSecond f (x, y) = (x, f y) := rfl

def mapInputState (f : S₁ → S₂) (m : RState S₂ α) (s : S₁) : PMF (α × S₂) :=
  StateT.run m (f s)

noncomputable def mapOutputState (f : S₁ → S₂) (m : RState S₁ α) (s : S₁) :
    PMF (α × S₂) :=
  (StateT.run m s).map (mapSecond f)

/-- Usual deterministic-state abstraction between two stateful oracle implementations. -/
def correctAbstraction {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) : Prop :=
  ro₁.initialState.map f = ro₂.initialState ∧
  ∀ (query : O.Domain),
      mapOutputState f (ro₁.queries query) =
      mapInputState f (ro₂.queries query)

/-- A more general version of abstraction allows for probabilistic mappings between states. -/
noncomputable def bindInputState (f : S₁ → PMF S₂) (m : RState S₂ α) (s : S₁) :
    PMF (α × S₂) := do
  let x : S₂ ← f s
  StateT.run m x

noncomputable def bindSecond {α β γ} (f : β → PMF γ) (p : α × β) :
    PMF (α × γ) := do
  let y ← f p.2
  return (p.1, y)

noncomputable def bindOutputState (f : S₁ → PMF S₂) (m : RState S₁ α) (s : S₁) :
    PMF (α × S₂) :=
  (StateT.run m s).bind (bindSecond f)

def correctAbstractionBindDiag {I : Type _} {stateType₁ stateType₂ : Type _} {O : OracleSpec I}
  (ro₁ : QueryImpl O (RState stateType₁)) (ro₂ : QueryImpl O (RState stateType₂))
    (f : stateType₁ → PMF stateType₂) : Prop :=
  ∀ (query : O.Domain),
      bindOutputState f (ro₁ query) =
      bindInputState f (ro₂ query)


/-- Bind/probabilistic-state abstraction between two stateful oracles. -/
def correctAbstractionBind {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → PMF ro₂.stateType) : Prop :=
  ro₁.initialState.bind f = ro₂.initialState ∧
  ∀ (query : O.Domain),
      bindOutputState f (ro₁.queries query) =
      bindInputState f (ro₂.queries query)


/-- ## Correctness of Abstraction -/
/- In this section we show that the existence of a correct abstraction between two oracles,
   implies observation equivalence -/
lemma correctAbstractionImpliesObsEqInnerBind {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType) (HCor : correctAbstractionBind ro₁ ro₂ f) queriesList
  : forall (init : ro₁.stateType),
      (runQueries2Aux ro₁.queries queriesList init).bind (bindSecond f) =
      (f init).bind (runQueries2Aux ro₂.queries queriesList)
  := by
    induction queriesList
    case cons head tail Hind =>
      intro init
      have hStep :
          bindOutputState f (ro₁.queries head) init =
            bindInputState f (ro₂.queries head) init := by
        exact congrArg (fun g => g init) (HCor.2 head)
      have hStep' :
          (f init).bind (StateT.run (ro₂.queries head)) =
            (StateT.run (ro₁.queries head) init).bind (bindSecond f) := by
        simpa [mapInputState, mapOutputState] using hStep.symm
      simp [runQueries2Aux]
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
      simp [runQueries2Aux, PMF.map]
      simp [bindSecond]

lemma correctAbstractionBindImpliesObsEq {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType) (HCor : correctAbstractionBind ro₁ ro₂ f)
  : ObsEq ro₁ ro₂ := by
    intro queriesList
    have hRun2 :
        (runQueries2 ro₁ queriesList).bind (bindSecond f) =
        (runQueries2 ro₂ queriesList) := by
      simp [runQueries2]
      rw [<- HCor.1]
      simp [PMF.map]
      conv =>
        rhs
        arg 2
        intro a
        rw [<- correctAbstractionImpliesObsEqInnerBind _ _ _ HCor]
    simp [runQueriesOnlyOut]
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

lemma correctAbstration2Bind {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) :
      correctAbstraction ro₁ ro₂ f <-> correctAbstractionBind ro₁ ro₂ (PMF.pure ∘ f)
:= by
  simp [correctAbstraction, correctAbstractionBind]
  simp [PMF.map]
  intro H
  conv =>
    lhs
    intro q
    rw [mapInputState2Bind, mapOutputState2Bind]

-- we use bind version to prove obsEq from map version

-- this lemma is probably unused, but nice
lemma correctAbstractionImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType) (HCor : correctAbstraction ro₁ ro₂ f) queriesList
  : forall (init : ro₁.stateType),
      (runQueries2Aux ro₁.queries queriesList init).map (mapSecond f) =
      (runQueries2Aux ro₂.queries queriesList (f init))
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
    (hStep : ∀ (query : O.Domain),
      RState.mapStateBij f (ro₁.queries query) = ro₂.queries query) :
    correctAbstraction ro₁ ro₂ (f : ro₁.stateType → ro₂.stateType)
    := by
  refine ⟨hInit, ?_⟩
  intro query
  funext s
  have hRun :
      StateT.run (RState.mapStateBij f (ro₁.queries query)) (f s) =
        StateT.run (ro₂.queries query) (f s) := by
    simpa using (congrArg (fun m => StateT.run m (f s)) (hStep query))
  have hMap :
      mapOutputState (f : ro₁.stateType → ro₂.stateType) (ro₁.queries query) s =
        StateT.run (RState.mapStateBij f (ro₁.queries query)) (f s) := by
    change PMF.map (fun p : (O query) × ro₁.stateType => (p.1, f p.2))
      (StateT.run (ro₁.queries query) s) =
      PMF.map (fun p : (O query) × ro₁.stateType => (p.1, f p.2))
        (StateT.run (ro₁.queries query) (f.invFun (f s)))
    simp [f.left_inv]
  calc
    mapOutputState (f : ro₁.stateType → ro₂.stateType) (ro₁.queries query) s =
        StateT.run (RState.mapStateBij f (ro₁.queries query)) (f s) := hMap
    _ = StateT.run (ro₂.queries query) (f s) := hRun
    _ = mapInputState (f : ro₁.stateType → ro₂.stateType) (ro₂.queries query) s := by
          rfl

lemma mapStateBijImpliesObsEq {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType ≃ ro₂.stateType)
    (hInit : ro₁.initialState.map f = ro₂.initialState)
    (hStep : ∀ (query : O.Domain),
      RState.mapStateBij f (ro₁.queries query) = ro₂.queries query) :
    ObsEq ro₁ ro₂ := by
  exact correctAbstractionImpliesObsEq ro₁ ro₂ (f := (f : ro₁.stateType → ro₂.stateType))
    (mapStateBijImpliesCorrectAbstraction ro₁ ro₂ f hInit hStep)

lemma existsMapStateBijImpliesObsEq {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O)
    (h :
      ∃ f : ro₁.stateType ≃ ro₂.stateType,
        ro₁.initialState.map f = ro₂.initialState ∧
        (∀ (query : O.Domain),
          RState.mapStateBij f (ro₁.queries query) = ro₂.queries query)) :
    ObsEq ro₁ ro₂ := by
  rcases h with ⟨f, hInit, hStep⟩
  exact mapStateBijImpliesObsEq ro₁ ro₂ f hInit hStep



/- ## Correct Bounded Abstraction -/

/- In this section we define, and proof correctness of the bounded abstraction,
which is a version of abstraction used to show bounded observational equivalence.
Such an abstraction consists of a mapping between the states of the two oracles,
and a valuatiion function from the states of the first oracle to the natural number (extended with infinity),
such that the valuation of the initial states is above the bound,
each query decreases the valuation by at most one,
and the abstraction condition (commuting square) holds for states whose valuation non zero.
-/

/-- A valuation is good if each query decreases it by at most one. -/
def goodValuation {I : Type _} {O : OracleSpec I} (ro : RStateOracle O) (val : ro.stateType -> ENat)
  : Prop :=
  ∀ (query : O.Domain) (s : ro.stateType),
  (ro.queries query s).support ⊆ {x | val x.2 >= val s - 1}

/-- Step condition for the weighted bind abstraction.  The commuting square is only required
from states whose valuation is still positive. -/
def correctAbstractionBindBound_step {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ro₁.stateType → PMF ro₂.stateType)
  (val : ro₁.stateType → ENat)
  : Prop :=
∀ (query : O.Domain) (s : ro₁.stateType),
    (val s > 0) ->
    bindOutputState f (ro₁.queries query) s =
    bindInputState f (ro₂.queries query) s

/-- Weighted bind abstraction, without a specific initial query budget. -/
def correctAbstractionBindBound_inner {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ro₁.stateType → PMF ro₂.stateType) (val : ro₁.stateType → ENat) : Prop :=
ro₁.initialState.bind f = ro₂.initialState ∧
goodValuation ro₁ val ∧
correctAbstractionBindBound_step ro₁ ro₂ f val

def correctAbstractionBindBound {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ro₁.stateType → PMF ro₂.stateType) (val : ro₁.stateType → ENat) (b : ENat) : Prop :=
  correctAbstractionBindBound_inner ro₁ ro₂ f val ∧
  ro₁.initialState.support ⊆ {x | val x >= b}


/- ## Correctness of Bounded Abstraction -/
/- Finally, we show that correct bounded abstraction, implies bounded observational equivalence. -/

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
  (HStep : correctAbstractionBindBound_step ro₁ ro₂ f val) (queriesList : List (O.Domain))
  :  ∀ (init : ro₁.stateType), (hq : queriesList.length ≤  val init) ->
  (do
    let (x, y) <- (runQueries2Aux ro₁.queries queriesList init)
    let z <- (f y)
    return (x, z)
   ) =
      (f init).bind (runQueries2Aux ro₂.queries queriesList)
  := by
  induction queriesList with
  | nil =>
      intro init
      simp [runQueries2Aux, PMF.map]
  | cons head tail ih =>
          intro init Hinit
          simp at Hinit
          have hStep := HStep head init (by
            suffices ¬ (val init = 0) from pos_of_ne_zero this
            intro Hval
            simp [Hval] at Hinit
          )
          simp [bindOutputState, bindInputState, bindSecond] at hStep
          simp [runQueries2Aux, PMF.map]
          conv =>
            rhs
            rw [<-PMF.bind_bind]
            arg 1
            rw [← hStep]
          simp [bindSecond]
          apply bindCongrOnSupport
          intro a Ha
          rw [<-PMF.bind_bind]
          rw [← ih]
          · simp []
          suffices val init-1 <= val a.2 by
            have X : tail.length+1-1  <= val init -1 := by
              exact tsub_le_tsub_right Hinit 1
            have X' :  tail.length <= val init -1 := by
              exact X
            exact Preorder.le_trans (↑tail.length) (val init - 1) (val a.2) X this
          have X := Hval head init Ha
          apply X

lemma correctAbstractionBindBoundImpliesObsEqBounded2 {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
  (val : ro₁.stateType → ENat)
  (b : ℕ)
  (HB : correctAbstractionBindBound ro₁ ro₂ f val b) :
  ObsEqBounded ro₁ ro₂ b := by
  intro queriesList hq
  simp [runQueries2, runQueriesOnlyOut]
  simp at hq
  obtain ⟨HCor, Hinit⟩ := HB
  have hRun2Aux := correctAbstractionBind_bound_ImpliesObsEqInner ro₁ ro₂ f val HCor.2.1 HCor.2.2 queriesList
  have hRun2AuxFst := fun init Hinit =>  congrArg (fun p => PMF.map Prod.fst p) (hRun2Aux init Hinit)
  try (simp at hRun2AuxFst)
  try (simp only [GameHoppingSimplifyPMF])
  try (simp only [GameHoppingSimplifyPMF] at hRun2AuxFst)
  try (simp at hRun2AuxFst)
  simp only [GameHoppingPrettyPrintPMF]
  simp only [GameHoppingPrettyPrintPMF] at hRun2AuxFst
  simp [← HCor.1]
  apply bindCongrOnSupport
  intro y Hy
  have hybound : ↑queriesList.length ≤ val y := by
    have X := Hinit Hy
    simp at X
    apply Preorder.le_trans
    · exact ENat.coe_le_coe.mpr hq
    · apply X
  simpa [PMF.bind_bind, PMF.bind_const] using hRun2AuxFst y hybound

-- ## version with explicit indices

def correctAbstractionB {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ) : Prop :=
ro₁.initialState.map (f b) = ro₂.initialState ∧
∀ (query : O.Domain) (k : Fin b),
    mapOutputState (f k) (ro₁.queries query) =
    mapInputState (f (k + 1)) (ro₂.queries query) ∨
    mapOutputState (f (k+1)) (ro₁.queries query) =
    mapInputState (f (k+1)) (ro₂.queries query)

def correctAbstractionBStep {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
  (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ) : Prop :=
∀ (query : O.Domain) (k : Fin b),
    mapOutputState (f k) (ro₁.queries query) =
    mapInputState (f (k + 1)) (ro₂.queries query) ∨
    mapOutputState (f (k+1)) (ro₁.queries query) =
    mapInputState (f (k+1)) (ro₂.queries query)

lemma correctAbstractionBStep_monotone {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ℕ → ro₁.stateType → ro₂.stateType)
  {b₁ b₂ : ℕ} (HCor : correctAbstractionBStep ro₁ ro₂ f b₂) (hle : b₁ ≤ b₂) :
  correctAbstractionBStep ro₁ ro₂ f b₁ := by
  intro query k
  exact HCor query ⟨k, lt_of_lt_of_le k.2 hle⟩

lemma correctAbstractionBImpliesObsEqInner {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ)
  (HStep : correctAbstractionBStep ro₁ ro₂ f b) (queriesList : List (O.Domain))
  (hq : queriesList.length ≤ b) :
  ∃ k' ≤ b, ∀ (init : ro₁.stateType),
  (runQueries2Aux ro₁.queries queriesList init).map (fun (x,y) => (x, f k' y)) =
        (runQueries2Aux ro₂.queries queriesList (f b init))
  := by
  induction queriesList generalizing b with
  | nil =>
      exists b
      constructor
      · exact le_rfl
      · intro init
        simp [runQueries2Aux, PMF.map]
  | cons head tail ih =>
      cases b with
      | zero =>
          simp at hq
      | succ b =>
          obtain hStep := HStep head ⟨b, by omega⟩
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
                simp [runQueries2Aux, PMF.map]
                try (simp only [GameHoppingSimplifyPMF, mapSecond] at hStepDropInit)
                simp [← hStepDropInit, ← ih', PMF.map, Function.comp, mapSecond]
                try (simp only [GameHoppingSimplifyPMF])
                try simp
          | inr hStepKeep =>
              obtain ⟨k', hk', ih'⟩ := ih (b + 1) HStep hq_tail_succ
              exists k'
              constructor
              · exact hk'
              · intro init
                have hStepKeepInit := congrFun hStepKeep init
                simp [mapOutputState, mapInputState, mapSecond] at hStepKeepInit
                simp [runQueries2Aux, PMF.map]
                try (simp only [GameHoppingSimplifyPMF, mapSecond] at hStepKeepInit)
                simp [← hStepKeepInit, ← ih', PMF.map, Function.comp, mapSecond]
                try (simp only [GameHoppingSimplifyPMF])
                try simp

lemma correctAbstractionBImpliesObsEqBounded {I : Type} {O : OracleSpec I}
  (ro₁ ro₂ : RStateOracle O) (f : ℕ → ro₁.stateType → ro₂.stateType) (b : ℕ)
  (HCor : correctAbstractionB ro₁ ro₂ f b) :
  ObsEqBounded ro₁ ro₂ b := by
  intro queriesList hq
  simp [runQueries2, runQueriesOnlyOut]
  simp at hq
  obtain ⟨k', hk', hRun2Aux⟩ := correctAbstractionBImpliesObsEqInner ro₁ ro₂ f b HCor.2 queriesList hq
  have hRun2AuxFst : ∀ init : ro₁.stateType,
      PMF.map Prod.fst
        (PMF.map (fun x => match x with | (x, y) => (x, f k' y))
          (runQueries2Aux ro₁.queries queriesList init)) =
      PMF.map Prod.fst
        (runQueries2Aux ro₂.queries queriesList (f b init)) := by
    intro init
    exact congrArg (fun p => PMF.map Prod.fst p) (hRun2Aux init)
  try (simp at hRun2AuxFst)
  try (simp only [GameHoppingSimplifyPMF])
  try (simp only [GameHoppingSimplifyPMF] at hRun2AuxFst)
  try (simp at hRun2AuxFst)
  simp only [GameHoppingPrettyPrintPMF]
  simp only [GameHoppingPrettyPrintPMF] at hRun2AuxFst
  simp [← HCor.1]
  apply congrArg (fun g => PMF.bind ro₁.initialState g)
  funext a
  simpa [PMF.bind_bind, PMF.bind_const] using hRun2AuxFst a





-- lemma rState2Rstate_correct_abstraction_bind2 {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : Nat):
--   exists (f : (rState2Rstate q_b o).stateType -> PMF o.stateType)
--     (val : (rState2Rstate none o).stateType -> ENat),
--     correctAbstractionBindBound (rState2Rstate q_b o) o f val q_b := by sorry



-- also true. It is a bit problematic that implication from correctAbstractionBindBound2 f val none (for some val) to
--  correctAbstractionBind f (the same f) is nontrivial/false. It is implied that diagram commutes on rechable states, but it could not commute elsewhere (val have to be infty on rechable states and could be zero otherwise)
-- lemma rState2Rstate_correct_abstraction_bind {I : Type} {O : OracleSpec I} (o : RStateOracle O):
--   exists
--     (f : (rState2Rstate none o).stateType -> PMF o.stateType),
--     correctAbstractionBind (rState2Rstate none o) o f := by sorry

-- ## Useful helper lemmas about ObsEq and ObsEqBounded

@[symm]
lemma ObsEqSymm {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O) :
  ObsEq ro₁ ro₂ -> ObsEq ro₂ ro₁ := by
  intro h queriesList
  rw [h queriesList]
