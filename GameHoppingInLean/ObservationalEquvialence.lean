import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.Misc.PMFLemmas

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

/-- Run a finite list of concrete oracle queries and keep only their observable outputs. -/
noncomputable def runQueries {I : Type} {O : OracleSpec I}
    (ro : RStateOracle O) (queries : List O.Domain) :
    PMF (List (QueryWithResult O)) :=
  RStateOracle.runQueriesOnlyOut ro queries

/-- Two stateful random oracles are observationally equal when every finite replay of
concrete queries induces the same distribution on observable query/output transcripts. -/
def ObsEq {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O) : Prop :=
  ∀ queriesList : List O.Domain, runQueries ro₁ queriesList = runQueries ro₂ queriesList

/- ## Bounded Observational Equivalence -/

/-- A version of observational equivalence with an bound on how many queries are we allowed to ask -/
def ObsEqBounded {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (q_b : ENat) : Prop :=
  ∀ queriesList : List O.Domain,
    queriesList.length ≤ q_b → runQueries ro₁ queriesList = runQueries ro₂ queriesList

/- ## Abstraction -/

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
  ∀ q : O.Domain,
    mapOutputState f (ro₁.queries q) =
    mapInputState f (ro₂.queries q)

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

/-- Bind/probabilistic-state abstraction between two query implementations. -/
def correctAbstractionBindDiag {I : Type} {stateType₁ stateType₂ : Type}
    {O : OracleSpec I}
    (ro₁ : QueryImpl O (RState stateType₁)) (ro₂ : QueryImpl O (RState stateType₂))
    (f : stateType₁ → PMF stateType₂) : Prop :=
  ∀ q : O.Domain,
    bindOutputState f (ro₁ q) =
    bindInputState f (ro₂ q)

/-- Bind/probabilistic-state abstraction between two stateful oracles. -/
def correctAbstractionBind {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → PMF ro₂.stateType) : Prop :=
  ro₁.initialState.bind f = ro₂.initialState ∧
  correctAbstractionBindDiag ro₁.queries ro₂.queries f

/-- ## Correctness of Abstraction -/
/- In this section we show that the existence of a correct abstraction between two oracles,
   implies observation equivalence -/
lemma correctAbstractionImpliesObsEqInnerBind {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (HCor : correctAbstractionBind ro₁ ro₂ f) (queriesList : List O.Domain) :
    ∀ init : ro₁.stateType,
      (RStateOracle.runQueries2Aux ro₁.queries queriesList init).bind (bindSecond f) =
      (f init).bind (RStateOracle.runQueries2Aux ro₂.queries queriesList) := by
  induction queriesList with
  | nil =>
      intro init
      simp [RStateOracle.runQueries2Aux, bindSecond]
  | cons head tail ih =>
      intro init
      have hStep :
          bindOutputState f (ro₁.queries head) init =
            bindInputState f (ro₂.queries head) init := by
        exact congrFun (HCor.2 head) init
      have hStep' :
          (f init).bind (StateT.run (ro₂.queries head)) =
            (StateT.run (ro₁.queries head) init).bind (bindSecond f) := by
        simpa [bindInputState, bindOutputState] using hStep.symm
      simp [RStateOracle.runQueries2Aux]
      rw [← PMF.bind_bind, hStep']
      simp [bindSecond, PMF.bind_bind]
      congr
      funext q
      simpa [PMF.map_bind, bindSecond, Function.comp_def] using
        congrArg
          (PMF.map (fun p : List (QueryWithResult O) × ro₂.stateType =>
            ({ input := head, output := q.1 } :: p.1, p.2)))
          (ih q.2)

lemma correctAbstractionBindImpliesObsEq {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (HCor : correctAbstractionBind ro₁ ro₂ f) :
    ObsEq ro₁ ro₂ := by
  intro queriesList
  have hRun :
      (RStateOracle.runQueries2 ro₁ queriesList).bind (bindSecond f) =
        RStateOracle.runQueries2 ro₂ queriesList := by
    simp [RStateOracle.runQueries2, ← HCor.1, PMF.bind_bind]
    congr
    funext init
    exact correctAbstractionImpliesObsEqInnerBind ro₁ ro₂ f HCor queriesList init
  simp [runQueries, RStateOracle.runQueriesOnlyOut]
  change PMF.map Prod.fst (RStateOracle.runQueries2 ro₁ queriesList) =
    PMF.map Prod.fst (RStateOracle.runQueries2 ro₂ queriesList)
  rw [← hRun]
  simp [bindSecond, PMF.map, Function.comp_def]

lemma mapInputState2Bind {S₁ S₂ α : Type} (f : S₁ → S₂) (x : RState S₂ α) :
    mapInputState f x = bindInputState (PMF.pure ∘ f) x := by
  funext s
  simp [mapInputState, bindInputState]

lemma mapOutputState2Bind {S₁ S₂ α : Type} (f : S₁ → S₂) (x : RState S₁ α) :
    mapOutputState f x = bindOutputState (PMF.pure ∘ f) x := by
  funext s
  rw [mapOutputState, bindOutputState, PMF.map]
  congr
  funext y
  simp [bindSecond, mapSecond]

lemma correctAbstration2Bind {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f : ro₁.stateType → ro₂.stateType) :
    correctAbstraction ro₁ ro₂ f ↔ correctAbstractionBind ro₁ ro₂ (PMF.pure ∘ f) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [PMF.map, Function.comp_def] using h.1
    · intro q
      rw [← mapOutputState2Bind f (ro₁.queries q),
        ← mapInputState2Bind f (ro₂.queries q)]
      exact h.2 q
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [PMF.map, Function.comp_def] using h.1
    · intro q
      rw [mapOutputState2Bind f (ro₁.queries q),
        mapInputState2Bind f (ro₂.queries q)]
      exact h.2 q

lemma correctAbstractionImpliesObsEqInner {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType)
    (HCor : correctAbstraction ro₁ ro₂ f) (queriesList : List O.Domain) :
    ∀ init : ro₁.stateType,
      (RStateOracle.runQueries2Aux ro₁.queries queriesList init).map (mapSecond f) =
      RStateOracle.runQueries2Aux ro₂.queries queriesList (f init) := by
  intro init
  have hBind := correctAbstractionImpliesObsEqInnerBind ro₁ ro₂ (PMF.pure ∘ f)
    ((correctAbstration2Bind ro₁ ro₂ f).mp HCor) queriesList init
  rw [PMF.map]
  have hfun :
      (PMF.pure ∘ (mapSecond (α := List (QueryWithResult O)) f)) =
        bindSecond (α := List (QueryWithResult O)) (PMF.pure ∘ f) := by
    funext y
    simp [bindSecond, mapSecond]
  rw [hfun]
  simpa [Function.comp_def] using hBind

lemma correctAbstractionImpliesObsEq {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → ro₂.stateType)
    (HCor : correctAbstraction ro₁ ro₂ f) :
    ObsEq ro₁ ro₂ := by
  exact correctAbstractionBindImpliesObsEq ro₁ ro₂ (PMF.pure ∘ f)
    ((correctAbstration2Bind ro₁ ro₂ f).mp HCor)

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
def goodValuation {I : Type} {O : OracleSpec I} (ro : RStateOracle O)
    (val : ro.stateType → ENat) : Prop :=
  ∀ (q : O.Domain) (s : ro.stateType),
    (StateT.run (ro.queries q) s).support ⊆
      {x : O.Range q × ro.stateType | val x.2 ≥ val s - 1}

/-- Step condition for the weighted bind abstraction.  The commuting square is only required
from states whose valuation is still positive. -/
def correctAbstractionBindBound_step {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (val : ro₁.stateType → ENat) : Prop :=
  ∀ (q : O.Domain) (s : ro₁.stateType),
    val s > 0 →
      bindOutputState f (ro₁.queries q) s =
      bindInputState f (ro₂.queries q) s

/-- Weighted bind abstraction, without a specific initial query budget. -/
def correctAbstractionBindBound_inner {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (val : ro₁.stateType → ENat) : Prop :=
  ro₁.initialState.bind f = ro₂.initialState ∧
  goodValuation ro₁ val ∧
  correctAbstractionBindBound_step ro₁ ro₂ f val

/-- Weighted bind abstraction for a bounded number of queries. -/
def correctAbstractionBindBound {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (val : ro₁.stateType → ENat) (b : ENat) : Prop :=
  correctAbstractionBindBound_inner ro₁ ro₂ f val ∧
  ro₁.initialState.support ⊆ {x | val x ≥ b}

/-- ## Correctness of Bounded Abstraction -/
/- Finally, we show that correct bounded abstraction, implies bounded observational equivalence. -/
lemma bindCongrOnSupport {A B : Type} (x : PMF A) {f g : A → PMF B}
    (Hf : ∀ y (_ : y ∈ x.support), f y = g y) :
    x.bind f = x.bind g := by
  rw [← PMF.bindOnSupport_eq_bind]
  rw [← PMF.bindOnSupport_eq_bind]
  congr 1
  ext y hy
  simp [Hf y hy]

lemma correctAbstractionBind_bound_ImpliesObsEqInner {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (val : ro₁.stateType → ENat) (Hval : goodValuation ro₁ val)
    (HStep : correctAbstractionBindBound_step ro₁ ro₂ f val)
    (queriesList : List O.Domain) :
    ∀ init : ro₁.stateType, queriesList.length ≤ val init →
      (do
        let (x, y) ← RStateOracle.runQueries2Aux ro₁.queries queriesList init
        let z ← f y
        return (x, z)) =
      (f init).bind (RStateOracle.runQueries2Aux ro₂.queries queriesList) := by
  induction queriesList with
  | nil =>
      intro init _hq
      simp [RStateOracle.runQueries2Aux]
  | cons head tail ih =>
      intro init hq
      simp at hq
      have hStep := HStep head init (by
        suffices val init ≠ 0 from pos_iff_ne_zero.mpr this
        intro hzero
        simp [hzero] at hq)
      simp [bindOutputState, bindInputState] at hStep
      simp [RStateOracle.runQueries2Aux]
      conv =>
        rhs
        rw [← PMF.bind_bind]
        arg 1
        rw [← hStep]
      simp [bindSecond]
      apply bindCongrOnSupport
      intro a ha
      rw [← PMF.bind_bind]
      rw [← ih]
      · simp
      · have htail : (tail.length : ENat) ≤ val init - 1 := by
          exact tsub_le_tsub_right hq 1
        exact le_trans htail (Hval head init ha)

lemma correctAbstractionBindBoundImpliesObsEqBounded {I : Type} {O : OracleSpec I}
    (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
    (val : ro₁.stateType → ENat) (b : ENat)
    (HB : correctAbstractionBindBound ro₁ ro₂ f val b) :
    ObsEqBounded ro₁ ro₂ b := by
  intro queriesList hq
  simp [runQueries, RStateOracle.runQueriesOnlyOut, RStateOracle.runQueries2]
  obtain ⟨HCor, Hinit⟩ := HB
  simp [← HCor.1, PMF.bind_bind]
  rw [PMF.map_bind, PMF.map_bind]
  apply bindCongrOnSupport
  intro init hinit
  have hrun := correctAbstractionBind_bound_ImpliesObsEqInner ro₁ ro₂ f val
    HCor.2.1 HCor.2.2 queriesList init (le_trans hq (Hinit hinit))
  have hfst := congrArg (PMF.map Prod.fst) hrun
  simpa [PMF.map_bind, bindSecond, PMF.map, Function.comp_def] using hfst

/-!
The older map-state-bijection, finite-step map abstraction, and `rState2Rstate` sections from
this file are intentionally left out of active code for now. They depend on the old `QueryS` /
`QueryResult` / `QueryImpl3` API and, in the `rState2Rstate` case, on behavioral-oracle
definitions that are currently commented out in `StatefulRandomOracle.lean`.
-/
