import GameHoppingInLean.Comp.OracleReductions
import GameHoppingInLean.Tactic.SimpAttrLemmas
open OracleReduction

/- # compositions of reduction
We define composition of reductions. This file is only used in soundnes proof - in cryptographic proofs reductions are
rearly composed with each other. -/

/-- Helper: simulating a computation through the identity reduction (first via
`addPMFtoImpl2` of the identity queries, then via `defaultImpl`) and applying the
initial state leaves the computation unchanged up to pairing with the (untouched)
state. Proved by induction over the free monad structure of `comp`. -/
lemma identity_roundtrip {Output I : Type} {O : OracleSpec I}
    (comp : OracleComp (withPMFSpec O) Output) (init : Unit) :
    (simulateQ (@defaultImpl I O Unit)
        (simulateQ (addPMFtoImpl2 (OracleReduction.identity O).queries) comp)) init
      = (fun o => (o, init)) <$> comp := by
  induction comp using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa ih =>
    cases t with
    | oracle i =>
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          addPMFtoImpl2]
        simp [ih]
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          identity, OracleSpec.query
        ]
        simp [bind, pure]
    | sample p =>
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          addPMFtoImpl2]
        simp [ih]
        simp [bind, pure]

lemma applyreduction2_identity {Output I : Type} {O : OracleSpec I}
  (dist : OracleComp (withPMFSpec O) Output)
  : applyReductionToAdversary (OracleReduction.identity O) dist = dist := by
  simp only [applyReductionToAdversary, OracleReduction.identity, pure_bind]
  have h := identity_roundtrip (O := O) dist ()
  simp only [OracleReduction.identity] at h
  simp [OracleReduction.lower_state_passing]
  rw [h]
  simp [Functor.map_map]

/-! ## Composition of reductions

We now build the composition of two reductions and prove that applying the
composed reduction to an adversary computation equals applying the two
reductions one after another.  The core technical work happens in
`combineImpl_simulate` (proved by induction over the simulated computation),
with `embedSnd_simulate` handling the embedding of the inner reduction's state
into the right component of the combined state. -/

/-- Embed a computation that uses local state `S₁` (over oracle `O₁`) into one
using the combined state `S₂ × S₁`, leaving the `S₂` component untouched and
threading `S₁` on the right. -/
def embedSnd {I₁ : Type} {O₁ : OracleSpec I₁} (S₂ S₁ : Type) :
    QueryImpl (withPMFAndStateSpec S₁ O₁) (OracleComp (withPMFAndStateSpec (S₂ × S₁) O₁)) := fun
  | .oracle i => OracleReduction.query i
  | .sample p => OracleReduction.sample p
  | .getState => Prod.snd <$> OracleReduction.get
  | .setState s1 => OracleReduction.modify (fun p => (p.1, s1))

/-- Interpret the operations available while answering a query of the outer
reduction `r2` (which live over `withPMFAndStateSpec S₂ O₂`) in terms of the
combined state `S₂ × r1.stateType` and the base oracle `O₁`, using `r1` to
answer the `O₂` queries. -/
def combineImpl {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (r1 : OracleReduction O₁ O₂) (S₂ : Type) :
    QueryImpl (withPMFAndStateSpec S₂ O₂)
      (OracleComp (withPMFAndStateSpec (S₂ × r1.stateType) O₁)) := fun
  | .oracle i => simulateQ (embedSnd S₂ r1.stateType) (r1.queries i)
  | .sample p => OracleReduction.sample p
  | .getState => Prod.fst <$> OracleReduction.get
  | .setState s2 => OracleReduction.modify (fun p => (s2, p.2))

/-- Compose two reductions: `r1 : O₁ → O₂` and `r2 : O₂ → O₃` give `O₁ → O₃`.
The combined state is `r2.stateType × r1.stateType`.  The initial state runs
`r1`'s initialization, then `r2`'s initialization with its `O₂` queries answered
by `r1`.  Each `O₃` query is answered by running `r2`'s query implementation with
its `O₂` queries answered by `r1`. -/
def rcompose {I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : OracleReduction O₁ O₂) (r2 : OracleReduction O₂ O₃) : OracleReduction O₁ O₃ where
  stateType := r2.stateType × r1.stateType
  initialState := r1.initialState >>= fun s1 =>
      simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r1.queries) r2.initialState) s1
  queries := fun i => simulateQ (combineImpl r1 r2.stateType) (r2.queries i)

/- # Lemma about composition of oracles
We prove that compostions (adversary, reduction1), reduction2 is equal to (adversary, (reduction1, reduction2))
Note that composing reduction with each other is an different operation then composing it with adversary.
-/

set_option maxHeartbeats 1000000 in -- large simp set over the free-monad induction
/-- Embedding a state-`S₁` computation into the combined state `S₂ × S₁` and
lowering with `defaultImpl` leaves the `S₂` component untouched and agrees with
lowering the original computation on the right component. Proved by induction. -/
lemma embedSnd_simulate {I₁ : Type} {O₁ : OracleSpec I₁} {S₂ S₁ Y : Type}
    (d : OracleComp (withPMFAndStateSpec S₁ O₁) Y) (s2 : S₂) (s1 : S₁) :
    simulateQ defaultImpl (simulateQ (embedSnd S₂ S₁) d) (s2, s1)
      = (fun w => (w.1, (s2, w.2))) <$> simulateQ defaultImpl d s1 := by
  induction d using OracleComp.inductionOn generalizing s1 s2 with
  | pure x => rfl
  | query_bind t oa ih =>
    cases t <;>
    · simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          embedSnd, addPMFtoImpl2, OracleSpec.query, OracleReduction.modify,
          OracleReduction.get, OracleReduction.set, ih]
      try rfl

set_option maxHeartbeats 4000000 in -- large free-monad induction with nested simp
/-- The key technical lemma: lowering the `combineImpl`-interpretation of a
computation `c` (over the combined state) equals first lowering `c` over `S₂`,
then running `r1` over the result, up to reassociating the state pair. Proved by
induction over `c`. -/
lemma combineImpl_simulate {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (r1 : OracleReduction O₁ O₂) {S₂ X : Type}
    (c : OracleComp (withPMFAndStateSpec S₂ O₂) X) (s2 : S₂) (s1 : r1.stateType) :
    simulateQ defaultImpl (simulateQ (combineImpl r1 S₂) c) (s2, s1)
      = (fun w => (w.1.1, (w.1.2, w.2))) <$>
          simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r1.queries)
            (simulateQ defaultImpl c s2)) s1 := by
  induction c using OracleComp.inductionOn generalizing s1 s2 with
  | pure x => rfl
  | query_bind t oa ih =>
    cases t with
    | oracle i =>
        simp only [combineImpl, simulateQ_roll, simulateQ_bind, simulateQ_query,
          OracleQuery.cont_query, id_map, id_eq]
        simp only [defaultImpl, OracleSpec.query, OracleQuery.query, OracleComp.queryBind]
        rw [statefulOracleComp_bind, embedSnd_simulate]
        simp only [StateT.lift, StateT.bind, StateT.run, bind_pure_comp, map_bind, bind_map,
          statefulOracleComp_bind, addPMFtoImpl2, simulateQ_bind, simulateQ_roll, simulateQ_map,
          simulateQ_pure, pure_bind, bind_assoc, Functor.map_map, Function.comp]
        simp only [ih]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
        apply bind_congr; intro a; rfl
    | sample p =>
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          combineImpl, addPMFtoImpl2, OracleSpec.query, OracleReduction.sample, ih]
        try rfl
    | getState =>
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          combineImpl, addPMFtoImpl2, OracleSpec.query, OracleReduction.get,
          OracleReduction.modify, OracleReduction.set, ih]
        try rfl
    | setState s =>
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          combineImpl, addPMFtoImpl2, OracleSpec.query, OracleReduction.get,
          OracleReduction.modify, OracleReduction.set, ih]
        try rfl

/-- Fusion: simulating with the composed reduction's queries equals simulating
with `r2`'s queries first and then `combineImpl`. Proved by induction. -/
lemma addPMF_compose_fusion {Output I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : OracleReduction O₁ O₂) (r2 : OracleReduction O₂ O₃)
    (dist : OracleComp (withPMFSpec O₃) Output) :
    simulateQ (addPMFtoImpl2 (rcompose r1 r2).queries) dist
      = simulateQ (combineImpl r1 r2.stateType) (simulateQ (addPMFtoImpl2 r2.queries) dist) := by
  induction dist using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    cases t with
    | oracle i =>
        simp only [simulateQ_roll, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, addPMFtoImpl2]
        rw [show (rcompose r1 r2).queries i
              = simulateQ (combineImpl r1 r2.stateType) (r2.queries i) from rfl]
        apply bind_congr; intro x; exact ih x
    | sample p =>
        simp only [simulateQ_roll, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, addPMFtoImpl2, combineImpl, OracleReduction.sample,
          OracleSpec.query]
        apply bind_congr; intro x; exact ih x

/-- Combining `addPMF_compose_fusion` and `combineImpl_simulate`. -/
lemma astep_compose {Output I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : OracleReduction O₁ O₂) (r2 : OracleReduction O₂ O₃)
    (dist : OracleComp (withPMFSpec O₃) Output) (s2 : r2.stateType) (s1 : r1.stateType) :
    simulateQ defaultImpl
        (simulateQ (addPMFtoImpl2 (rcompose r1 r2).queries) dist) (s2, s1)
      = (fun w => (w.1.1, (w.1.2, w.2))) <$>
          simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r1.queries)
            (simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r2.queries) dist) s2)) s1 := by
  rw [addPMF_compose_fusion]
  exact combineImpl_simulate r1 (simulateQ (addPMFtoImpl2 r2.queries) dist) s2 s1

set_option maxHeartbeats 1000000 in -- monad-homomorphism rewriting over the reduction state
/-- Applying the composed reduction to an adversary computation equals applying
`r2` and then `r1`. -/
lemma rcompose_apply {Output I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : OracleReduction O₁ O₂) (r2 : OracleReduction O₂ O₃)
    (dist : OracleComp (withPMFSpec O₃) Output) :
    applyReductionToAdversary (rcompose r1 r2) dist =
    applyReductionToAdversary r1 (applyReductionToAdversary r2 dist)
       := by
  simp only [applyReductionToAdversary]
  conv_lhs => rw [show (rcompose r1 r2).initialState
      = r1.initialState >>= fun s1 =>
          simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r1.queries) r2.initialState) s1 from rfl]
  simp only [bind_assoc, Functor.mapRev, simulateQ_bind, simulateQ_map, statefulOracleComp_bind,
    map_bind, bind_map, Functor.map_map, Function.comp, OracleReduction.lower_state_passing]
  apply bind_congr; intro s1
  apply bind_congr; intro a
  obtain ⟨s2, s1'⟩ := a
  rw [astep_compose]
  generalize simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r1.queries)
    (simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r2.queries) dist) s2)) = M
  simp only [map_eq_bind_pure_comp, statefulOracleComp_bind, statefulOracleComp_pure,
    bind_assoc, pure_bind, Function.comp]
  apply bind_congr; intro x; rfl
