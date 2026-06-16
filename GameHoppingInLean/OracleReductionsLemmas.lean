import GameHoppingInLean.OracleReductions
import GameHoppingInLean.Misc.SimpAttrLemmas

open OracleReduction

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
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
          identity, OracleSpec.query
        ]
        simp [bind, pure]

lemma applyComplexInitReduction2_identity {Output I : Type} {O : OracleSpec I}
  (dist : OracleComp (withPMFSpec O) Output)
  : applyReductionToAdversary (OracleReduction.identity O) dist = dist := by
  simp only [applyReductionToAdversary, OracleReduction.identity, pure_bind]
  have h := identity_roundtrip (O := O) dist ()
  simp only [OracleReduction.identity] at h
  rw [h]
  simp [Functor.map_map]


/-- Apply a reduction whose initialization may query the underlying oracle. -/
def ComplexInitReduction2_compose {I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : OracleReduction O₁ O₂) (r2 : OracleReduction O₂ O₃) : OracleReduction O₁ O₃ := by sorry

/-- Apply a reduction whose initialization may query the underlying oracle. -/
lemma ComplexInitReduction2_compose_apply {Output I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : OracleReduction O₁ O₂) (r2 : OracleReduction O₂ O₃)
    (dist : OracleComp (withPMFSpec O₃) Output) :
    applyReductionToAdversary (ComplexInitReduction2_compose r1 r2) dist =
    applyReductionToAdversary r1 (applyReductionToAdversary r2 dist)
       := by sorry
