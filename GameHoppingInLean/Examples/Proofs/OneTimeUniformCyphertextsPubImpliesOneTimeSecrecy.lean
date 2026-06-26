import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub
import GameHoppingInLean.Misc.SimpAttrLemmas
import GameHoppingInLean.IndistinguishabilityTactics


open scoped OracleReduction


/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the left one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₀`. -/
def OTUCPubToOTSL {PubK M C : Type} :
    OracleReduction (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) := {
  stateType := Unit
  initialState := pure PUnit.unit
  queries t := match t with
    | IndCpaPubQ.getPk => do
      let x <- orQuery(.getPk)
      by
        simp [OneTimeUniformCyphertextsPubSpec] at x
        exact return x
    | IndCpaPubQ.eavesdrop (m₀, _m₁) => do
      let x <- orQuery(.eavesdrop m₀)
      by
        simp [OneTimeUniformCyphertextsPubSpec] at x
        exact return x
    }

/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the right one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₁`. -/
def OTUCPubToOTSR {PubK M C : Type} :
    OracleReduction (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) := {
  stateType := Unit
  initialState := pure PUnit.unit
  queries t := match t with
    | IndCpaPubQ.getPk => do
      let x <- orQuery(.getPk)
      by
        simp [OneTimeUniformCyphertextsPubSpec] at x
        exact return x
    | IndCpaPubQ.eavesdrop (_m₀, m₁) => do
      let x <- orQuery(.eavesdrop m₁)
      by
        simp [OneTimeUniformCyphertextsPubSpec] at x
        exact return x
    }


attribute [local game_hopping_unfold] OneTimeSecrecyL OneTimeUniformCyphertextsPubReal OTUCPubToOTSL OneTimeSecrecyL OneTimeSecrecyR OTUCPubToOTSR OneTimeUniformCyphertextsPubRand

/-- `OTS_L` is observationally equivalent to applying the left reduction to the real
one-time uniform-ciphertexts public-key oracle. -/
theorem obsEq_otsL_apply_left_oneTimeUniformCyphertextsPubReal
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq (OneTimeSecrecyL scheme)
      ((OTUCPubToOTSL (PubK := PubK) (M := M) (C := C)) ◇
        (OneTimeUniformCyphertextsPubReal scheme)) := by
  apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
  solveCorrectAbstraction []
  case neg =>
    simp_all


/-- Applying the right reduction to the real one-time uniform-ciphertexts public-key oracle is observationally equivalent to
the right OTS oracle. -/
theorem obsEq_apply_right_oneTimeUniformCyphertextsPubReal_otsR
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq
      ((OTUCPubToOTSR (PubK := PubK) (M := M) (C := C)) ◇
        (OneTimeUniformCyphertextsPubReal scheme))
      (OneTimeSecrecyR scheme) := by
  symm
  apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
  solveCorrectAbstraction []
  case neg =>
    simp_all

/-- One-time secrecy follows from one-time uniform-ciphertexts public-key via the two simple reductions. -/
noncomputable def otucPubImpliesOTS
    -- {Reductions : IndistinguishabilityReductions}
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C)
    -- (hLeftRed : OTUCPubToOTSL (PubK := PubK) (M := M) (C := C) ∈
    --   Reductions.simpleReductions (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C))
    -- (hRightRed : OTUCPubToOTSR (PubK := PubK) (M := M) (C := C) ∈
    --   Reductions.simpleReductions (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C))
    : OneTimeSecrecyDef (OneTimeUniformCyphertextsPubAssumption' scheme) scheme := by
  intro κ
  game_hopping [
    (OneTimeSecrecyL scheme),
    (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C)) ◇
        (OneTimeUniformCyphertextsPubReal scheme),
    (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C)) ◇
        (OneTimeUniformCyphertextsPubRand scheme),
    (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C)) ◇
        (OneTimeUniformCyphertextsPubRand scheme),
    (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C)) ◇
        (OneTimeUniformCyphertextsPubReal scheme),
    (OneTimeSecrecyR scheme)
  ]
  · apply Indistinguishable.of_ObsEq
    apply obsEq_otsL_apply_left_oneTimeUniformCyphertextsPubReal
  · apply Indistinguishable.of_ObsEq
    apply obsEq_apply_right_oneTimeUniformCyphertextsPubReal_otsR
