import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub
import GameHoppingInLean.Tactic.SimpAttrLemmas
import GameHoppingInLean.Tactic.Defs


open scoped OracleReduction


/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the left one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₀`. -/
def OTUCPubToOTSL {PubK M C : Type} :
    OracleReduction (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) := {
  stateType := Unit
  initialState := pure ()
  queries t := match t with
    | IndCpaPubQ.getPk => orQuery(OneTimeUniformCyphertextsPubQ.getPk)
    | IndCpaPubQ.eavesdrop (m₀, _m₁) => orQuery(OneTimeUniformCyphertextsPubQ.eavesdrop m₀)
    }

/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the right one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₁`. -/
def OTUCPubToOTSR {PubK M C : Type} :
    OracleReduction (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) := {
  stateType := Unit
  initialState := pure PUnit.unit
  queries t := match t with
    | IndCpaPubQ.getPk => orQuery(OneTimeUniformCyphertextsPubQ.getPk)
    | IndCpaPubQ.eavesdrop (_m₀, m₁) => orQuery(OneTimeUniformCyphertextsPubQ.eavesdrop m₁)
    }

attribute [local game_hopping_unfold] OneTimeSecrecyL OneTimeUniformCyphertextsPubReal OTUCPubToOTSL OneTimeSecrecyL OneTimeSecrecyR OTUCPubToOTSR OneTimeUniformCyphertextsPubRand

/-- One-time secrecy follows from one-time uniform-ciphertexts public-key via the two simple reductions. -/
noncomputable def otucPubImpliesOTS
    {PubK SecK M C : ℕ -> Type} [forall κ, Fintype (C κ)] [forall κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C)
    : OneTimeSecrecyIFam (OneTimeUniformCyphertextsPubAssumptionFam schemeFam) schemeFam := by
  intro κ
  simp [OneTimeUniformCyphertextsPubAssumptionFam]
  generalize schemeFam.scheme κ = schemek
  game_hopping [
    (OneTimeSecrecyL schemek),
    OTUCPubToOTSL ◇ (OneTimeUniformCyphertextsPubReal schemek),
    OTUCPubToOTSL ◇ (OneTimeUniformCyphertextsPubRand schemek),
    OTUCPubToOTSR ◇ (OneTimeUniformCyphertextsPubRand schemek),
    OTUCPubToOTSR ◇ (OneTimeUniformCyphertextsPubReal schemek),
    (OneTimeSecrecyR schemek)
  ]
