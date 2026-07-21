import Hopscotch.Examples.SecurityDefinitions.OneTimeUniformCiphertextsPub
import Hopscotch.Tactic.SimpAttrLemmas
import Hopscotch.Tactic.Defs


open scoped OracleReduction


/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the left one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₀`. -/
def OTUCPubToOTSL {PubK M C : Type} :
    OracleReduction (OneTimeUniformCiphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) := {
  stateType := Unit
  initialState := pure ()
  queries t := match t with
    | IndCpaPubQ.getPk => orQuery(OneTimeUniformCiphertextsPubQ.getPk)
    | IndCpaPubQ.eavesdrop (m₀, _m₁) => orQuery(OneTimeUniformCiphertextsPubQ.eavesdrop m₀)
    }

/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the right one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₁`. -/
def OTUCPubToOTSR {PubK M C : Type} :
    OracleReduction (OneTimeUniformCiphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) := {
  stateType := Unit
  initialState := pure PUnit.unit
  queries t := match t with
    | IndCpaPubQ.getPk => orQuery(OneTimeUniformCiphertextsPubQ.getPk)
    | IndCpaPubQ.eavesdrop (_m₀, m₁) => orQuery(OneTimeUniformCiphertextsPubQ.eavesdrop m₁)
    }

attribute [local game_hopping_unfold] OneTimeSecrecyL OneTimeUniformCiphertextsPubReal OTUCPubToOTSL OneTimeSecrecyL OneTimeSecrecyR OTUCPubToOTSR OneTimeUniformCiphertextsPubRand

/-- One-time secrecy follows from one-time uniform-ciphertexts public-key via the two simple reductions. -/
noncomputable def otucPubImpliesOTS
    {PubK SecK M C : ℕ -> Type} [forall κ, Fintype (C κ)] [forall κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C)
    : OneTimeSecrecyIFam (OneTimeUniformCiphertextsPubAssumptionFam schemeFam) schemeFam := by
  intro κ
  simp [OneTimeUniformCiphertextsPubAssumptionFam]
  generalize schemeFam.scheme κ = schemek
  game_hopping [
    (OneTimeSecrecyL schemek),
    OTUCPubToOTSL ◇ (OneTimeUniformCiphertextsPubReal schemek),
    OTUCPubToOTSL ◇ (OneTimeUniformCiphertextsPubRand schemek),
    OTUCPubToOTSR ◇ (OneTimeUniformCiphertextsPubRand schemek),
    OTUCPubToOTSR ◇ (OneTimeUniformCiphertextsPubReal schemek),
    (OneTimeSecrecyR schemek)
  ]
