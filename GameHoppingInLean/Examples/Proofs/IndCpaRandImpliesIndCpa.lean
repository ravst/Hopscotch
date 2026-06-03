import GameHoppingInLean.Examples.SecurityDefinitions.IndCpa
import GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand
import GameHoppingInLean.IndistinguishabilityTactics

open scoped OracleReduction

/-- Simple reduction from the single-message `ctxt` oracle to the left IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₀)`. -/
@[game_hopping_unfold]
def IndCpaRand_to_IndCpaL {C : ℕ → Type} : OracleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, (m₀, _m₁)⟩ =>
    OracleReduction.query (IndCpaRandDomain.ctxt n m₀)

/-- Simple reduction from the single-message `ctxt` oracle to the right IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₁)`. -/
@[game_hopping_unfold]
def IndCpaRand_to_IndCpaR {C : ℕ → Type} : OracleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, (_m₀, m₁)⟩ =>
    OracleReduction.query (IndCpaRandDomain.ctxt n m₁)

/-- IND-CPA left/right indistinguishability derived from IND-CPA-rand indistinguishability,
via the two simple reductions. -/
noncomputable def indCpaRandImpliesIndCpa
    {K : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (scheme : SymEncScheme K C) :
    IndCpaDef (IndCpaRandAssumption' scheme) scheme := by
  intro κ
  game_hopping [
    IndCpaL scheme,
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandReal scheme),
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandRand scheme),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandRand scheme),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandReal scheme),
    IndCpaR scheme
  ]
