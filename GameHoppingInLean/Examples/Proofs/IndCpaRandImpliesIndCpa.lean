import GameHoppingInLean.Examples.SecurityDefinitions.IndCpa
import GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand
import GameHoppingInLean.IndistinguishabilityTactics

-- the proof that 'indCpaRand' definition imply 'indCpa'.

-- files:
-- * GameHoppingInLean.Examples.Schemes.SymEnc -- definition of Symetric encryption
-- * GameHoppingInLean.Examples.SecurityDefinitions.IndCpa -- definition 'IndCpa'
-- * GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand -- definition 'IndCpaRand'
-- * here - the proof of the implication.

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
noncomputable def indCpaRandImpliesIndCpa (schemeFam : SymEncSchemeFamily)
    [∀ κ n, Fintype (schemeFam.C κ n)] [∀ κ n, Nonempty (schemeFam.C κ n)]
    :
    IndCpaIFam (IndCpaRandAssumption' schemeFam) schemeFam := by
  intro κ
  -- TODO: line below breaks proof :-(
  -- generalize (schemeFam.scheme κ) = scheme
  game_hopping [
    IndCpaL (schemeFam.scheme κ),
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandReal (schemeFam.scheme κ)),
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandRand (schemeFam.scheme κ)),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandRand (schemeFam.scheme κ)),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandReal (schemeFam.scheme κ)),
    IndCpaR (schemeFam.scheme κ)
  ]
  · sorry
  · sorry
