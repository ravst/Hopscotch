import Hopscotch.Examples.SecurityDefinitions.IndCpa
import Hopscotch.Examples.SecurityDefinitions.IndCpaRand
import Hopscotch.Tactic.Defs
import Hopscotch.ComputationalIndistinguishability.AssumptionCounting

-- the proof that 'indCpaRand' definition implies 'indCpa'.

-- files:
-- * Hopscotch.Examples.Schemes.SymEnc -- definition of Symmetric encryption
-- * Hopscotch.Examples.SecurityDefinitions.IndCpa -- definition 'IndCpa'
-- * Hopscotch.Examples.SecurityDefinitions.IndCpaRand -- definition 'IndCpaRand'
-- * here - the proof of the implication.

open scoped OracleReduction

attribute [local game_hopping_unfold] IndCpaL IndCpaR IndCpaLFam IndCpaRFam IndCpaRandReal IndCpaRandRand

/-- Simple reduction from the single-message `ctxt` oracle to the left IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₀)`. -/
@[local game_hopping_unfold]
def IndCpaRand_to_IndCpaL {C : ℕ → Type} : OracleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, (m₀, _m₁)⟩ =>
    OracleReduction.query (IndCpaRandDomain.ctxt n m₀)

/-- Simple reduction from the single-message `ctxt` oracle to the right IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₁)`. -/
@[local game_hopping_unfold]
def IndCpaRand_to_IndCpaR {C : ℕ → Type} : OracleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, (_m₀, m₁)⟩ =>
    OracleReduction.query (IndCpaRandDomain.ctxt n m₁)

/-- IND-CPA left/right indistinguishability derived from IND-CPA-rand indistinguishability,
via the two simple reductions. -/
noncomputable def indCpaRandImpliesIndCpa {K : ℕ → Type} {C : ℕ → ℕ → Type}
    (schemeFam : SymEncSchemeFamily K C)
    [∀ κ n, Fintype (C κ n)] [∀ κ n, Nonempty (C κ n)]
    :
    Indistinguishable
      (IndCpaRandAssumptionFam schemeFam)
      (IndCpaLFam schemeFam)
      (IndCpaRFam schemeFam) := by
  intro κ
  let Enc := schemeFam.scheme κ
  game_hopping [
    IndCpaL Enc,
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandReal Enc),
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandRand Enc),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandRand Enc),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandReal Enc),
    IndCpaR Enc
  ]


/-- how to see bounds that we proved? The best way it to write
"assumptionCounting (indCpaRandImpliesIndCpa schemeFam κ) = sorry"
and then to simplify as below. Do not simplify reduction names!
Then replace sorry with resulting term. -/
noncomputable def proof_constants_simp {K : ℕ → Type} {C : ℕ → ℕ → Type}
    (schemeFam : SymEncSchemeFamily K C)
    [∀ κ n, Fintype (C κ n)] [∀ κ n, Nonempty (C κ n)] (κ : ℕ)
    :
    assumptionCounting (indCpaRandImpliesIndCpa schemeFam κ) =
    (fun _x ↦
      [rcompose
        (OracleReduction.identity (IndCpaRandSpec (C κ)))
        IndCpaRand_to_IndCpaL]
    , fun _x ↦
      [rcompose
        (OracleReduction.identity (IndCpaRandSpec (C κ)))
        IndCpaRand_to_IndCpaR]
  ) := by
  simp [indCpaRandImpliesIndCpa, IndCpaRandAssumptionFam]
  simp [transitive_step_val_simple, assumptionCounting,
    Indistinguishable.of_ObsEq,
  ]
