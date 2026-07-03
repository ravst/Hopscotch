import GameHoppingInLean.Examples.SecurityDefinitions.IndCpa
import GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.ComputationalIndistinguishibility.Defs

-- the proof that 'indCpaRand' definition imply 'indCpa'.

-- files:
-- * GameHoppingInLean.Examples.Schemes.SymEnc -- definition of Symetric encryption
-- * GameHoppingInLean.Examples.SecurityDefinitions.IndCpa -- definition 'IndCpa'
-- * GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand -- definition 'IndCpaRand'
-- * here - the proof of the implication.

open scoped OracleReduction

attribute [local game_hopping_unfold] IndCpaL IndCpaR IndCpaRandReal IndCpaRandRand

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
    IndCpaIFam (IndCpaRandAssumption' schemeFam) schemeFam := by
  intro κ
  game_hopping [
    IndCpaL (schemeFam.scheme κ),
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandReal (schemeFam.scheme κ)),
    (IndCpaRand_to_IndCpaL) ◇ (IndCpaRandRand (schemeFam.scheme κ)),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandRand (schemeFam.scheme κ)),
    (IndCpaRand_to_IndCpaR) ◇ (IndCpaRandReal (schemeFam.scheme κ)),
    IndCpaR (schemeFam.scheme κ)
  ]

noncomputable def proof_constants {K : ℕ → Type} {C : ℕ → ℕ → Type}
    (schemeFam : SymEncSchemeFamily K C)
    [∀ κ n, Fintype (C κ n)] [∀ κ n, Nonempty (C κ n)] (κ : ℕ)
    :=
    assumptionCounting_low (indCpaRandImpliesIndCpa schemeFam κ)

lemma stupidBoundRewrite {I : Type}
  {Assumptions : IndistinguishabilityAssumptions}
  {O : OracleSpec I}
  (x : AssumptionsUseT Assumptions O) :
  x = {subset := x.subset, values := (fun t => x.values t)} :=
    by simp


-- lemma empty_union (x : Finset X) [DecidableEq X] : x ∪ ∅ = x := by simp []
-- lemma union_empty (x : Finset X) [DecidableEq X] : ∅ ∪ x = x := by simp []

-- noncomputable def proof_constants_simp {K : ℕ → Type} {C : ℕ → ℕ → Type}
--     (schemeFam : SymEncSchemeFamily K C)
--     [∀ κ n, Fintype (C κ n)] [∀ κ n, Nonempty (C κ n)] (κ : ℕ)
--     : (proof_constants schemeFam κ).1.values = (fun x => sorry) := by
--   -- rw [stupidBoundRewrite (proof_constants schemeFam κ).1]
--   simp [indCpaRandImpliesIndCpa, proof_constants, IndCpaRandAssumption']
--   simp [transitive_step_val, assumptionJoiner, assumptionCounting_low,
--     sumJoiner, AssumptionsUseT.empty, finsetSum,
--     Indistinguishable.of_ObsEq, noAssumptionUse,
--     empty_union, union_empty
--   ]
--   funext x
--   simp [] at x
--   sorry
