import GameHoppingInLean.Examples.SecurityDefinitions.IndCpa
import GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand
import GameHoppingInLean.Misc.SimpAttrLemmas

local notation:50 x " ≈ᵢ'[" Assumptions ", " κ ", " q_b ", " O "] " y =>
  IndistinguishableI Assumptions κ q_b O x y

/-- Simple reduction from the single-message `ctxt` oracle to the left IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₀)`. -/
def IndCpaRand_to_IndCpaL {C : ℕ → Type} : OracleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, (m₀, _m₁)⟩ =>
    OracleReduction.query (IndCpaRandDomain.ctxt n m₀)

/-- Simple reduction from the single-message `ctxt` oracle to the right IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₁)`. -/
def IndCpaRand_to_IndCpaR {C : ℕ → Type} : OracleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, (_m₀, m₁)⟩ =>
    OracleReduction.query (IndCpaRandDomain.ctxt n m₁)

/-- `IND_CPA_L` is observationally equivalent to applying the left reduction to
the real `ctxt` oracle. -/
theorem obsEq_indCpaL_apply_left_real {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    ObsEq (IndCpaL scheme)
      (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme)) := by
  apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
  solveCorrectAbstraction [IndCpaL, IndCpaRand_to_IndCpaL, IndCpaRandReal]

/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent (the message is ignored). -/
theorem obsEq_apply_left_rand_apply_right_rand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    ObsEq (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme))
      (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme)) := by
  apply correctAbstractionImpliesObsEq _ _ (fun x => x)
  solveCorrectAbstraction [IndCpaRand_to_IndCpaL, IndCpaRandRand]

/-- Applying the right reduction to the real `ctxt` oracle is observationally equivalent to
`IND_CPA_R`. -/
theorem obsEq_apply_right_real_indCpaR {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    ObsEq (OracleReduction.apply (IndCpaRand_to_IndCpaR) (IndCpaRandReal scheme))
      (IndCpaR scheme) := by
  symm
  apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
  solveCorrectAbstraction [IndCpaR, IndCpaRand_to_IndCpaR, IndCpaRandReal]

/-- IND-CPA left/right indistinguishability derived from IND-CPA-rand indistinguishability,
via the two simple reductions. -/
noncomputable def indCpaRandImpliesIndCpa
    {K : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (scheme : SymEncScheme K C) :
    IndCpaDef (IndCpaRandAssumption' scheme) scheme := by
  intro κ
  have hRealRand :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaRandSpec C) (IndCpaRandReal scheme) (IndCpaRandRand scheme) := by
    simpa [IndCpaRandAssumption', IndCpaRandAssumptionFull, IndCpaRandAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := IndCpaRandAssumption' scheme)
        (κ := κ) (q_b := none) ())

  have hRandReal :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaRandSpec C) (IndCpaRandRand scheme) (IndCpaRandReal scheme) :=
    IndistinguishableI.symm none hRealRand

  calc
    IndCpaL scheme
        ≈ᵢ'[IndCpaRandAssumption' scheme, κ, none, IndCpaSpec C]
        OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme) := by
          exact Indistinguishable.of_ObsEq (obsEq_indCpaL_apply_left_real scheme)
    _ ≈ᵢ'[IndCpaRandAssumption' scheme, κ, none, IndCpaSpec C]
        OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme) := by
          exact IndistinguishableI.complexInitReduction
            (IndCpaRand_to_IndCpaL (C := C)) none hRealRand
    _ ≈ᵢ'[IndCpaRandAssumption' scheme, κ, none, IndCpaSpec C]
        OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme) := by
          exact Indistinguishable.of_ObsEq (obsEq_apply_left_rand_apply_right_rand scheme)
    _ ≈ᵢ'[IndCpaRandAssumption' scheme, κ, none, IndCpaSpec C]
        OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme) := by
          exact IndistinguishableI.complexInitReduction
            (IndCpaRand_to_IndCpaR (C := C)) none hRandReal
    _ ≈ᵢ'[IndCpaRandAssumption' scheme, κ, none, IndCpaSpec C]
        IndCpaR scheme := by
          exact Indistinguishable.of_ObsEq (obsEq_apply_right_real_indCpaR scheme)
