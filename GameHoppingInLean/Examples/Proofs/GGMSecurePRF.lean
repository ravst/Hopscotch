import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRG
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF
import GameHoppingInLean.Examples.Constructions.GGM

section
attribute [-simp] bind_pure_comp

/-- The `i`-th hybrid for the GGM proof.

The oracle samples a uniformly random label for every depth-`i` node in the GGM tree.
On input `x`, it reads the first `i` bits in the same LSB-first order used by `applyPRGs`,
looks up the corresponding random label, and then evaluates the remaining suffix with `prg`. -/
noncomputable def GGMHybrid {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := BitVec i.1 → BitVec k
  initialState := PMF.uniformOfFintype (BitVec i.1 → BitVec k)
  queries := {
    impl := fun _ x => do
      let labels ← get
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg (labels nodeBits) remainingBits)
  }

/-- Skeleton reduction for one adjacent hybrid step in the GGM proof.

The intended implementation should:
1. maintain a cache of labels for depth-`i+1` nodes,
2. query the underlying PRG challenger once per unseen depth-`i` prefix, and
3. interpret the challenge output as the two child labels for that prefix. -/
noncomputable def GGMHybridStepReduction {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    SRReduction (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k)) := by
  sorry

/-- The real GGM oracle is the first hybrid. -/
theorem obsEq_real_GGMHybrid_zero {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (PRF_real (GGM prg n)) (GGMHybrid prg 0) := by
  sorry

/-- Consecutive GGM hybrids differ by one use of the underlying PRG. -/
theorem obsEq_GGMHybrid_applyStepReduction_real {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (GGMHybrid prg i.castSucc)
      (applySRReduction (GGMHybridStepReduction prg i) (PRG_real prg)) := by
  sorry

/-- Replacing the embedded PRG call with uniform randomness advances the hybrid by one level. -/
theorem obsEq_applyStepReduction_rand_GGMHybrid {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (applySRReduction (GGMHybridStepReduction prg i) (PRG_rand k k))
      (GGMHybrid prg i.succ) := by
  sorry

/-- The final GGM hybrid is the ideal random-function oracle. -/
theorem obsEq_GGMHybrid_last_ideal {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (GGMHybrid prg (Fin.last n)) (PRF_ideal (BitVec n) (BitVec k)) := by
  sorry

/-- One hybrid step is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def GGMHybrid_step_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    (hRi : GGMHybridStepReduction prg i ∈
      Reductions.reductions (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k))) :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (SecurePRFSpec (BitVec n) (BitVec k))
      (GGMHybrid prg i.castSucc)
      (GGMHybrid prg i.succ) := by
  intro κ
  have hPRG :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k k) (PRG_real prg) (PRG_rand k k) := by
    simpa [SecurePRGAssumption', SecurePRGAssumptionFull, SecurePRGAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := SecurePRGAssumption' prg)
        (Reductions := Reductions) (κ := κ) (q_b := none) ())

  have hRed :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction prg i) (PRG_real prg))
        (applySRReduction (GGMHybridStepReduction prg i) (PRG_rand k k)) :=
    IndistinguishableI.reduction (r := GGMHybridStepReduction prg i) none hPRG hRi

  have hLeft :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid prg i.castSucc)
        (applySRReduction (GGMHybridStepReduction prg i) (PRG_real prg)) :=
    Indistinguishable.of_ObsEq (obsEq_GGMHybrid_applyStepReduction_real prg i)

  have hRight :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction prg i) (PRG_rand k k))
        (GGMHybrid prg i.succ) :=
    Indistinguishable.of_ObsEq (obsEq_applyStepReduction_rand_GGMHybrid prg i)

  exact Indistinguishable.transitive hLeft <|
    Indistinguishable.transitive hRed hRight

/-- Skeleton proof of GGM security from security of the underlying length-doubling PRG.

The remaining work is to chain the `n` hybrid steps between the two endpoint observational
equivalences, for example via `IndistinguishableI.longSequence` or an induction on `n`. -/
noncomputable def secureGGM_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k)
    (hStep : ∀ i : Fin n,
      GGMHybridStepReduction prg i ∈
        Reductions.reductions (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k))) :
    SecurePRFDef (SecurePRGAssumption' prg) Reductions (GGM prg n) := by
  intro κ

  have hStart :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (PRF_real (GGM prg n))
        (GGMHybrid prg 0) :=
    Indistinguishable.of_ObsEq (obsEq_real_GGMHybrid_zero prg)

  have hMiddle :
      ∀ i : Fin n,
        IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
          (SecurePRFSpec (BitVec n) (BitVec k))
          (GGMHybrid prg i.castSucc)
          (GGMHybrid prg i.succ) := by
    intro i
    exact GGMHybrid_step_indistinguishable_of_securePRG
      (Reductions := Reductions) prg i (hStep i) κ

  have hEnd :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid prg (Fin.last n))
        (PRF_ideal (BitVec n) (BitVec k)) :=
    Indistinguishable.of_ObsEq (obsEq_GGMHybrid_last_ideal prg)

  -- TODO: chain `hStart`, all instances of `hMiddle`, and `hEnd`.
  sorry

end
