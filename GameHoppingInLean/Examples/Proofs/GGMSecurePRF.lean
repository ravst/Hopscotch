import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRG
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF
import GameHoppingInLean.Examples.Constructions.GGM
import GameHoppingInLean.Examples.Misc.RF_caching

section
attribute [-simp] bind_pure_comp
open scoped IndistinguishableI

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

/-- The real GGM oracle is the first hybrid. -/
theorem obsEq_real_GGMHybrid_zero {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (PRF_real (GGM prg n)) (GGMHybrid prg 0) := by
  sorry

/-- The final GGM hybrid is the ideal random-function oracle. -/
theorem obsEq_GGMHybrid_last_ideal {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (GGMHybrid prg (Fin.last n)) (PRF_ideal (BitVec n) (BitVec k)) := by
  sorry


noncomputable def GGMHybrid2 {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec k)
  initialState := pure ∅
  queries := {
    impl := fun _ x => do
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let labels ← (do
        let state <- get
        match state.lookup nodeBits with
        | some x => return x
        | none =>
          let out <- PMF.uniformOfFintype (BitVec k)
          let state' := state.insert nodeBits out
          let _ <- set state'
          return out
        )
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg labels remainingBits)

  }


/-- Skeleton reduction for one adjacent hybrid step in the GGM proof.

The intended implementation should:
1. maintain a cache of labels for depth-`i+1` nodes,
2. query the underlying PRG challenger once per unseen depth-`i` prefix, and
3. interpret the challenge output as the two child labels for that prefix. -/
noncomputable def GGMHybridStepReduction2PRG {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    SRReduction (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k)) := by
  sorry

noncomputable def GGMHybridStepReduction2RF {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    SRReduction (SecurePRFSpec (BitVec i.1) (BitVec k)) (SecurePRFSpec (BitVec n) (BitVec k)) := by
  sorry




/-- Consecutive GGM hybrids differ by one use of the underlying PRG. -/
-- easy
theorem obsEq_GGMHybrid_reduction_rf {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    ObsEq (GGMHybrid prg i)
      (applySRReduction (GGMHybridStepReduction2RF prg i) (PRF_ideal (BitVec i.1) (BitVec k))) := by
  sorry

-- easy/medium
theorem obsEq_GGMHybrid2_reduction_rf {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    ObsEq (GGMHybrid2 prg i)
      (applySRReduction (GGMHybridStepReduction2RF prg i) (PRF_ideal2 (BitVec i.1) (BitVec k))) := by
  sorry

/-- Replacing the embedded PRG call with uniform randomness advances the hybrid by one level. -/
def obsEq_rand_GGMHybrid_1_2 {Reductions : IndistinguishabilityReductions} {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    (GGMHybridStepReduction2RF prg i ∈ Reductions.reductions _ _) ->
    Indistinguishable IndistinguishabilityAssumptions.empty Reductions
      (GGMHybrid prg i)
      (GGMHybrid2 prg i) := by
  -- by chatbot, from above
  sorry

-- easy, just definition
theorem obsEq_GGMHybrid2_applyStepReduction_real {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (GGMHybrid2 prg i.castSucc)
      (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg)) := by
  sorry

-- hard
theorem obsEq_applyStepReduction_rand_GGMHybrid2 {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k))
      (GGMHybrid2 prg i.succ) := by
  sorry




/-- One hybrid step is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def GGMHybrid2_step_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    (hRi : GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    -- (hRi2 : GGMHybridStepReduction2RF prg i.castSucc ∈ Reductions.reductions _ _)
    :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid2 prg i.castSucc)
      (GGMHybrid2 prg i.succ) := by
  intro κ
  let hLeft :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid2 prg i.castSucc)
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg)) :=
    Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_applyStepReduction_real prg i)
  let hPRG :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k k) (PRG_real prg) (PRG_rand k k) := by
    simpa [SecurePRGAssumption', SecurePRGAssumptionFull, SecurePRGAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := SecurePRGAssumption' prg)
        (Reductions := Reductions) (κ := κ) (q_b := none) ())
  let hMiddle :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg))
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k)) :=
    IndistinguishableI.reduction (r := GGMHybridStepReduction2PRG prg i) none hPRG hRi
  let hRight :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k))
        (GGMHybrid2 prg i.succ) :=
    Indistinguishable.of_ObsEq (obsEq_applyStepReduction_rand_GGMHybrid2 prg i)
  calc
    GGMHybrid2 prg i.castSucc
        ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg) := hLeft
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k) := hMiddle
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid2 prg i.succ := hRight

noncomputable def GGMHybrid_step_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    (hRi : GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    (hStep2 : ∀ i : Fin (n+1),
      GGMHybridStepReduction2RF prg i.castSucc ∈ Reductions.reductions _ _)
    :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid prg i.castSucc)
      (GGMHybrid prg i.succ) := by sorry

noncomputable def GGMHybrids_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k)
    (hStep : ∀ i : Fin n,
      GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    (hStep2 : ∀ i : Fin (n+1),
      GGMHybridStepReduction2RF prg i.castSucc ∈ Reductions.reductions _ _) :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid prg 0)
      (GGMHybrid prg (Fin.last n)) := by
  intro κ
  refine Indistinguishable.long_step n
    (fun j => GGMHybrid prg ⟨j.1, ?_⟩)
    (GGMHybrid prg 0)
    (GGMHybrid prg (Fin.last n))
    (by rfl)
    (by rfl)
    ?_
  · exact Finset.mem_range.mp j.2
  · intro i hi
    simp [ro_seq_fixed]
    exact GGMHybrid_step_indistinguishable_of_securePRG
      (Reductions := Reductions) prg ⟨i, hi⟩ (hStep ⟨i, hi⟩) hStep2 κ

-- /-- Skeleton proof of GGM security from security of the underlying length-doubling PRG.

-- The remaining work is to chain the `n` hybrid steps between the two endpoint observational
-- equivalences, for example via `IndistinguishableI.longSequence` or an induction on `n`. -/
-- noncomputable def secureGGM_of_securePRG
--     {Reductions : IndistinguishabilityReductions}
--     {k n : ℕ} (prg : lengthDoublingPRG k)
--     (hStep : ∀ i : Fin n,
--       GGMHybridStepReduction prg i ∈
--         Reductions.reductions (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k))) :
--     SecurePRFDef (SecurePRGAssumption' prg) Reductions (GGM prg n) := by
--   intro κ
--   calc
--     PRF_real (GGM prg n)
--         ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
--             SecurePRFSpec (BitVec n) (BitVec k)]
--       GGMHybrid prg 0 :=
--         Indistinguishable.of_ObsEq (obsEq_real_GGMHybrid_zero prg)
--     _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
--             SecurePRFSpec (BitVec n) (BitVec k)]
--       GGMHybrid prg (Fin.last n) :=
--         (GGMHybrids_indistinguishable_of_securePRG
--           (Reductions := Reductions) prg hStep) κ
--     _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
--             SecurePRFSpec (BitVec n) (BitVec k)]
--       PRF_ideal (BitVec n) (BitVec k) :=
--         Indistinguishable.of_ObsEq (obsEq_GGMHybrid_last_ideal prg)

-- end
