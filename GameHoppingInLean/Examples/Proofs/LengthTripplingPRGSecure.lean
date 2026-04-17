import GameHoppingInLean.Examples.SecurityDefintions.SecurePRG
import GameHoppingInLean.Examples.Constructions.LengthTripplingPRG

section
attribute [-simp] bind_pure_comp

/-- `R1`: from secure-PRG game on `2k` output to secure-PRG game on `3k` output.
On query, ask inner oracle for a `2k`-bit string `x || y`, then return `x || prg.draw y`. -/
def PRGDouble_to_Tripple_R1 {k : ℕ} (prg : lengthDoublingPRG k) :
    RReduction (SecurePRGSpec k k) (SecurePRGSpec k (2 * k)) where
  impl _ _ := do
        let xy ← RReduction.query () ()
        let x : BitVec k := BitVec.extractLsb' k k xy
        let y : BitVec k := BitVec.extractLsb' 0 k xy
        let dy : BitVec (2 * k) := cast (by simp [two_mul]) (prg.draw y)
        pure (BitVec.append x dy)

/-- `R2`: from secure-PRG game on `2k` output to secure-PRG game on `3k` output.
On query, sample random `k` bits `x`, query inner oracle for `y : BitVec (2k)`,
and return `x || y`. -/
noncomputable def PRGDouble_to_Tripple_R2 {k : ℕ} :
    RReduction (SecurePRGSpec k k) (SecurePRGSpec k (2 * k)) where
  impl _ _ := do
        let x ← RReduction.sample (PMF.uniformOfFintype (BitVec k))
        let y : BitVec (k + k) ← RReduction.query () ()
        let y' : BitVec (2 * k) := cast (by simp [two_mul]) y
        pure (BitVec.append x y')

/-- Explicit game `G1`: sample uniform `xy : BitVec (2k)`, split as `x || y`,
return `x || prg.draw y`. -/
noncomputable def PRG_G1 {k : ℕ} (prg : lengthDoublingPRG k) :
    RStateOracle (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun  _ _ => do
          let xy ← PMF.uniformOfFintype (BitVec (k + k))
          let x : BitVec k := BitVec.extractLsb' k k xy
          let y : BitVec k := BitVec.extractLsb' 0 k xy
          let dy : BitVec (2 * k) := cast (by simp [two_mul]) (prg.draw y)
          pure (BitVec.append x dy)
  }

/-- Explicit game `G2`: sample independent uniform `x,y : BitVec k`,
return `x || prg.draw y`. -/
noncomputable def PRG_G2 {k : ℕ} (prg : lengthDoublingPRG k) :
    RStateOracle (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun  _ _ => do
          let x ← PMF.uniformOfFintype (BitVec k)
          let y ← PMF.uniformOfFintype (BitVec k)
          let dy : BitVec (2 * k) := cast (by simp [two_mul]) (prg.draw y)
          pure (BitVec.append x dy)
  }

/-- Explicit game `G3`: sample independent uniform `x : BitVec k` and
`y : BitVec (2k)`, return `x || y`. -/
noncomputable def PRG_G3 {k : ℕ} :
    RStateOracle (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun  _ _ => do
          let x ← PMF.uniformOfFintype (BitVec k)
          let y ← PMF.uniformOfFintype (BitVec (2 * k))
          pure (BitVec.append x y)
  }

/-- `PRG_real(3k)` is observationally equivalent to `PRG_real(2k)` composed with `R1`. -/
theorem obsEq_prgRealTripple_applyR1_realDouble {k : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (PRG_real (LengthTrippingPRG prg))
      (applyRReduction (PRGDouble_to_Tripple_R1 prg) (PRG_real prg)) := by
  apply obsEqReflexive
  simp[PRG_real, applyRReduction]
  funext α x
  cases x
  -- case query =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, LengthTrippingPRG, PRGDouble_to_Tripple_R1, addPMFtoImpl]



/-- `PRG_rand(2k)` composed with `R1` is observationally equivalent to `G1`. -/
theorem obsEq_applyR1_randDouble_G1 {k : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (applyRReduction (PRGDouble_to_Tripple_R1 prg) (PRG_rand k k)) (PRG_G1 prg) := by
  apply obsEqReflexive
  simp[PRG_real, PRG_G1, PRG_rand, applyRReduction]
  funext α x
  cases x
  -- case query =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, LengthTrippingPRG, PRGDouble_to_Tripple_R1, addPMFtoImpl]



/-- `G1` is observationally equivalent to `G2`. -/
theorem obsEq_G1_G2 {k : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (PRG_G1 prg) (PRG_G2 prg) := by
  apply obsEqReflexive
  simp[PRG_real, PRG_G1, PRG_G2, applyRReduction]



/-- `G2` is observationally equivalent to `PRG_real(2k)` composed with `R2`. -/
theorem obsEq_G2_applyR2_realDouble {k : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (PRG_G2 prg) (applyRReduction (PRGDouble_to_Tripple_R2 (k := k)) (PRG_real prg)) := by
  apply obsEqReflexive
  simp[PRG_real, PRG_G2, PRGDouble_to_Tripple_R2, applyRReduction]
  funext α x
  cases x
  -- case query =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, LengthTrippingPRG, PRGDouble_to_Tripple_R1, addPMFtoImpl]

/-- `PRG_rand(2k)` composed with `R2` is observationally equivalent to `G3`. -/
theorem obsEq_applyR2_randDouble_G3 {k : ℕ} :
    ObsEq (applyRReduction (PRGDouble_to_Tripple_R2 (k := k)) (PRG_rand k k)) (PRG_G3 (k := k)) := by
  apply obsEqReflexive
  simp[PRG_real, PRG_G3, PRGDouble_to_Tripple_R2, PRG_rand, applyRReduction]
  funext α x
  cases x
  -- case query =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, LengthTrippingPRG, PRGDouble_to_Tripple_R1, addPMFtoImpl]


/-- `G3` is observationally equivalent to `PRG_rand(3k)`. -/
theorem obsEq_G3_prgRandTripple {k : ℕ} :
    ObsEq (PRG_G3 (k := k)) (PRG_rand k (2 * k)) := by
  apply obsEqReflexive
  simp[PRG_real, PRG_G3, PRGDouble_to_Tripple_R2, PRG_rand, applyRReduction]

/-- Security of the length-tripling construction from security of the length-doubling PRG,
via reductions `R1` and `R2`. -/
noncomputable def secureLengthTrippling_of_secureLengthDoubling
    {Reductions : IndistinguishabilityReductions}
    {k : ℕ} (prg : lengthDoublingPRG k)
    (hR1 : PRGDouble_to_Tripple_R1 prg ∈
      Reductions.randomReductions (SecurePRGSpec k k) (SecurePRGSpec k (2 * k)))
    (hR2 : PRGDouble_to_Tripple_R2 (k := k) ∈
      Reductions.randomReductions (SecurePRGSpec k k) (SecurePRGSpec k (2 * k)))
    : SecurePRGDef (SecurePRGAssumption' prg) Reductions (LengthTrippingPRG prg) := by
  intro κ
  have hRealRandDouble :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k k) (PRG_real prg) (PRG_rand k k) := by
    simpa [SecurePRGAssumption', SecurePRGAssumptionFull, SecurePRGAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := SecurePRGAssumption' prg)
        (Reductions := Reductions) (κ := κ) (q_b := none) ())

  have h1 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (PRG_real (LengthTrippingPRG prg))
        (applyRReduction (PRGDouble_to_Tripple_R1 prg) (PRG_real prg)) :=
    by
      apply Indistinguishable.of_ObsEq (obsEq_prgRealTripple_applyR1_realDouble prg)

  have h2 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (applyRReduction (PRGDouble_to_Tripple_R1 prg) (PRG_real prg))
        (applyRReduction (PRGDouble_to_Tripple_R1 prg) (PRG_rand k k)) :=
  by
    apply IndistinguishableI.randReduction (r := PRGDouble_to_Tripple_R1 prg) none hRealRandDouble hR1

  have h3 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (applyRReduction (PRGDouble_to_Tripple_R1 prg) (PRG_rand k k))
        (PRG_G1 prg) :=
    Indistinguishable.of_ObsEq (obsEq_applyR1_randDouble_G1 prg)

  have h4 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (PRG_G1 prg) (PRG_G2 prg) :=
    Indistinguishable.of_ObsEq (obsEq_G1_G2 prg)

  have h5 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (PRG_G2 prg)
        (applyRReduction (PRGDouble_to_Tripple_R2 (k := k)) (PRG_real prg)) :=
    Indistinguishable.of_ObsEq (obsEq_G2_applyR2_realDouble prg)

  have h6 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (applyRReduction (PRGDouble_to_Tripple_R2 (k := k)) (PRG_real prg))
        (applyRReduction (PRGDouble_to_Tripple_R2 (k := k)) (PRG_rand k k)) :=
    IndistinguishableI.randReduction (r := PRGDouble_to_Tripple_R2 (k := k)) none hRealRandDouble hR2

  have h7 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (applyRReduction (PRGDouble_to_Tripple_R2 (k := k)) (PRG_rand k k))
        (PRG_G3 (k := k)) :=
    Indistinguishable.of_ObsEq (obsEq_applyR2_randDouble_G3 (k := k))

  have h8 :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (PRG_G3 (k := k)) (PRG_rand k (2 * k)) :=
    Indistinguishable.of_ObsEq (obsEq_G3_prgRandTripple (k := k))

  have h :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k (2 * k))
        (PRG_real (LengthTrippingPRG prg)) (PRG_rand k (2 * k)) :=
    Indistinguishable.transitive h1 <|
      Indistinguishable.transitive h2 <|
        Indistinguishable.transitive h3 <|
          Indistinguishable.transitive h4 <|
            Indistinguishable.transitive h5 <|
              Indistinguishable.transitive h6 <|
                Indistinguishable.transitive h7 h8

  simpa [SecurePRGDef] using h


end
