import GameHoppingInLean.Examples.SecurityDefintions.OTUC
import GameHoppingInLean.Examples.Constructions.DoubleSymEnc
import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.PMFLiftOrder


/-- `R1`: reduction from inner-OTUC (`T`) to outer-OTUC (`Double(S,T)`).
On query `m`, sample an `S` key, encrypt with `S`, then delegate to the input OTUC oracle. -/
noncomputable def OUTCInner_to_OUTCDouble_R1 {K₁ : Type} {C : ℕ → Type}
    (S : SymEncScheme K₁ BitVec) : RReduction (OTUCSpec C) (OTUCSpec C) where
  impl := fun
    | OracleSpec.query n m => do
        let ks ← RReduction.sample S.keyGen
        let m' ← RReduction.sample (S.encrypt ks m)
        RReduction.query n m'

/-- Explicit intermediate game `G1`:
sample an `S` key, encrypt the message with `S`, ignore that result, and output random ciphertext. -/
noncomputable def OUTC_G1 {K₁ K₂ : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (S : SymEncScheme K₁ BitVec) (_T : SymEncScheme K₂ C) :
    RStateOracle (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun n m => do
          let ks ← S.keyGen
          let _m' ← S.encrypt ks m
          let c ← PMF.uniformOfFintype (C n)
          pure c
  }

/-- `OTUC_Real(Double(S,T))` is observationally equivalent to `OTUC_Real(T)` composed with `R1`. -/
theorem obsEq_outcRealDouble_applyR1_realT
    {K₁ K₂ : Type} {C : ℕ → Type} (S : SymEncScheme K₁ BitVec) (T : SymEncScheme K₂ C) :
    ObsEq (OTUC_Real (doubleSymEnc S T))
      (applyRReduction (OUTCInner_to_OUTCDouble_R1 S) (OTUC_Real T)) := by
  apply obsEqReflexive
  simp [OTUC_Real, applyRReduction]
  ext1 α; ext1 q;
  cases q
  -- case query i msg =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, OUTCInner_to_OUTCDouble_R1, FreeMonad.lift,
    doubleSymEnc]
  rfl


/-- `OTUC_Rand(T)` composed with `R1` is observationally equivalent to explicit game `G1`. -/
theorem obsEq_applyR1_randT_G1
    {K₁ K₂ : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (S : SymEncScheme K₁ BitVec) (T : SymEncScheme K₂ C) :
    ObsEq (applyRReduction (OUTCInner_to_OUTCDouble_R1 S) (OTUC_Rand T)) (OUTC_G1 S T) := by
  apply obsEqReflexive
  simp [OUTCInner_to_OUTCDouble_R1, OUTC_G1, applyRReduction, OTUC_Rand]
  ext1 α; ext1 q
  cases q
  -- case query i msg =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, OUTCInner_to_OUTCDouble_R1, FreeMonad.lift, doubleSymEnc]

/-- `G1` is observationally equivalent to `OTUC_Rand(Double(S,T))`. -/
theorem obsEq_G1_outcRandDouble
    {K₁ K₂ : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (S : SymEncScheme K₁ BitVec) (T : SymEncScheme K₂ C) :
    ObsEq (OUTC_G1 S T) (OTUC_Rand (doubleSymEnc S T)) := by
  apply obsEqReflexive
  simp [OUTCInner_to_OUTCDouble_R1, OUTC_G1, applyRReduction, OTUC_Rand]

/-- OUTC/OTUC of inner scheme `T` implies OUTC/OTUC of `Double(S,T)`, via reduction `R1`. -/
theorem outcInnerImpliesOutcDouble
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {K₁ K₂ : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (S : SymEncScheme K₁ BitVec) (T : SymEncScheme K₂ C)
    (hR1 : OUTCInner_to_OUTCDouble_R1 S ∈
      Reductions.randomReductions (OTUCSpec C) (OTUCSpec C))
    (hOutcT : OTUCDef Assumptions Reductions T) :
    OTUCDef Assumptions Reductions (doubleSymEnc S T) := by
  have hRealRandT :
      Indistinguishable Assumptions Reductions
        (OTUCSpec C) (OTUC_Real T) (OTUC_Rand T) := by
    simpa [OTUCDef] using hOutcT

  have h1 :
      Indistinguishable Assumptions Reductions
        (OTUCSpec C) (OTUC_Real (doubleSymEnc S T))
          (applyRReduction (OUTCInner_to_OUTCDouble_R1 S) (OTUC_Real T)) :=
    Indistinguishable.of_ObsEq (obsEq_outcRealDouble_applyR1_realT S T)

  have h2 :
      Indistinguishable Assumptions Reductions
        (OTUCSpec C)
          (applyRReduction (OUTCInner_to_OUTCDouble_R1 S) (OTUC_Real T))
          (applyRReduction (OUTCInner_to_OUTCDouble_R1 S) (OTUC_Rand T)) :=
    Indistinguishable.randReduction (r := OUTCInner_to_OUTCDouble_R1 S) hRealRandT hR1

  have h3 :
      Indistinguishable Assumptions Reductions
        (OTUCSpec C)
          (applyRReduction (OUTCInner_to_OUTCDouble_R1 S) (OTUC_Rand T))
          (OUTC_G1 S T) :=
    Indistinguishable.of_ObsEq (obsEq_applyR1_randT_G1 S T)

  have h4 :
      Indistinguishable Assumptions Reductions
        (OTUCSpec C) (OUTC_G1 S T) (OTUC_Rand (doubleSymEnc S T)) :=
    Indistinguishable.of_ObsEq (obsEq_G1_outcRandDouble S T)

  have h :
      Indistinguishable Assumptions Reductions
        (OTUCSpec C) (OTUC_Real (doubleSymEnc S T)) (OTUC_Rand (doubleSymEnc S T)) :=
    Indistinguishable.trans h1 <|
      Indistinguishable.trans h2 <|
        Indistinguishable.trans h3 h4

  simpa [OTUCDef] using h
