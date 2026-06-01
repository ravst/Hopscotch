import GameHoppingInLean.Examples.SecurityDefinitions.IndCpa
import GameHoppingInLean.Examples.SecurityDefinitions.IndCpaRand
import GameHoppingInLean.OracleReductions

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
  constructor
  · simp [IndCpaL, IndCpaRand_to_IndCpaL, IndCpaRandReal, OracleReduction.apply, StateT.run, simulateQ, PFunctor.FreeM.mapM, PMF.map]
    congr
  · intro query
    cases query
    case eavesdrop n m =>
    ext1 st
    simp [IndCpaL, IndCpaRand_to_IndCpaL, IndCpaRandReal]
    simp [OracleReduction.apply, OracleComp.instMonadLiftOracleQuery._aux_1, simulateQ, OracleReduction.query,
      PFunctor.FreeM.mapM, liftM, monadLift, MonadLift.monadLift]
    simp [OracleReduction.liftWithPMFAndState]
    simp [mapInputState, mapOutputState, mapSecond, PMF.map]
    simp [StateT.lift, StateT.run, StateT.get]
    congr

/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent (the message is ignored). -/
theorem obsEq_apply_left_rand_apply_right_rand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    ObsEq (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme))
      (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme)) := by
  apply obsEqReflexive
  simp [IndCpaRandRand, IndCpaRand_to_IndCpaL, IndCpaRand_to_IndCpaR]
  simp [OracleReduction.apply, OracleComp.instMonadLiftOracleQuery._aux_1, simulateQ, OracleReduction.query,
      PFunctor.FreeM.mapM, liftM, monadLift, MonadLift.monadLift]
  simp [OracleReduction.liftWithPMFAndState]
  congr

/-- Applying the right reduction to the real `ctxt` oracle is observationally equivalent to
`IND_CPA_R`. -/
theorem obsEq_apply_right_real_indCpaR {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    ObsEq (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme))
      (IndCpaR scheme) := by
  apply ObsEq.symm
  apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
  constructor
  · simp [IndCpaR, IndCpaRand_to_IndCpaR, IndCpaRandReal, OracleReduction.apply, StateT.run, simulateQ, PFunctor.FreeM.mapM, PMF.map]
    congr
  · intro query
    cases query
    case eavesdrop n m =>
    ext1 st
    simp [IndCpaR, IndCpaRand_to_IndCpaR, IndCpaRandReal]
    simp [OracleReduction.apply, OracleComp.instMonadLiftOracleQuery._aux_1, simulateQ, OracleReduction.query,
      PFunctor.FreeM.mapM, liftM, monadLift, MonadLift.monadLift]
    simp [OracleReduction.liftWithPMFAndState]
    simp [mapInputState, mapOutputState, mapSecond, PMF.map]
    simp [StateT.lift, StateT.run, StateT.get]
    congr

/-- IND-CPA left/right indistinguishability derived from IND-CPA-rand indistinguishability,
via the two simple reductions. -/
noncomputable def indCpaRandImpliesIndCpa
    {K : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (scheme : SymEncScheme K C)
    : IndCpaDef (IndCpaRandAssumption' scheme) scheme := by
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

  have h1 :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaSpec C) (IndCpaL scheme)
          (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_indCpaL_apply_left_real scheme)

  have h2 :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaSpec C)
          (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme))
          (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme)) :=
    IndistinguishableI.complexInitReduction _ _ hRealRand

  have h3 :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaSpec C)
          (OracleReduction.apply (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme))
          (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_apply_left_rand_apply_right_rand scheme)

  have h4 :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaSpec C)
          (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme))
          (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme)) :=
    IndistinguishableI.complexInitReduction _ _ hRandReal

  have h5 :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaSpec C)
          (OracleReduction.apply (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme))
          (IndCpaR scheme) :=
    Indistinguishable.of_ObsEq (obsEq_apply_right_real_indCpaR scheme)

  have h :
      IndistinguishableI (IndCpaRandAssumption' scheme) κ none
        (IndCpaSpec C) (IndCpaL scheme) (IndCpaR scheme) :=
    Indistinguishable.transitive h1 <|
      Indistinguishable.transitive h2 <|
        Indistinguishable.transitive h3 <|
          Indistinguishable.transitive h4 h5

  simpa [IndCpaDef] using h
