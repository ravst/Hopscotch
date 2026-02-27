import GameHoppingInLean.Examples.SecurityDefintions.IndCpa
import GameHoppingInLean.Examples.SecurityDefintions.IndCpaRand

/-- Simple reduction from the single-message `ctxt` oracle to the left IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₀)`. -/
def IndCpaRand_to_IndCpaL : simpleReduction IndCpaRandSpec IndCpaSpec where
  impl := fun
    | OracleSpec.query _n (m₀, _m₁) => ctxt m₀

/-- Simple reduction from the single-message `ctxt` oracle to the right IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₁)`. -/
def IndCpaRand_to_IndCpaR : simpleReduction IndCpaRandSpec IndCpaSpec where
  impl := fun
    | OracleSpec.query _n (_m₀, m₁) => ctxt m₁

/-- `IND_CPA_L` is observationally equivalent to applying the left reduction to
the real `ctxt` oracle. -/
theorem obsEq_indCpaL_apply_left_real {K : Type} (scheme : SymEncScheme K) :
    ObsEq (IndCpaL scheme) (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandReal scheme)) := by
  apply obsEqReflexive
  simp [IndCpaL, IndCpaRandReal, applySimpleReduction]
  ext1 α; ext1 q
  cases q
  case query n msg =>
  cases msg
  case  mk m₀ m₁ =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, IndCpaRand_to_IndCpaL, ctxt]
  ext1 k
  simp [FreeMonad.lift]

/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent (the message is ignored). -/
theorem obsEq_apply_left_rand_apply_right_rand {K : Type} (scheme : SymEncScheme K) :
    ObsEq (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandRand scheme))
      (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandRand scheme)) := by
  apply obsEqReflexive
  simp [IndCpaRandRand, applySimpleReduction, OracleComp.simulateQ, IndCpaRand_to_IndCpaL, IndCpaRand_to_IndCpaR]
  funext α ⟨n, msg'⟩ s
  rfl

/-- Applying the right reduction to the real `ctxt` oracle is observationally equivalent to
`IND_CPA_R`. -/
theorem obsEq_apply_right_real_indCpaR {K : Type} (scheme : SymEncScheme K) :
    ObsEq (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandReal scheme)) (IndCpaR scheme) := by
  apply obsEqReflexive
  simp [IndCpaR, IndCpaRandReal, applySimpleReduction]
  ext1 α; ext1 q
  cases q with
  | query n msg =>
      cases msg with
      | mk m₀ m₁ =>
          simp [OracleComp.simulateQ, FreeMonad.mapM, IndCpaRand_to_IndCpaR, ctxt]
          ext1 k
          congr
          simp [FreeMonad.lift]

/-- IND-CPA left/right indistinguishability derived from IND-CPA-rand indistinguishability,
via the two simple reductions. -/
theorem indCpaRandImpliesIndCpa
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {K : Type} (scheme : SymEncScheme K)
    (hLeftRed : IndCpaRand_to_IndCpaL ∈ Reductions.simpleReductions IndCpaRandSpec IndCpaSpec)
    (hRightRed : IndCpaRand_to_IndCpaR ∈ Reductions.simpleReductions IndCpaRandSpec IndCpaSpec)
    (hIndCpaRand : IndCpaRandDef Assumptions Reductions scheme) :
    IndCpaDef Assumptions Reductions scheme := by
  have hRealRand :
      Indistinguishable Assumptions Reductions
        IndCpaRandSpec (IndCpaRandReal scheme) (IndCpaRandRand scheme) := by
    simpa [IndCpaRandDef] using hIndCpaRand

  have hRandReal :
      Indistinguishable Assumptions Reductions
        IndCpaRandSpec (IndCpaRandRand scheme) (IndCpaRandReal scheme) :=
    Indistinguishable.symm hRealRand

  have h1 :
      Indistinguishable Assumptions Reductions
        IndCpaSpec (IndCpaL scheme)
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandReal scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_indCpaL_apply_left_real scheme)

  have h2 :
      Indistinguishable Assumptions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandReal scheme))
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandRand scheme)) :=
    Indistinguishable.simpleReduction (r := IndCpaRand_to_IndCpaL) hRealRand hLeftRed

  have h3 :
      Indistinguishable Assumptions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandRand scheme))
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandRand scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_apply_left_rand_apply_right_rand scheme)

  have h4 :
      Indistinguishable Assumptions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandRand scheme))
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandReal scheme)) :=
    Indistinguishable.simpleReduction (r := IndCpaRand_to_IndCpaR) hRandReal hRightRed

  have h5 :
      Indistinguishable Assumptions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandReal scheme))
          (IndCpaR scheme) :=
    Indistinguishable.of_ObsEq (obsEq_apply_right_real_indCpaR scheme)

  have h :
      Indistinguishable Assumptions Reductions
        IndCpaSpec (IndCpaL scheme) (IndCpaR scheme) :=
    Indistinguishable.trans h1 <|
      Indistinguishable.trans h2 <|
        Indistinguishable.trans h3 <|
          Indistinguishable.trans h4 h5

  simpa [IndCpaDef] using h
