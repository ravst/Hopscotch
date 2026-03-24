import GameHoppingInLean.Examples.SecurityDefintions.IndCpa
import GameHoppingInLean.Examples.SecurityDefintions.IndCpaRand

/-- Simple reduction from the single-message `ctxt` oracle to the left IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₀)`. -/
def IndCpaRand_to_IndCpaL {C : ℕ → Type} : simpleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  impl n t := match n, t with
    | _n, (m₀, _m₁) => ctxt (C := C) m₀

/-- Simple reduction from the single-message `ctxt` oracle to the right IND-CPA oracle:
on input `(m₀, m₁)` query `ctxt(m₁)`. -/
def IndCpaRand_to_IndCpaR {C : ℕ → Type} : simpleReduction (IndCpaRandSpec C) (IndCpaSpec C) where
  impl n t := match n, t with
    | _n, (_m₀, m₁) => ctxt (C := C) m₁

/-- `IND_CPA_L` is observationally equivalent to applying the left reduction to
the real `ctxt` oracle. -/
theorem obsEq_indCpaL_apply_left_real {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    ObsEq (IndCpaL scheme)
      (applySimpleReduction (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme)) := by
  apply obsEqReflexive
  simp [IndCpaL, IndCpaRandReal, applySimpleReduction]
  ext1 α; ext1 q
  cases q
  -- case query n msg =>
  -- cases msg
  case  mk m₀ m₁ =>
  simp [OracleComp.simulateQ, FreeMonad.mapM, IndCpaRand_to_IndCpaL, ctxt]
  ext1 k
  simp [FreeMonad.lift]

/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent (the message is ignored). -/
theorem obsEq_apply_left_rand_apply_right_rand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    ObsEq (applySimpleReduction (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme))
      (applySimpleReduction (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme)) := by
  apply obsEqReflexive
  simp [IndCpaRandRand, applySimpleReduction, OracleComp.simulateQ, IndCpaRand_to_IndCpaL,
    IndCpaRand_to_IndCpaR]
  funext α ⟨n, msg'⟩ s
  rfl

/-- Applying the right reduction to the real `ctxt` oracle is observationally equivalent to
`IND_CPA_R`. -/
theorem obsEq_apply_right_real_indCpaR {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    ObsEq (applySimpleReduction (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme))
      (IndCpaR scheme) := by
  apply obsEqReflexive
  simp [IndCpaR, IndCpaRandReal, applySimpleReduction]
  ext1 α; ext1 q
  cases q with
  | mk m₀ m₁ =>
    simp [OracleComp.simulateQ, FreeMonad.mapM, IndCpaRand_to_IndCpaR, ctxt]
    ext1 k
    congr
    simp [FreeMonad.lift]
  -- | hEq =>
  --

/-- IND-CPA left/right indistinguishability derived from IND-CPA-rand indistinguishability,
via the two simple reductions. -/
theorem indCpaRandImpliesIndCpa
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {K : Type} {C : ℕ → Type} [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (scheme : SymEncScheme K C)
    (hLeftRed : (IndCpaRand_to_IndCpaL (C := C)) ∈
      Reductions.simpleReductions (IndCpaRandSpec C) (IndCpaSpec C))
    (hRightRed : (IndCpaRand_to_IndCpaR (C := C)) ∈
      Reductions.simpleReductions (IndCpaRandSpec C) (IndCpaSpec C))
    (hIndCpaRand : IndCpaRandDef Assumptions Reductions scheme) :
    IndCpaDef Assumptions Reductions scheme := by
  have hRealRand :
      Indistinguishable Assumptions Reductions
        (IndCpaRandSpec C) (IndCpaRandReal scheme) (IndCpaRandRand scheme) := by
    simpa [IndCpaRandDef] using hIndCpaRand

  have hRandReal :
      Indistinguishable Assumptions Reductions
        (IndCpaRandSpec C) (IndCpaRandRand scheme) (IndCpaRandReal scheme) :=
    Indistinguishable.symm hRealRand

  have h1 :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec C) (IndCpaL scheme)
          (applySimpleReduction (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_indCpaL_apply_left_real scheme)

  have h2 :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec C)
          (applySimpleReduction (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandReal scheme))
          (applySimpleReduction (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme)) :=
    Indistinguishable.simpleReduction (r := IndCpaRand_to_IndCpaL (C := C)) hRealRand hLeftRed

  have h3 :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec C)
          (applySimpleReduction (IndCpaRand_to_IndCpaL (C := C)) (IndCpaRandRand scheme))
          (applySimpleReduction (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_apply_left_rand_apply_right_rand scheme)

  have h4 :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec C)
          (applySimpleReduction (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandRand scheme))
          (applySimpleReduction (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme)) :=
    Indistinguishable.simpleReduction (r := IndCpaRand_to_IndCpaR (C := C)) hRandReal hRightRed

  have h5 :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec C)
          (applySimpleReduction (IndCpaRand_to_IndCpaR (C := C)) (IndCpaRandReal scheme))
          (IndCpaR scheme) :=
    Indistinguishable.of_ObsEq (obsEq_apply_right_real_indCpaR scheme)

  have h :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec C) (IndCpaL scheme) (IndCpaR scheme) :=
    Indistinguishable.trans h1 <|
      Indistinguishable.trans h2 <|
        Indistinguishable.trans h3 <|
          Indistinguishable.trans h4 h5

  simpa [IndCpaDef] using h
