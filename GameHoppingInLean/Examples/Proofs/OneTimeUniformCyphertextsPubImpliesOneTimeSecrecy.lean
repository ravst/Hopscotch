import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub

/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the left one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₀`. -/
def OTUCPubToOTSL {PubK M C : Type} :
    simpleReduction (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) where
  impl i t := match i, t with
    | IndCpaPubQ.getPk, () => otucPubGetPk
    | IndCpaPubQ.eavesdrop, (m₀, _m₁) => otucPubCtxt m₀

/-- Simple reduction from the single-message one-time uniform-ciphertexts public-key interface to the right one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₁`. -/
def OTUCPubToOTSR {PubK M C : Type} :
    simpleReduction (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C) where
  impl i t := match i, t with
    | IndCpaPubQ.getPk, () => otucPubGetPk
    | IndCpaPubQ.eavesdrop, (_m₀, m₁) => otucPubCtxt m₁

@[simp] lemma OTUCPubToOTSL_getPk {PubK M C : Type} :
    (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C)).impl
      IndCpaPubQ.getPk PUnit.unit =
    otucPubGetPk (PubK := PubK) (M := M) (C := C) := rfl

@[simp] lemma OTUCPubToOTSL_eavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C)).impl
      IndCpaPubQ.eavesdrop (m₀, m₁) =
    otucPubCtxt (PubK := PubK) (M := M) (C := C) m₀ := rfl

@[simp] lemma OTUCPubToOTSR_getPk {PubK M C : Type} :
    (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C)).impl
      IndCpaPubQ.getPk PUnit.unit =
    otucPubGetPk (PubK := PubK) (M := M) (C := C) := rfl

@[simp] lemma OTUCPubToOTSR_eavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C)).impl
      IndCpaPubQ.eavesdrop (m₀, m₁) =
    otucPubCtxt (PubK := PubK) (M := M) (C := C) m₁ := rfl

/-- `OTS_L` is observationally equivalent to applying the left reduction to the real
one-time uniform-ciphertexts public-key oracle. -/
theorem obsEq_otsL_apply_left_oneTimeUniformCyphertextsPubReal
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq (OneTimeSecrecyL scheme)
      (applySimpleReduction (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C))
        (OneTimeUniformCyphertextsPubReal scheme)) := by
  apply obsEqReflexive
  simp [OneTimeSecrecyL, OneTimeUniformCyphertextsPubReal, applySimpleReduction]
  ext1 α
  ext1 q
  cases α <;> cases q
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otucPubGetPk]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otucPubCtxt]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]

/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent because the message is ignored. -/
theorem obsEq_apply_left_oneTimeUniformCyphertextsPubRand_apply_right_oneTimeUniformCyphertextsPubRand
    {PubK SecK M C : Type} [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq
      (applySimpleReduction (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C))
        (OneTimeUniformCyphertextsPubRand scheme))
      (applySimpleReduction (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C))
        (OneTimeUniformCyphertextsPubRand scheme)) := by
  apply obsEqReflexive
  simp [OneTimeUniformCyphertextsPubRand, applySimpleReduction]
  ext1 α
  ext1 q
  cases α <;> cases q <;>
    simp [OracleComp.simulateQ, FreeMonad.mapM, otucPubGetPk, otucPubCtxt,
      FreeMonad.lift, query_impl_convert]

/-- Applying the right reduction to the real one-time uniform-ciphertexts public-key oracle is observationally equivalent to
the right OTS oracle. -/
theorem obsEq_apply_right_oneTimeUniformCyphertextsPubReal_otsR
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq
      (applySimpleReduction (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C))
        (OneTimeUniformCyphertextsPubReal scheme))
      (OneTimeSecrecyR scheme) := by
  apply obsEqReflexive
  simp [OneTimeSecrecyR, OneTimeUniformCyphertextsPubReal, applySimpleReduction]
  ext1 α
  ext1 q
  cases α <;> cases q
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otucPubGetPk]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otucPubCtxt]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]

/-- One-time secrecy follows from one-time uniform-ciphertexts public-key via the two simple reductions. -/
noncomputable def otucPubImpliesOTS
    {Reductions : IndistinguishabilityReductions}
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C)
    (hLeftRed : OTUCPubToOTSL (PubK := PubK) (M := M) (C := C) ∈
      Reductions.simpleReductions (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C))
    (hRightRed : OTUCPubToOTSR (PubK := PubK) (M := M) (C := C) ∈
      Reductions.simpleReductions (OneTimeUniformCyphertextsPubSpec PubK M C) (OneTimeSecrecySpec PubK M C))
    : OneTimeSecrecyDef (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions scheme := by
  intro κ
  have hRealRand :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeUniformCyphertextsPubSpec PubK M C)
        (OneTimeUniformCyphertextsPubReal scheme)
        (OneTimeUniformCyphertextsPubRand scheme) := by
    simpa [OneTimeUniformCyphertextsPubAssumption', OneTimeUniformCyphertextsPubAssumptionFull,
      OneTimeUniformCyphertextsPubAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := OneTimeUniformCyphertextsPubAssumption' scheme)
        (Reductions := Reductions) (κ := κ) (q_b := none) ())

  have hRandReal :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeUniformCyphertextsPubSpec PubK M C)
        (OneTimeUniformCyphertextsPubRand scheme)
        (OneTimeUniformCyphertextsPubReal scheme) :=
    IndistinguishableI.symm none hRealRand

  have h1 :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (OneTimeSecrecyL scheme)
        (applySimpleReduction (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubReal scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_otsL_apply_left_oneTimeUniformCyphertextsPubReal scheme)

  have h2 :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubReal scheme))
        (applySimpleReduction (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubRand scheme)) :=
    IndistinguishableI.simpleReduction
      (r := OTUCPubToOTSL (PubK := PubK) (M := M) (C := C)) none hRealRand hLeftRed

  have h3 :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTUCPubToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubRand scheme))
        (applySimpleReduction (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubRand scheme)) :=
    Indistinguishable.of_ObsEq
      (obsEq_apply_left_oneTimeUniformCyphertextsPubRand_apply_right_oneTimeUniformCyphertextsPubRand scheme)

  have h4 :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubRand scheme))
        (applySimpleReduction (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubReal scheme)) :=
    IndistinguishableI.simpleReduction
      (r := OTUCPubToOTSR (PubK := PubK) (M := M) (C := C)) none hRandReal hRightRed

  have h5 :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTUCPubToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeUniformCyphertextsPubReal scheme))
        (OneTimeSecrecyR scheme) :=
    Indistinguishable.of_ObsEq (obsEq_apply_right_oneTimeUniformCyphertextsPubReal_otsR scheme)

  have h :
      IndistinguishableI (OneTimeUniformCyphertextsPubAssumption' scheme) Reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (OneTimeSecrecyL scheme) (OneTimeSecrecyR scheme) :=
    Indistinguishable.transitive h1 <|
      Indistinguishable.transitive h2 <|
        Indistinguishable.transitive h3 <|
          Indistinguishable.transitive h4 h5

  simpa [OneTimeSecrecyDef] using h
