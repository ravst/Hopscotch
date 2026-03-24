import GameHoppingInLean.Examples.SecurityDefintions.OneTimeSecrecyRand

/-- Simple reduction from the single-message OTS-rand interface to the left one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₀`. -/
def OTSRandToOTSL {PubK M C : Type} :
    simpleReduction (OneTimeSecrecyRandSpec PubK M C) (OneTimeSecrecySpec PubK M C) where
  impl i t := match i, t with
    | OneTimeSecrecyQ.getPk, () => otsRandGetPk
    | OneTimeSecrecyQ.eavesdrop, (m₀, _m₁) => otsRandCtxt m₀

/-- Simple reduction from the single-message OTS-rand interface to the right one-time secrecy
oracle: on input `(m₀, m₁)` query the source oracle on `m₁`. -/
def OTSRandToOTSR {PubK M C : Type} :
    simpleReduction (OneTimeSecrecyRandSpec PubK M C) (OneTimeSecrecySpec PubK M C) where
  impl i t := match i, t with
    | OneTimeSecrecyQ.getPk, () => otsRandGetPk
    | OneTimeSecrecyQ.eavesdrop, (_m₀, m₁) => otsRandCtxt m₁

@[simp] lemma OTSRandToOTSL_getPk {PubK M C : Type} :
    (OTSRandToOTSL (PubK := PubK) (M := M) (C := C)).impl
      OneTimeSecrecyQ.getPk PUnit.unit =
    otsRandGetPk (PubK := PubK) (M := M) (C := C) := rfl

@[simp] lemma OTSRandToOTSL_eavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    (OTSRandToOTSL (PubK := PubK) (M := M) (C := C)).impl
      OneTimeSecrecyQ.eavesdrop (m₀, m₁) =
    otsRandCtxt (PubK := PubK) (M := M) (C := C) m₀ := rfl

@[simp] lemma OTSRandToOTSR_getPk {PubK M C : Type} :
    (OTSRandToOTSR (PubK := PubK) (M := M) (C := C)).impl
      OneTimeSecrecyQ.getPk PUnit.unit =
    otsRandGetPk (PubK := PubK) (M := M) (C := C) := rfl

@[simp] lemma OTSRandToOTSR_eavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    (OTSRandToOTSR (PubK := PubK) (M := M) (C := C)).impl
      OneTimeSecrecyQ.eavesdrop (m₀, m₁) =
    otsRandCtxt (PubK := PubK) (M := M) (C := C) m₁ := rfl

/-- `OTS_L` is observationally equivalent to applying the left reduction to the real
OTS-rand oracle. -/
theorem obsEq_otsL_apply_left_otsrReal
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq (OneTimeSecrecyL scheme)
      (applySimpleReduction (OTSRandToOTSL (PubK := PubK) (M := M) (C := C))
        (OneTimeSecrecyRandReal scheme)) := by
  apply obsEqReflexive
  simp [OneTimeSecrecyL, OneTimeSecrecyRandReal, applySimpleReduction]
  ext1 α
  ext1 q
  cases α <;> cases q
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otsRandGetPk]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otsRandCtxt]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]

/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent because the message is ignored. -/
theorem obsEq_apply_left_otsrRand_apply_right_otsrRand
    {PubK SecK M C : Type} [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq
      (applySimpleReduction (OTSRandToOTSL (PubK := PubK) (M := M) (C := C))
        (OneTimeSecrecyRandRand scheme))
      (applySimpleReduction (OTSRandToOTSR (PubK := PubK) (M := M) (C := C))
        (OneTimeSecrecyRandRand scheme)) := by
  apply obsEqReflexive
  simp [OneTimeSecrecyRandRand, applySimpleReduction]
  ext1 α
  ext1 q
  cases α <;> cases q <;>
    simp [OracleComp.simulateQ, FreeMonad.mapM, otsRandGetPk, otsRandCtxt,
      FreeMonad.lift, query_impl_convert]

/-- Applying the right reduction to the real OTS-rand oracle is observationally equivalent to
the right OTS oracle. -/
theorem obsEq_apply_right_otsrReal_otsR
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    ObsEq
      (applySimpleReduction (OTSRandToOTSR (PubK := PubK) (M := M) (C := C))
        (OneTimeSecrecyRandReal scheme))
      (OneTimeSecrecyR scheme) := by
  apply obsEqReflexive
  simp [OneTimeSecrecyR, OneTimeSecrecyRandReal, applySimpleReduction]
  ext1 α
  ext1 q
  cases α <;> cases q
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otsRandGetPk]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]
  · simp [OracleComp.simulateQ, FreeMonad.mapM, otsRandCtxt]
    ext1 s
    simp [FreeMonad.lift, query_impl_convert]

/-- One-time secrecy follows from one-time secrecy-rand via the two simple reductions. -/
theorem otsRandImpliesOTS
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C)
    (hLeftRed : OTSRandToOTSL (PubK := PubK) (M := M) (C := C) ∈
      Reductions.simpleReductions (OneTimeSecrecyRandSpec PubK M C) (OneTimeSecrecySpec PubK M C))
    (hRightRed : OTSRandToOTSR (PubK := PubK) (M := M) (C := C) ∈
      Reductions.simpleReductions (OneTimeSecrecyRandSpec PubK M C) (OneTimeSecrecySpec PubK M C))
    (hOTSRand : OneTimeSecrecyRandDef Assumptions Reductions scheme) :
    OneTimeSecrecyDef Assumptions Reductions scheme := by
  have hRealRand :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec PubK M C)
        (OneTimeSecrecyRandReal scheme)
        (OneTimeSecrecyRandRand scheme) := by
    simpa [OneTimeSecrecyRandDef] using hOTSRand

  have hRandReal :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec PubK M C)
        (OneTimeSecrecyRandRand scheme)
        (OneTimeSecrecyRandReal scheme) :=
    Indistinguishable.symm hRealRand

  have h1 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecySpec PubK M C)
        (OneTimeSecrecyL scheme)
        (applySimpleReduction (OTSRandToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandReal scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_otsL_apply_left_otsrReal scheme)

  have h2 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTSRandToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandReal scheme))
        (applySimpleReduction (OTSRandToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandRand scheme)) :=
    Indistinguishable.simpleReduction
      (r := OTSRandToOTSL (PubK := PubK) (M := M) (C := C)) hRealRand hLeftRed

  have h3 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTSRandToOTSL (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandRand scheme))
        (applySimpleReduction (OTSRandToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandRand scheme)) :=
    Indistinguishable.of_ObsEq
      (obsEq_apply_left_otsrRand_apply_right_otsrRand scheme)

  have h4 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTSRandToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandRand scheme))
        (applySimpleReduction (OTSRandToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandReal scheme)) :=
    Indistinguishable.simpleReduction
      (r := OTSRandToOTSR (PubK := PubK) (M := M) (C := C)) hRandReal hRightRed

  have h5 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecySpec PubK M C)
        (applySimpleReduction (OTSRandToOTSR (PubK := PubK) (M := M) (C := C))
          (OneTimeSecrecyRandReal scheme))
        (OneTimeSecrecyR scheme) :=
    Indistinguishable.of_ObsEq (obsEq_apply_right_otsrReal_otsR scheme)

  have h :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecySpec PubK M C)
        (OneTimeSecrecyL scheme) (OneTimeSecrecyR scheme) :=
    Indistinguishable.trans h1 <|
      Indistinguishable.trans h2 <|
        Indistinguishable.trans h3 <|
          Indistinguishable.trans h4 h5

  simpa [OneTimeSecrecyDef] using h
