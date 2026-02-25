import GameHoppingInLean.IndistinguishabilityDef

/-- Private-key encryption scheme with security parameter `κ`.
Keys are `κ`-bit strings, and encryption/decryption preserve message length by type. -/
structure PrivKeyEncryptionScheme (κ : ℕ) where
  keyGen : PMF (BitVec κ)
  encrypt : {n : ℕ} → BitVec κ → BitVec n → PMF (BitVec n)
  decrypt : {n : ℕ} → BitVec κ → BitVec n → BitVec n

/-- IND-CPA eavesdropping oracle spec.
The query indexed by `n` takes a pair of `n`-bit messages and returns an `n`-bit ciphertext. -/
def IndCpaSpec : OracleSpec ℕ :=
  fun n => (BitVec n × BitVec n, BitVec n)

/-- Convenience query constructor for the IND-CPA eavesdropping oracle. -/
@[reducible, inline] def eavesdrop {n : ℕ} (m₀ m₁ : BitVec n) : OracleComp IndCpaSpec (BitVec n) :=
  IndCpaSpec.query n (m₀, m₁)

/-- Left IND-CPA oracle: encrypts the left message `m₀`. -/
noncomputable def IndCpaL {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ) : RStateOracle IndCpaSpec where
  stateType := BitVec κ
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query n (m₀, _m₁) => fun key =>
          (fun c => (c, key)) <$> scheme.encrypt (n := n) key m₀
  }

/-- Right IND-CPA oracle: encrypts the right message `m₁`. -/
noncomputable def IndCpaR {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ) : RStateOracle IndCpaSpec where
  stateType := BitVec κ
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query n (_m₀, m₁) => fun key =>
          (fun c => (c, key)) <$> scheme.encrypt (n := n) key m₁
  }

/-- IND-CPA "real vs random ciphertext" oracle spec.
The query indexed by `n` takes a single `n`-bit message and returns an `n`-bit ciphertext. -/
def IndCpaRandSpec : OracleSpec ℕ :=
  fun n => (BitVec n, BitVec n)

/-- Convenience query constructor for the `ctxt(m)` oracle query. -/
@[reducible, inline] def ctxt {n : ℕ} (m : BitVec n) : OracleComp IndCpaRandSpec (BitVec n) :=
  IndCpaRandSpec.query n m

/-- IND-CPA "real ciphertext" oracle for the `ctxt(m)` interface. Returns `Enc_k(m)`. -/
noncomputable def IndCpaRandReal {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ) :
    RStateOracle IndCpaRandSpec where
  stateType := BitVec κ
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query n m => fun key =>
          (fun c => (c, key)) <$> scheme.encrypt (n := n) key m
  }

/-- IND-CPA "random ciphertext" oracle for the `ctxt(m)` interface.
Ignores the message and returns a uniformly random `n`-bit ciphertext. -/
noncomputable def IndCpaRandRand {κ : ℕ} (_enc : PrivKeyEncryptionScheme κ) :
    RStateOracle IndCpaRandSpec where
  stateType := Unit
  initialState := pure Unit.unit
  queries := {
    impl := fun
      | OracleSpec.query n _m => fun key =>
          (fun c => (c, key)) <$> PMF.uniformOfFintype (BitVec n)
  }

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
theorem obsEq_indCpaL_apply_left_real {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ) :
    ObsEq (IndCpaL scheme) (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandReal scheme)) := by
  apply obsEqReflexive
  simp [IndCpaL, IndCpaRandReal, applySimpleReduction]
  ext1 α; ext1 q
  cases q with
  | query n msg =>
      cases msg with
      | mk m₀ m₁ =>
          simp [OracleComp.simulateQ, FreeMonad.mapM, IndCpaRand_to_IndCpaL, ctxt]
          ext1 k
          congr
          simp [FreeMonad.lift]
          rfl


/-- Under the random ciphertext oracle, forwarding the left vs right challenge message is
observationally equivalent (the message is ignored). -/
theorem obsEq_apply_left_rand_apply_right_rand {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ) :
    ObsEq (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandRand scheme))
      (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandRand scheme)) := by
  apply obsEqReflexive
  simp [IndCpaRandRand, applySimpleReduction, OracleComp.simulateQ, IndCpaRand_to_IndCpaL, IndCpaRand_to_IndCpaR]
  funext α ⟨n, msg'⟩ s
  rfl

/-- Applying the right reduction to the real `ctxt` oracle is observationally equivalent to
`IND_CPA_R`. -/
theorem obsEq_apply_right_real_indCpaR {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ) :
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
          rfl

/-- IND-CPA left/right indistinguishability derived from indistinguishability of the
real-vs-random `ctxt` oracle, via the two simple reductions.

Uses symmetry to reverse the real-vs-random indistinguishability assumption when needed. -/
theorem indCpa_from_rand_oracle
    {Assumptions : IndistinguishabilityAssumptions}
    {SimpleReductions : IndistinguishabilitySimpleReductions}
    {Reductions : IndistinguishabilityReductions}
    {κ : ℕ} (scheme : PrivKeyEncryptionScheme κ)
    (hLeftRed : IndCpaRand_to_IndCpaL ∈ SimpleReductions IndCpaRandSpec IndCpaSpec)
    (hRightRed : IndCpaRand_to_IndCpaR ∈ SimpleReductions IndCpaRandSpec IndCpaSpec)
    (hRealRand :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaRandSpec (IndCpaRandReal scheme) (IndCpaRandRand scheme)) :
    Indistinguishable Assumptions SimpleReductions Reductions
      IndCpaSpec (IndCpaL scheme) (IndCpaR scheme) := by
  have hRandReal :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaRandSpec (IndCpaRandRand scheme) (IndCpaRandReal scheme) :=
    Indistinguishable.symm hRealRand

  have h1 :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaSpec (IndCpaL scheme)
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandReal scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_indCpaL_apply_left_real scheme)

  have h2 :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandReal scheme))
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandRand scheme)) :=
    Indistinguishable.simpleReduction (r := IndCpaRand_to_IndCpaL) hRealRand hLeftRed

  have h3 :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaL (IndCpaRandRand scheme))
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandRand scheme)) :=
    Indistinguishable.of_ObsEq (obsEq_apply_left_rand_apply_right_rand scheme)

  have h4 :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandRand scheme))
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandReal scheme)) :=
    Indistinguishable.simpleReduction (r := IndCpaRand_to_IndCpaR) hRandReal hRightRed

  have h5 :
      Indistinguishable Assumptions SimpleReductions Reductions
        IndCpaSpec
          (applySimpleReduction IndCpaRand_to_IndCpaR (IndCpaRandReal scheme))
          (IndCpaR scheme) :=
    Indistinguishable.of_ObsEq (obsEq_apply_right_real_indCpaR scheme)

  exact Indistinguishable.trans h1 <|
    Indistinguishable.trans h2 <|
      Indistinguishable.trans h3 <|
        Indistinguishable.trans h4 h5
