import GameHoppingInLean.Examples.SecurityDefintions.IndCca
import GameHoppingInLean.Examples.SecurityDefintions.IndCpa
import GameHoppingInLean.Examples.SecurityDefintions.MACUnforgeability
import GameHoppingInLean.Examples.Constructions.EncryptThenMac

abbrev EtMC (Tag : Type) (n : ℕ) := BitVec n × Tag
abbrev EtMSpec (Tag : Type) : OracleSpec IndCcaQ :=
  IndCcaSpec (fun n => EtMC Tag n)
abbrev EtMCiphertext (Tag : Type) :=
  IndCcaCiphertext (fun n => EtMC Tag n)

/-- Local state for EtM reductions that use encryption and track issued challenge ciphertexts. -/
structure EtMFromMacState (KEnc Tag : Type) where
  encKey : KEnc
  seen : Finset (EtMCiphertext Tag)

/-- Local state for the IND-CPA-to-EtM reduction: MAC key and seen challenge ciphertexts. -/
structure EtMFromIndCpaState (KMac Tag : Type) where
  macKey : KMac
  seen : Finset (EtMCiphertext Tag)

/-- Reduction from MAC-unforgeability oracle to the IND-CCA left game for Encrypt-then-MAC.
It delegates tagging/checking to the MAC oracle while keeping encryption state locally. -/
noncomputable def EtMFromMACLReduction {KEnc Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) :
    SRReduction (MACUFSpec Tag) (EtMSpec Tag) where
  stateType := EtMFromMacState KEnc Tag
  initialState := do
    let ke ← enc.keyGen
    pure { encKey := ke, seen := ∅ }
  queries := {
    impl := fun
      | OracleSpec.query (IndCcaQ.eavesdrop n) (m₀, _m₁) => do
          let st ← SRReduction.get
          let c ← SRReduction.sample (enc.encrypt st.encKey m₀)
          let t ← SRReduction.query (MACUFQ.getTag n) c
          SRReduction.set { st with seen := insert (⟨n, (c, t)⟩ : EtMCiphertext Tag) st.seen }
          pure (c, t)
      | OracleSpec.query (IndCcaQ.decrypt n) ct => do
          let st ← SRReduction.get
          if (ct : EtMCiphertext Tag) ∈ st.seen then
            pure none
          else
            let b : Bool ← SRReduction.query (MACUFQ.checkTag n) ct
            if b then
              pure (some (enc.decrypt st.encKey ct.1))
            else
              pure (some (BitVec.zero n))
  }

/-- Reduction from MAC-unforgeability oracle to the IND-CCA right game for Encrypt-then-MAC.
It is symmetric to `EtMFromMACLReduction`, using the right message in eavesdrop queries. -/
noncomputable def EtMFromMACRReduction {KEnc Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) :
    SRReduction (MACUFSpec Tag) (EtMSpec Tag) where
  stateType := EtMFromMacState KEnc Tag
  initialState := do
    let ke ← enc.keyGen
    pure { encKey := ke, seen := ∅ }
  queries := {
    impl := fun
      | OracleSpec.query (IndCcaQ.eavesdrop n) (_m₀, m₁) => do
          let st ← SRReduction.get
          let c ← SRReduction.sample (enc.encrypt st.encKey m₁)
          let t ← SRReduction.query (MACUFQ.getTag n) c
          SRReduction.set { st with seen := insert (⟨n, (c, t)⟩ : EtMCiphertext Tag) st.seen }
          pure (c, t)
      | OracleSpec.query (IndCcaQ.decrypt n) ct => do
          let st ← SRReduction.get
          if (ct : EtMCiphertext Tag) ∈ st.seen then
            pure none
          else
            let b : Bool ← SRReduction.query (MACUFQ.checkTag n) ct
            if b then
              pure (some (enc.decrypt st.encKey ct.1))
            else
              pure (some (BitVec.zero n))
  }

/-- Reduction from IND-CPA left/right games to an IND-CCA-style EtM game whose decrypt oracle
returns `none` on challenge ciphertexts and zero otherwise. -/
noncomputable def EtMFromIndCpaReduction {KMac Tag : Type} [DecidableEq Tag]
    (mac : MACScheme KMac Tag) :
    SRReduction (IndCpaSpec BitVec) (EtMSpec Tag) where
  stateType := EtMFromIndCpaState KMac Tag
  initialState := do
    let km ← mac.keyGen
    pure { macKey := km, seen := ∅ }
  queries := {
    impl := fun
      | OracleSpec.query (IndCcaQ.eavesdrop n) (m₀, m₁) => do
          let st ← SRReduction.get
          let c ← SRReduction.query n (m₀, m₁)
          let t := mac.tag st.macKey c
          SRReduction.set { st with seen := insert (⟨n, (c, t)⟩ : EtMCiphertext Tag) st.seen }
          pure (c, t)
      | OracleSpec.query (IndCcaQ.decrypt n) ct => do
          let st ← SRReduction.get
          if (ct : EtMCiphertext Tag) ∈ st.seen then
            pure none
          else
            pure (some (BitVec.zero n))
  }


def IndCCAToRedEncTimesMac {KMac KEnc Tag}
    (s : IndCcaState (KMac × KEnc) (fun n => BitVec n × Tag)) :
    EtMFromMacState KEnc Tag × KMac :=
  ({ encKey := s.key.2, seen := s.seen }, s.key.1)


/-- `IND-CCA-L` for EtM is observationally equivalent to composing MAC-real with
`EtMFromMACLReduction`. -/
theorem obsEq_indCcaL_apply_macReal
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq
      (IndCcaL (encryptThenMac enc mac))
      (applySRReduction (EtMFromMACLReduction enc) (MACUFReal mac)) := by
    refine correctAbstractionImpliesObsEq
      (ro₁ := IndCcaL (encryptThenMac enc mac))
      (ro₂ := applySRReduction (EtMFromMACLReduction enc) (MACUFReal mac))
      (f := IndCCAToRedEncTimesMac)
      ?_

    constructor
    · simp [IndCCAToRedEncTimesMac, IndCcaL, applySRReduction, EtMFromMACLReduction, MACUFReal, encryptThenMac]
      simp only [PMF.map_bind, PMF.pure_map, IndCCAToRedEncTimesMac]
    · intro s₁ i query
      cases i with
      | eavesdrop n =>
        simp [OracleSpec.domain, IndCcaSpec] at query
        simp [EtMFromMACLReduction]
        dsimp [applySRReduction]
        simp [query_impl_convert]
        simp [OracleComp.simulateQ]
        simp [IndCcaL]
        simp [StateT.run]
        simp [IndCCAToRedEncTimesMac]
        simp [OracleSpec.range, OracleSpec.domain, IndCcaSpec]
        simp [PMF.map]
        conv =>
          lhs
          arg 2
          intro p
          arg 2
          dsimp [Function.comp, mapSecond, IndCCAToRedEncTimesMac]

        -- simp [EtMFromMACLReduction]

        -- simp [applySRReduction]

        sorry
      | decrypt m =>
        sorry



/-- `IND-CCA-R` for EtM is observationally equivalent to composing MAC-real with
`EtMFromMACRReduction`. -/
theorem obsEq_apply_macReal_indCcaR
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFReal mac))
      (IndCcaR (C := fun n => EtMC Tag n) (encryptThenMac enc mac)) := by
  sorry

/-- State for the explicit EtM intermediate games:
encryption key, IND-CCA seen set, MAC key, MAC seen-pairs set. -/
structure EtMGameState (KEnc KMac Tag : Type) where
  encKey : KEnc
  seenCca : Finset (EtMCiphertext Tag)
  macKey : KMac
  seenMac : Finset (EtMCiphertext Tag)

/-- Explicit game after replacing MAC-real by MAC-ideal (left branch), written without
oracle composition. -/
noncomputable def EtMGameMacIdealL {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMGameState KEnc KMac Tag
  initialState := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure { encKey := ke, seenCca := ∅, macKey := km, seenMac := ∅ }
  queries := {
    impl := fun
      | (IndCcaQ.eavesdrop n), (m₀, _m₁) => do
          let st ← get
          let c ← enc.encrypt st.encKey m₀
          let t := mac.tag st.macKey c
          let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
          set { st with seenCca := insert p st.seenCca, seenMac := insert p st.seenMac }
          pure (c, t)
      | (IndCcaQ.decrypt n), ct => do
          let st ← get
          if (ct : EtMCiphertext Tag) ∈ st.seenCca then
            pure none
          else if (ct : EtMCiphertext Tag) ∉ st.seenMac then
            pure (some (BitVec.zero n))
          else
            pure (some (enc.decrypt st.encKey ct.1))
  }

/-- Right-branch version of `EtMGameMacIdealL`. -/
noncomputable def EtMGameMacIdealR {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMGameState KEnc KMac Tag
  initialState := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure { encKey := ke, seenCca := ∅, macKey := km, seenMac := ∅ }
  queries := {
    impl := fun
      | (IndCcaQ.eavesdrop n), (_m₀, m₁) => do
          let st ← get
          let c ← enc.encrypt st.encKey m₁
          let t := mac.tag st.macKey c
          let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
          set { st with seenCca := insert p st.seenCca, seenMac := insert p st.seenMac }
          pure (c, t)
      | (IndCcaQ.decrypt n), ct => do
          let st ← get
          if (ct : EtMCiphertext Tag) ∈ st.seenCca then
            pure none
          else if (ct : EtMCiphertext Tag) ∉ st.seenMac then
            pure (some (BitVec.zero n))
          else
            pure (some (enc.decrypt st.encKey ct.1))
  }

/-- Simplified left intermediate game: decryption no longer uses `enc.decrypt`. -/
noncomputable def EtMGameZeroL {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMGameState KEnc KMac Tag
  initialState := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure { encKey := ke, seenCca := ∅, macKey := km, seenMac := ∅ }
  queries := {
    impl := fun
      | (IndCcaQ.eavesdrop n), (m₀, _m₁) => do
          let st ← get
          let c ← enc.encrypt st.encKey m₀
          let t := mac.tag st.macKey c
          let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
          set { st with seenCca := insert p st.seenCca, seenMac := insert p st.seenMac }
          pure (c, t)
      | (IndCcaQ.decrypt n), ct => do
          let st ← get
          if (ct : EtMCiphertext Tag) ∈ st.seenCca then
            pure none
          else
            pure (some (BitVec.zero n))
  }

/-- Simplified right intermediate game: decryption no longer uses `enc.decrypt`. -/
noncomputable def EtMGameZeroR {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMGameState KEnc KMac Tag
  initialState := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure { encKey := ke, seenCca := ∅, macKey := km, seenMac := ∅ }
  queries := {
    impl := fun
      | (IndCcaQ.eavesdrop n), (_m₀, m₁) => do
          let st ← get
          let c ← enc.encrypt st.encKey m₁
          let t := mac.tag st.macKey c
          let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
          set { st with seenCca := insert p st.seenCca, seenMac := insert p st.seenMac }
          pure (c, t)
      | (IndCcaQ.decrypt n), ct => do
          let st ← get
          if (ct : EtMCiphertext Tag) ∈ st.seenCca then
            pure none
          else
            pure (some (BitVec.zero n))
  }

/-- Bridge: composed MAC-ideal oracle equals explicit left intermediate game. -/
theorem obsEq_apply_macIdeal_gameMacIdealL
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (applySRReduction (EtMFromMACLReduction (Tag := Tag) enc) (MACUFIdeal mac))
      (EtMGameMacIdealL enc mac) := by
  sorry

/-- Bridge: explicit left intermediate game equals the simplified decryption game. -/
theorem obsEq_gameMacIdealL_gameZeroL
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (EtMGameMacIdealL enc mac) (EtMGameZeroL enc mac) := by
  sorry

/-- Bridge: simplified left game equals IND-CPA-left composed with `EtMFromIndCpaReduction`. -/
theorem obsEq_gameZeroL_apply_indCpaL
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (EtMGameZeroL enc mac)
      (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaL (C := BitVec) enc)) := by
  sorry

/-- Bridge: IND-CPA-right composed with `EtMFromIndCpaReduction` equals simplified right game. -/
theorem obsEq_apply_indCpaR_gameZeroR
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaR (C := BitVec) enc))
      (EtMGameZeroR enc mac) := by
  sorry

/-- Bridge: simplified right game equals explicit right intermediate game. -/
theorem obsEq_gameZeroR_gameMacIdealR
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (EtMGameZeroR enc mac) (EtMGameMacIdealR enc mac) := by
  sorry

/-- Bridge: explicit right intermediate game equals composed MAC-ideal oracle. -/
theorem obsEq_gameMacIdealR_apply_macIdeal
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (EtMGameMacIdealR enc mac)
      (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFIdeal mac)) := by
  sorry

/-- IND-CCA security of Encrypt-then-MAC from IND-CPA security of encryption and
MAC unforgeability, via the game-hopping sequence described above. -/
theorem indCpaAndMacUfImpliesIndCcaEncryptThenMac
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag)
    (hMacRedL :
      (EtMFromMACLReduction (Tag := Tag) enc) ∈
        Reductions.reductions (MACUFSpec Tag) (EtMSpec Tag))
    (hMacRedR :
      (EtMFromMACRReduction (Tag := Tag) enc) ∈
        Reductions.reductions (MACUFSpec Tag) (EtMSpec Tag))
    (hIndCpaRed :
      (EtMFromIndCpaReduction (Tag := Tag) mac) ∈
        Reductions.reductions (IndCpaSpec BitVec) (EtMSpec Tag))
    (hIndCpa : IndCpaDef Assumptions Reductions (C := BitVec) enc)
    (hMacUf : MACUFDef Assumptions Reductions mac) :
    IndCcaDef Assumptions Reductions (C := fun n => EtMC Tag n) (encryptThenMac enc mac) := by
  have hMacRealIdeal :
      Indistinguishable Assumptions Reductions
        (MACUFSpec Tag) (MACUFReal mac) (MACUFIdeal mac) := by
    simpa [MACUFDef] using hMacUf

  have hMacIdealReal :
      Indistinguishable Assumptions Reductions
        (MACUFSpec Tag) (MACUFIdeal mac) (MACUFReal mac) :=
    Indistinguishable.symm hMacRealIdeal

  have hIndCpaLR :
      Indistinguishable Assumptions Reductions
        (IndCpaSpec BitVec) (IndCpaL (C := BitVec) enc) (IndCpaR (C := BitVec) enc) := by
    simpa [IndCpaDef] using hIndCpa

  have h1 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (IndCcaL (C := fun n => EtMC Tag n) (encryptThenMac enc mac))
        (applySRReduction (EtMFromMACLReduction (Tag := Tag) enc) (MACUFReal mac)) :=
    Indistinguishable.of_ObsEq (obsEq_indCcaL_apply_macReal enc mac)

  have h2 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (applySRReduction (EtMFromMACLReduction (Tag := Tag) enc) (MACUFReal mac))
        (applySRReduction (EtMFromMACLReduction (Tag := Tag) enc) (MACUFIdeal mac)) :=
    Indistinguishable.reduction (r := EtMFromMACLReduction (Tag := Tag) enc) hMacRealIdeal hMacRedL

  have h3 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (applySRReduction (EtMFromMACLReduction (Tag := Tag) enc) (MACUFIdeal mac))
        (EtMGameMacIdealL enc mac) :=
    Indistinguishable.of_ObsEq (obsEq_apply_macIdeal_gameMacIdealL enc mac)

  have h4 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (EtMGameMacIdealL enc mac) (EtMGameZeroL enc mac) :=
    Indistinguishable.of_ObsEq (obsEq_gameMacIdealL_gameZeroL enc mac)

  have h5 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (EtMGameZeroL enc mac)
        (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaL (C := BitVec) enc)) :=
    Indistinguishable.of_ObsEq (obsEq_gameZeroL_apply_indCpaL enc mac)

  have h6 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaL (C := BitVec) enc))
        (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaR (C := BitVec) enc)) :=
    Indistinguishable.reduction (r := EtMFromIndCpaReduction (Tag := Tag) mac) hIndCpaLR hIndCpaRed

  have h7 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaR (C := BitVec) enc))
        (EtMGameZeroR enc mac) :=
    Indistinguishable.of_ObsEq (obsEq_apply_indCpaR_gameZeroR enc mac)

  have h8 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (EtMGameZeroR enc mac) (EtMGameMacIdealR enc mac) :=
    Indistinguishable.of_ObsEq (obsEq_gameZeroR_gameMacIdealR enc mac)

  have h9 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (EtMGameMacIdealR enc mac)
        (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFIdeal mac)) :=
    Indistinguishable.of_ObsEq (obsEq_gameMacIdealR_apply_macIdeal enc mac)

  have h10 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFIdeal mac))
        (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFReal mac)) :=
    Indistinguishable.reduction (r := EtMFromMACRReduction (Tag := Tag) enc) hMacIdealReal hMacRedR

  have h11 :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFReal mac))
        (IndCcaR (C := fun n => EtMC Tag n) (encryptThenMac enc mac)) :=
    Indistinguishable.of_ObsEq (obsEq_apply_macReal_indCcaR enc mac)

  have h :
      Indistinguishable Assumptions Reductions
        (EtMSpec Tag)
        (IndCcaL (C := fun n => EtMC Tag n) (encryptThenMac enc mac))
        (IndCcaR (C := fun n => EtMC Tag n) (encryptThenMac enc mac)) :=
    Indistinguishable.trans h1 <|
      Indistinguishable.trans h2 <|
        Indistinguishable.trans h3 <|
          Indistinguishable.trans h4 <|
            Indistinguishable.trans h5 <|
              Indistinguishable.trans h6 <|
                Indistinguishable.trans h7 <|
                  Indistinguishable.trans h8 <|
                    Indistinguishable.trans h9 <|
                      Indistinguishable.trans h10 h11

  simpa [IndCcaDef, EtMSpec] using h
