import GameHoppingInLean.Examples.SecurityDefinitions.IndCca
import GameHoppingInLean.Examples.SecurityDefinitions.IndCpa
import GameHoppingInLean.Examples.SecurityDefinitions.MACUnforgeability
import GameHoppingInLean.Examples.Constructions.EncryptThenMac
import GameHoppingInLean.IndistinguishabilityTactics

open scoped OracleReduction



abbrev EtMC (Tag : Type) (n : ℕ) := BitVec n × Tag
abbrev EtMSpec (Tag : Type) : OracleSpec (IndCcaQ (fun n => EtMC Tag n)) :=
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

/-- Reduction from MAC-unforgeability oracle to the IND-CCA left game for Encrypt-then-MAC. -/
@[local game_hopping_unfold]
noncomputable def EtMFromMACLReduction {KEnc Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) :
    OracleReduction (MACUFSpec Tag) (EtMSpec Tag) where
  stateType := EtMFromMacState KEnc Tag
  initialState := do
    let ke ← OracleReduction.initSample enc.keyGen
    pure { encKey := ke, seen := ∅ }
  queries := fun
    | IndCcaQ.eavesdrop n (m₀, _m₁) => do
        let st ← OracleReduction.get
        let c ← OracleReduction.sample (enc.encrypt st.encKey m₀)
        let t ← OracleReduction.query (MACUFQ.getTag n c)
        OracleReduction.set { st with seen := insert (⟨n, (c, t)⟩ : EtMCiphertext Tag) st.seen }
        pure (c, t)
    | IndCcaQ.decrypt n (c, t) => do
        let st ← OracleReduction.get
        if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.seen then
          pure none
        else
          let b : Bool ← OracleReduction.query (MACUFQ.checkTag n c t)
          if b then
            pure (some (enc.decrypt st.encKey c))
          else
            pure (some (BitVec.zero n))

/-- Right-message version of `EtMFromMACLReduction`. -/
@[local game_hopping_unfold]
noncomputable def EtMFromMACRReduction {KEnc Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) :
    OracleReduction (MACUFSpec Tag) (EtMSpec Tag) where
  stateType := EtMFromMacState KEnc Tag
  initialState := do
    let ke ← OracleReduction.initSample enc.keyGen
    pure { encKey := ke, seen := ∅ }
  queries := fun
    | IndCcaQ.eavesdrop n (_m₀, m₁) => do
        let st ← OracleReduction.get
        let c ← OracleReduction.sample (enc.encrypt st.encKey m₁)
        let t ← OracleReduction.query (MACUFQ.getTag n c)
        OracleReduction.set { st with seen := insert (⟨n, (c, t)⟩ : EtMCiphertext Tag) st.seen }
        pure (c, t)
    | IndCcaQ.decrypt n (c, t) => do
        let st ← OracleReduction.get
        if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.seen then
          pure none
        else
          let b : Bool ← OracleReduction.query (MACUFQ.checkTag n c t)
          if b then
            pure (some (enc.decrypt st.encKey c))
          else
            pure (some (BitVec.zero n))

/-- Reduction from IND-CPA left/right games to a simplified IND-CCA-style EtM game. -/
@[local game_hopping_unfold]
noncomputable def EtMFromIndCpaReduction {KMac Tag : Type} [DecidableEq Tag]
    (mac : MACScheme KMac Tag) :
    OracleReduction (IndCpaSpec BitVec) (EtMSpec Tag) where
  stateType := EtMFromIndCpaState KMac Tag
  initialState := do
    let km ← OracleReduction.initSample mac.keyGen
    pure { macKey := km, seen := ∅ }
  queries := fun
    | IndCcaQ.eavesdrop n (m₀, m₁) => do
        let st ← OracleReduction.get
        let c ← OracleReduction.query (IndCpaDomain.eavesdrop n (m₀, m₁))
        let t := mac.tag st.macKey c
        OracleReduction.set { st with seen := insert (⟨n, (c, t)⟩ : EtMCiphertext Tag) st.seen }
        pure (c, t)
    | IndCcaQ.decrypt n (c, t) => do
        let st ← OracleReduction.get
        if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.seen then
          pure none
        else
          pure (some (BitVec.zero n))

/-- Explicit game after replacing MAC-real by MAC-ideal on the left branch. -/
@[local game_hopping_unfold]
noncomputable def EtMGameMacIdealL {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag
  initialState := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure ({ encKey := ke, seen := ∅ }, { key := km, seen := ∅ })
  queries := fun
    | IndCcaQ.eavesdrop n (m₀, _m₁) => do
        let st ← get
        let c ← enc.encrypt st.1.encKey m₀
        let t := mac.tag st.2.key c
        let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
        set ({ st.1 with seen := insert p st.1.seen },
          { st.2 with seen := insert p st.2.seen })
        pure (c, t)
    | IndCcaQ.decrypt n (c, t) => do
        let st ← get
        if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.1.seen then
          pure none
        else if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.2.seen then
          pure (some (enc.decrypt st.1.encKey c))
        else
          pure (some (BitVec.zero n))

/-- Right-branch version of `EtMGameMacIdealL`. -/
@[local game_hopping_unfold]
noncomputable def EtMGameMacIdealR {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag
  initialState := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure ({ encKey := ke, seen := ∅ }, { key := km, seen := ∅ })
  queries := fun
    | IndCcaQ.eavesdrop n (_m₀, m₁) => do
        let st ← get
        let c ← enc.encrypt st.1.encKey m₁
        let t := mac.tag st.2.key c
        let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
        set ({ st.1 with seen := insert p st.1.seen },
          { st.2 with seen := insert p st.2.seen })
        pure (c, t)
    | IndCcaQ.decrypt n (c, t) => do
        let st ← get
        if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.1.seen then
          pure none
        else if (⟨n, (c, t)⟩ : EtMCiphertext Tag) ∈ st.2.seen then
          pure (some (enc.decrypt st.1.encKey c))
        else
          pure (some (BitVec.zero n))

/-- Abstraction from the left MAC reduction state to the left IND-CCA EtM state. -/
@[local game_hopping_unfold]
abbrev EtMIndCcaLToMacLAbstraction {KEnc KMac Tag : Type}
    (s : EtMFromMacState KEnc Tag × KMac) :
    IndCcaState (KMac × KEnc) (fun n => EtMC Tag n) :=
  { key := (s.2, s.1.encKey), seen := s.1.seen }

/-- Abstraction from the left IND-CPA reduction state to the left MAC-ideal EtM game. -/
@[local game_hopping_unfold]
abbrev EtMMacIdealLToIndCpaLAbstraction {KEnc KMac Tag : Type}
    (s : EtMFromIndCpaState KMac Tag × KEnc) :
    EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag :=
  ({ encKey := s.2, seen := s.1.seen },
    { key := s.1.macKey, seen := s.1.seen })

/-- Abstraction from the right IND-CPA reduction state to the right MAC-ideal EtM game. -/
@[local game_hopping_unfold]
abbrev EtMIndCpaRToMacIdealRAbstraction {KEnc KMac Tag : Type}
    (s : EtMFromIndCpaState KMac Tag × KEnc) :
    EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag :=
  ({ encKey := s.2, seen := s.1.seen },
    { key := s.1.macKey, seen := s.1.seen })

/-- Abstraction from the right MAC reduction state to the right IND-CCA EtM state. -/
@[local game_hopping_unfold]
abbrev EtMMacRToIndCcaRAbstraction {KEnc KMac Tag : Type}
    (s : EtMFromMacState KEnc Tag × KMac) :
    IndCcaState (KMac × KEnc) (fun n => EtMC Tag n) :=
  { key := (s.2, s.1.encKey), seen := s.1.seen }

attribute [local game_hopping_unfold] EtMFromMACLReduction EtMFromMACRReduction
  EtMFromIndCpaReduction EtMGameMacIdealL EtMGameMacIdealR
  IndCpaL IndCpaR IndCcaL IndCcaR MACUFReal MACUFIdeal MACScheme.check
  IndCcaLFam  IndCcaRFam encryptThenMac encryptThenMacFamily
/-- IND-CCA security of Encrypt-then-MAC from IND-CPA security and MAC unforgeability,
family version. The generated hop obligations are intentionally left for future proof work. -/
noncomputable def indCpaAndMacUfImpliesIndCcaEncryptThenMacFam
    {KEnc KMac Tag : ℕ → Type} [∀ κ, DecidableEq (Tag κ)]
    (encFam : SymEncSchemeFamily KEnc (fun _ => BitVec))
    (macFam : MACSchemeFamily KMac Tag) :
    IndCcaProof
      ((IndCpaAssumptionFam encFam) ⊕ MACUFAssumptionFam macFam)
      (encryptThenMacFamily encFam macFam) := by
  intro κ
  let enc := encFam.scheme κ
  let mac := macFam.scheme κ
  game_hopping [
    IndCcaL (encryptThenMac enc mac),
    (EtMFromMACLReduction enc) ◇ (MACUFReal mac),
    (EtMFromMACLReduction enc) ◇ (MACUFIdeal mac),
    -- EtMGameMacIdealL enc mac,
    (EtMFromIndCpaReduction mac) ◇ (IndCpaL enc),
    (EtMFromIndCpaReduction mac) ◇ (IndCpaR enc),
    -- EtMGameMacIdealR enc mac,
    (EtMFromMACRReduction enc) ◇ (MACUFIdeal mac),
    (EtMFromMACRReduction enc) ◇ (MACUFReal mac),
    IndCcaR (encryptThenMac enc mac)
  ]
  · by_abstraction ← EtMIndCcaLToMacLAbstraction
  · by_abstraction ← EtMMacIdealLToIndCpaLAbstraction
  · by_abstraction EtMIndCpaRToMacIdealRAbstraction
  · by_abstraction EtMMacRToIndCcaRAbstraction
