import GameHoppingInLean.Examples.SecurityDefintions.IndCca
import GameHoppingInLean.Examples.SecurityDefintions.IndCpa
import GameHoppingInLean.Examples.SecurityDefintions.MACUnforgeability
import GameHoppingInLean.Examples.Constructions.EncryptThenMac
import GameHoppingInLean.FreeMonadLemmas


attribute [-simp] bind_pure_comp

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

def RedEncTimesMacToIndCCA {KMac KEnc Tag}
    (s : EtMFromMacState KEnc Tag × KMac) :
    IndCcaState (KMac × KEnc) (fun n => BitVec n × Tag) :=
  { key := (s.2, s.1.encKey), seen := s.1.seen }

def IndCCAToRedEncTimesMacEquiv {KMac KEnc Tag} :
    IndCcaState (KMac × KEnc) (fun n => BitVec n × Tag) ≃
      (EtMFromMacState KEnc Tag × KMac) where
  toFun := IndCCAToRedEncTimesMac
  invFun := RedEncTimesMacToIndCCA
  left_inv := by
    intro s
    cases s with
    | mk k seen =>
        cases k with
        | mk km ke =>
            rfl
  right_inv := by
    intro s
    cases s with
    | mk st km =>
        cases st with
        | mk ke seen =>
            rfl

@[simp]
lemma push_map_second {A B C D : Type} {x : PMF A} (f : A -> PMF (B × C))  (g : C → D)
  :  PMF.map (mapSecond g) (PMF.bind x f) = PMF.bind x (fun x' => (f x').map (mapSecond g)) :=
  by
    exact PMF.map_bind x f (mapSecond g)

/-- `IND-CCA-L` for EtM is observationally equivalent to composing MAC-real with
`EtMFromMACLReduction`. -/
theorem obsEq_indCcaL_apply_macReal
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq
      (IndCcaL (encryptThenMac enc mac))
      (applySRReduction (EtMFromMACLReduction enc) (MACUFReal mac)) := by
    refine existsMapStateBijImpliesObsEq
      (ro₁ := IndCcaL (encryptThenMac enc mac))
      (ro₂ := applySRReduction (EtMFromMACLReduction enc) (MACUFReal mac))
      ?_
    refine ⟨IndCCAToRedEncTimesMacEquiv (KMac := KMac) (KEnc := KEnc) (Tag := Tag), ?_, ?_⟩
    · simp [IndCCAToRedEncTimesMacEquiv, IndCCAToRedEncTimesMac, RedEncTimesMacToIndCCA,
        IndCcaL, applySRReduction, EtMFromMACLReduction, MACUFReal, encryptThenMac,
        PMF.map_bind, PMF.pure_map]
    · intro i query
      cases i with
      | eavesdrop n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACLReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [IndCcaL, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACLReduction, RState.modify, MACUFReal, IndCCAToRedEncTimesMacEquiv, RedEncTimesMacToIndCCA, IndCCAToRedEncTimesMac, encryptThenMac]
      | decrypt n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACLReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [IndCcaL, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACLReduction, RState.modify, MACUFReal, IndCCAToRedEncTimesMacEquiv, RedEncTimesMacToIndCCA, IndCCAToRedEncTimesMac, encryptThenMac, FreeMonad.roll]


/-- `IND-CCA-R` for EtM is observationally equivalent to composing MAC-real with
`EtMFromMACRReduction`. -/
theorem obsEq_apply_macReal_indCcaR
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFReal mac))
      (IndCcaR (C := fun n => EtMC Tag n) (encryptThenMac enc mac)) := by
  first
  | exact obsEqReflexive _ _ rfl
  | refine existsMapStateBijImpliesObsEq
      (ro₁ := applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFReal mac))
      (ro₂ := IndCcaR (C := fun n => EtMC Tag n) (encryptThenMac enc mac))
      ?_
    refine ⟨(IndCCAToRedEncTimesMacEquiv (KMac := KMac) (KEnc := KEnc) (Tag := Tag)).symm, ?_, ?_⟩
    · simp [IndCCAToRedEncTimesMacEquiv, IndCCAToRedEncTimesMac, RedEncTimesMacToIndCCA,
        IndCcaR, applySRReduction, EtMFromMACRReduction, MACUFReal, encryptThenMac,
        PMF.map_bind, PMF.pure_map]
    · intro i query
      cases i with
      | eavesdrop n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACRReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [IndCcaR, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACRReduction, RState.modify,
            MACUFReal, IndCCAToRedEncTimesMacEquiv, RedEncTimesMacToIndCCA,
            IndCCAToRedEncTimesMac, encryptThenMac]
      | decrypt n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACRReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [IndCcaR, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACRReduction, RState.modify,
            MACUFReal, IndCCAToRedEncTimesMacEquiv, RedEncTimesMacToIndCCA,
            IndCCAToRedEncTimesMac, encryptThenMac, FreeMonad.roll]

/-- State for the explicit EtM intermediate games:
encryption key, IND-CCA seen set, MAC key, MAC seen-pairs set. -/
structure EtMGameState (KEnc KMac Tag : Type) where
  encKey : KEnc
  seenCca : Finset (EtMCiphertext Tag)
  macKey : KMac
  seenMac : Finset (EtMCiphertext Tag)

def RedMacIdealToEtMGameState {KEnc KMac Tag}
    (s : EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag) :
    EtMGameState KEnc KMac Tag :=
  { encKey := s.1.encKey
    seenCca := s.1.seen
    macKey := s.2.key
    seenMac := s.2.seen }

def EtMGameStateToRedMacIdeal {KEnc KMac Tag}
    (s : EtMGameState KEnc KMac Tag) :
    EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag :=
  ({ encKey := s.encKey, seen := s.seenCca }, { key := s.macKey, seen := s.seenMac })

def RedMacIdealEtMGameStateEquiv {KEnc KMac Tag} :
    (EtMFromMacState KEnc Tag × MACUFIdealState KMac Tag) ≃
      EtMGameState KEnc KMac Tag where
  toFun := RedMacIdealToEtMGameState
  invFun := EtMGameStateToRedMacIdeal
  left_inv := by
    intro s
    cases s with
    | mk s1 s2 =>
        cases s1 with
        | mk encKey seen =>
            cases s2 with
            | mk key seen' =>
                simp [RedMacIdealToEtMGameState, EtMGameStateToRedMacIdeal, EtMCiphertext,
                  MACTaggedMessage]
  right_inv := by
    intro s
    cases s with
    | mk encKey seenCca macKey seenMac =>
        rfl

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

/-- Simplified left intermediate game: decryption no longer uses `enc.decrypt`.
State is reduced to exactly what the IND-CPA reduction keeps: MAC key, seen set, and enc key. -/
noncomputable def EtMGameZeroL {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMFromIndCpaState KMac Tag × KEnc
  initialState := do
    let km ← mac.keyGen
    let ke ← enc.keyGen
    pure ({ macKey := km, seen := ∅ }, ke)
  queries := {
    impl := fun
      | (IndCcaQ.eavesdrop n), (m₀, _m₁) => do
          let st ← get
          let c ← enc.encrypt st.2 m₀
          let t := mac.tag st.1.macKey c
          let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
          set ({ st.1 with seen := insert p st.1.seen }, st.2)
          pure (c, t)
      | (IndCcaQ.decrypt n), ct => do
          let st ← get
          if (ct : EtMCiphertext Tag) ∈ st.1.seen then
            pure none
          else
            pure (some (BitVec.zero n))
  }

/-- Simplified right intermediate game: decryption no longer uses `enc.decrypt`.
State is reduced to exactly what the IND-CPA reduction keeps: MAC key, seen set, and enc key. -/
noncomputable def EtMGameZeroR {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    RStateOracle (EtMSpec Tag) where
  stateType := EtMFromIndCpaState KMac Tag × KEnc
  initialState := do
    let km ← mac.keyGen
    let ke ← enc.keyGen
    pure ({ macKey := km, seen := ∅ }, ke)
  queries := {
    impl := fun
      | (IndCcaQ.eavesdrop n), (_m₀, m₁) => do
          let st ← get
          let c ← enc.encrypt st.2 m₁
          let t := mac.tag st.1.macKey c
          let p : EtMCiphertext Tag := ⟨n, (c, t)⟩
          set ({ st.1 with seen := insert p st.1.seen }, st.2)
          pure (c, t)
      | (IndCcaQ.decrypt n), ct => do
          let st ← get
          if (ct : EtMCiphertext Tag) ∈ st.1.seen then
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
  first
  | exact obsEqReflexive _ _ rfl
  | refine existsMapStateBijImpliesObsEq
      (ro₁ := applySRReduction (EtMFromMACLReduction (Tag := Tag) enc) (MACUFIdeal mac))
      (ro₂ := EtMGameMacIdealL enc mac)
      ?_
    refine ⟨RedMacIdealEtMGameStateEquiv (KEnc := KEnc) (KMac := KMac) (Tag := Tag), ?_, ?_⟩
    · simp [RedMacIdealEtMGameStateEquiv, RedMacIdealToEtMGameState, EtMGameStateToRedMacIdeal,
        applySRReduction, EtMFromMACLReduction, MACUFIdeal, EtMGameMacIdealL,
        PMF.map_bind, PMF.pure_map]
    · intro i query
      cases i with
      | eavesdrop n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACLReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameMacIdealL, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACLReduction,
            RState.modify, MACUFIdeal, RedMacIdealEtMGameStateEquiv, RedMacIdealToEtMGameState,
            EtMGameStateToRedMacIdeal]
      | decrypt n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACLReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameMacIdealL, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACLReduction,
            RState.modify, MACUFIdeal, RedMacIdealEtMGameStateEquiv, RedMacIdealToEtMGameState,
            EtMGameStateToRedMacIdeal, FreeMonad.roll]

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
  first
  | exact obsEqReflexive _ _ rfl
  | refine existsMapStateBijImpliesObsEq
      (ro₁ := EtMGameZeroL enc mac)
      (ro₂ := applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaL (C := BitVec) enc))
      ?_
    refine ⟨Equiv.refl _, ?_, ?_⟩
    · simp [EtMGameZeroL, applySRReduction, EtMFromIndCpaReduction, IndCpaL,
        PMF.map_bind, PMF.pure_map]
    · intro i query
      cases i with
      | eavesdrop n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromIndCpaReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameZeroL, OracleComp.simulateQ, FreeMonad.mapM, EtMFromIndCpaReduction,
            RState.modify, IndCpaL]
          rfl
      | decrypt n =>
          rcases query with ⟨ct, t⟩
          simp [EtMFromIndCpaReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameZeroL, OracleComp.simulateQ, FreeMonad.mapM, EtMFromIndCpaReduction,
            RState.modify, IndCpaL, FreeMonad.roll]

/-- Bridge: IND-CPA-right composed with `EtMFromIndCpaReduction` equals simplified right game. -/
theorem obsEq_apply_indCpaR_gameZeroR
    {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    ObsEq (applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaR (C := BitVec) enc))
      (EtMGameZeroR enc mac) := by
  first
  | exact obsEqReflexive _ _ rfl
  | refine existsMapStateBijImpliesObsEq
      (ro₁ := applySRReduction (EtMFromIndCpaReduction (Tag := Tag) mac) (IndCpaR (C := BitVec) enc))
      (ro₂ := EtMGameZeroR enc mac)
      ?_
    refine ⟨Equiv.refl _, ?_, ?_⟩
    · simp [EtMGameZeroR, applySRReduction, EtMFromIndCpaReduction, IndCpaR,
        PMF.map_bind, PMF.pure_map]
    · intro i query
      cases i with
      | eavesdrop n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromIndCpaReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameZeroR, OracleComp.simulateQ, FreeMonad.mapM, EtMFromIndCpaReduction,
            RState.modify, IndCpaR]
          rfl
      | decrypt n =>
          rcases query with ⟨ct, t⟩
          simp [EtMFromIndCpaReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameZeroR, OracleComp.simulateQ, FreeMonad.mapM, EtMFromIndCpaReduction,
            RState.modify, IndCpaR, FreeMonad.roll]

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
  first
  | exact obsEqReflexive _ _ rfl
  | refine existsMapStateBijImpliesObsEq
      (ro₁ := EtMGameMacIdealR enc mac)
      (ro₂ := applySRReduction (EtMFromMACRReduction (Tag := Tag) enc) (MACUFIdeal mac))
      ?_
    refine ⟨(RedMacIdealEtMGameStateEquiv (KEnc := KEnc) (KMac := KMac) (Tag := Tag)).symm, ?_, ?_⟩
    · simp [RedMacIdealEtMGameStateEquiv, RedMacIdealToEtMGameState, EtMGameStateToRedMacIdeal,
        applySRReduction, EtMFromMACRReduction, MACUFIdeal, EtMGameMacIdealR,
        PMF.map_bind, PMF.pure_map]
    · intro i query
      cases i with
      | eavesdrop n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACRReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameMacIdealR, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACRReduction,
            RState.modify, MACUFIdeal, RedMacIdealEtMGameStateEquiv, RedMacIdealToEtMGameState,
            EtMGameStateToRedMacIdeal]
      | decrypt n =>
          rcases query with ⟨m₀, m₁⟩
          simp [EtMFromMACRReduction]
          dsimp [applySRReduction]
          simp [query_impl_convert]
          simp [EtMGameMacIdealR, OracleComp.simulateQ, FreeMonad.mapM, EtMFromMACRReduction,
            RState.modify, MACUFIdeal, RedMacIdealEtMGameStateEquiv, RedMacIdealToEtMGameState,
            EtMGameStateToRedMacIdeal, FreeMonad.roll]

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
