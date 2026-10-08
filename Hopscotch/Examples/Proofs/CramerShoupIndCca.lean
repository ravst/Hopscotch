import Hopscotch.Examples.Constructions.CramerShoup
import Hopscotch.Examples.SecurityDefinitions.CollisionResistance
import Hopscotch.Examples.Proofs.CramerShoupFailure
import Hopscotch.ApproxEq.CorrectUntilBad
import Hopscotch.ObservationalEq.Defs
import Hopscotch.Indistinguishability.Def
import Hopscotch.Tactic.Defs
import Hopscotch.Tactic.Normalization.PMF.Simprocs

/-!
# Cramer--Shoup IND-CCA game chain

This file follows Games G0--G5 in the proof of Cramer and Shoup, with small
instrumentation and coupling games around G2. These isolate the paper's
conditioning and rejection events into individual HOPSCOTCH hops.

All games use the same state type. The three Boolean fields are ghost state:

* `pairBad` records the conditioning failure `r₁ = r₂`;
* `rejectionBad` records the paper's event R3/R4/R5;
* `hashBad` records the target-hash collision event C5.

Challenge and decryption behavior is expressed with `if` statements. The only
pattern match left in a game is the unavoidable dispatch on the oracle query.
The final proof is a single game chain. Local abstraction and probability
lemmas are proved separately below. Rejection bridges reconstruct hidden full
states probabilistically and apply Bellman bounds only to simple oracle states.
The concrete cryptographic bridges remain explicit inputs to the chain.
-/

namespace Hopscotch.CramerShoup

open scoped OracleReduction

/-- Queries of the single-challenge public-key IND-CCA experiment. -/
inductive IndCcaQuery (V : Type) where
  | getPublicKey
  | challenge (m0 m1 : V)
  | decrypt (ct : Ciphertext V)

/-- Result types for the Cramer--Shoup IND-CCA experiment. -/
def IndCcaSpec (F V HashKey : Type) : OracleSpec (IndCcaQuery V)
  | .getPublicKey => PublicKey F V HashKey
  | .challenge _ _ => Option (Ciphertext V)
  | .decrypt _ => Option V

/-- Common state for every game in the proof. Keeping the state fixed makes
the paper's common probability space explicit and keeps adjacent hops local. -/
structure GameState (F V HashKey : Type) where
  secretKey : SecretKey F HashKey
  target : Option (Ciphertext V)
  pairBad : Bool
  rejectionBad : Bool
  hashBad : Bool

/-- The one-dimensional group hypothesis used by the paper's G3--G4
coupling: every message has a unique scalar coordinate relative to `g`. -/
structure CyclicGenerator (F V : Type) [SMul F V] (g : V) where
  coordinate : V → F
  reconstruct : ∀ v, coordinate v • g = v
  coordinate_smul : ∀ a, coordinate (a • g) = a

/-- A pair of distinct exponents, used by the conditioned form of G2. -/
abbrev DistinctPair (F : Type) := { p : F × F // p.1 ≠ p.2 }

instance distinctPairNonempty (F : Type) [Nontrivial F] :
    Nonempty (DistinctPair F) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne F
  exact ⟨⟨(a, b), hab⟩⟩

/-- Pick the message selected by the left/right challenge bit. -/
def selectedMessage {V : Type} (right : Bool) (m0 m1 : V) : V :=
  if right then m1 else m0

/-- Construct the G1 challenge directly from the secret exponents. -/
def encryptWithSecretPair
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (sk : SecretKey F HashKey)
    (message u1 u2 : V) : Ciphertext V :=
  let e := sk.z1 • u1 + sk.z2 • u2 + message
  let alpha := hf.hash sk.hashKey u1 u2 e
  let v := (sk.x1 + alpha * sk.y1) • u1 +
    (sk.x2 + alpha * sk.y2) • u2
  { u1 := u1, u2 := u2, e := e, v := v }

/-- Authenticate an explicitly chosen challenge payload. G4 uses this after
the message mask has been replaced by a fresh uniform group element. -/
def authenticate
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (sk : SecretKey F HashKey)
    (u1 u2 e : V) : Ciphertext V :=
  let alpha := hf.hash sk.hashKey u1 u2 e
  let v := (sk.x1 + alpha * sk.y1) • u1 +
    (sk.x2 + alpha * sk.y2) • u2
  { u1 := u1, u2 := u2, e := e, v := v }

/-- The public-key and secret-key descriptions of an honest challenge agree. -/
theorem encryptWithSecretPair_eq_encryptWithCoins
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (sk : SecretKey F HashKey) (message : V) (r : F) :
    encryptWithSecretPair hf sk message (r • g1) (r • g2) =
      encryptWithCoins hf (publicKey g1 g2 sk) message r := by
  have he :
      sk.z1 • (r • g1) + sk.z2 • (r • g2) + message =
        r • (sk.z1 • g1 + sk.z2 • g2) + message := by
    module
  simp only [encryptWithSecretPair, encryptWithCoins, publicKey]
  rw [he]
  congr 1
  module

/-- Collapsed exponents used by the paper after fixing `g₂ = w • g₁`. -/
def SecretKey.collapsedX
    {F HashKey : Type} [Semiring F]
    (sk : SecretKey F HashKey) (w : F) : F :=
  sk.x1 + w * sk.x2

def SecretKey.collapsedY
    {F HashKey : Type} [Semiring F]
    (sk : SecretKey F HashKey) (w : F) : F :=
  sk.y1 + w * sk.y2

def SecretKey.collapsedZ
    {F HashKey : Type} [Semiring F]
    (sk : SecretKey F HashKey) (w : F) : F :=
  sk.z1 + w * sk.z2

/-- Verification rule used from G3 onward. -/
def collapsedValid
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (ct : Ciphertext V) : Prop :=
  let alpha := hf.hash sk.hashKey ct.u1 ct.u2 ct.e
  ct.v = (sk.collapsedX w + alpha * sk.collapsedY w) • ct.u1

open scoped Classical in
/-- G3 decryption: first require the DH consistency equation and then use the
collapsed secret-key equations. -/
noncomputable def specialDecrypt
    {F V HashKey : Type} [Field F]
    [AddCommGroup V] [Module F V] [DecidableEq V]
    (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (ct : Ciphertext V) : Option V :=
  if ct.u2 = w • ct.u1 then
    if collapsedValid hf w sk ct then
      some (ct.e - sk.collapsedZ w • ct.u1)
    else
      none
  else
    none

open scoped Classical in
/-- Event R3: ordinary verification accepts a ciphertext that the special
G3 consistency test rejects. -/
noncomputable def rejectionEvent
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V] [DecidableEq V]
    (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (ct : Ciphertext V) : Bool :=
  decide (ct.u2 ≠ w • ct.u1 ∧ valid hf sk ct)

/-- Event C5: a different hash input collides with the target hash. -/
def targetHashCollision
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V] [DecidableEq F] [DecidableEq V]
    (hf : HashFamily F V HashKey) (sk : SecretKey F HashKey)
    (target candidate : Ciphertext V) : Bool :=
  decide
    ((candidate.u1, candidate.u2, candidate.e) ≠
        (target.u1, target.u2, target.e) ∧
      hf.hash sk.hashKey candidate.u1 candidate.u2 candidate.e =
        hf.hash sk.hashKey target.u1 target.u2 target.e)

/-- The message passed to the hash-comparison oracle consists of the first
three components of a ciphertext. Its authentication tag is excluded. -/
def hashMessage {V : Type} (ct : Ciphertext V) : V × V × V :=
  (ct.u1, ct.u2, ct.e)

/-- The fixed-public-key hash used by both collision-resistance worlds. -/
def ciphertextHash {F V HashKey : Type} (hf : HashFamily F V HashKey) (hk : HashKey)
    (m : V × V × V) : F := hf.hash hk m.1 m.2.1 m.2.2

/-- The paper's target-collision flag is exactly the event on which the
concrete and ideal comparison answers disagree. -/
theorem targetHashCollision_eq_comparisonDiff
    {F V HashKey : Type} [CommSemiring F] [AddCommMonoid V] [Module F V]
    [DecidableEq F] [DecidableEq V]
    (hf : HashFamily F V HashKey) (sk : SecretKey F HashKey)
    (target candidate : Ciphertext V) :
    targetHashCollision hf sk target candidate =
      decide (decide (ciphertextHash hf sk.hashKey (hashMessage candidate) =
        ciphertextHash hf sk.hashKey (hashMessage target)) ≠
        decide (hashMessage candidate = hashMessage target)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.decide_iff, targetHashCollision, hashMessage, ciphertextHash]
  exact (HashComparison.comparison_diff_iff_collision
    (ciphertextHash hf sk.hashKey) (hashMessage candidate) (hashMessage target)).symm

/-- Projections used as the bad predicates in correct-until-bad hops. -/
def pairBadFlag {F V HashKey : Type} (st : GameState F V HashKey) : Bool :=
  st.pairBad

def rejectionBadFlag {F V HashKey : Type} (st : GameState F V HashKey) : Bool :=
  st.rejectionBad

def hashBadFlag {F V HashKey : Type} (st : GameState F V HashKey) : Bool :=
  st.hashBad

/- These are the deterministic state abstractions used by the exact ghost
instrumentation hops.  They retain all operational state and erase precisely
the ghost component which is invisible in the neighboring game. -/

def forgetPairBadAbstraction
    {F V HashKey : Type} (st : GameState F V HashKey) :
    GameState F V HashKey :=
  { st with pairBad := false }

def forgetRejectionBadAbstraction
    {F V HashKey : Type} (st : GameState F V HashKey) :
    GameState F V HashKey :=
  { st with rejectionBad := false }

def forgetHashBadAbstraction
    {F V HashKey : Type} (st : GameState F V HashKey) :
    GameState F V HashKey :=
  { st with hashBad := false }

/-! The DDH interface used by this proof is the fixed-two-generator,
additive-module presentation: the real oracle uses one scalar for both
generators, while the random oracle uses independent scalars. -/

inductive ModuleDDHQuery where
  | query

def ModuleDDHSpec (V : Type) : OracleSpec ModuleDDHQuery
  | .query => V × V

noncomputable def DDHReal
    {F V : Type} [Fintype F] [Nonempty F] [SMul F V] (g1 g2 : V) :
    OracleImpl (ModuleDDHSpec V) where
  stateType := Unit
  initialState := pure ()
  queries := fun
    | .query => do
        let r ← PMF.uniformOfFintype F
        pure (r • g1, r • g2)

noncomputable def DDHRandom
    {F V : Type} [Fintype F] [Nonempty F] [SMul F V] (g1 g2 : V) :
    OracleImpl (ModuleDDHSpec V) where
  stateType := Unit
  initialState := pure ()
  queries := fun
    | .query => do
        let r1 ← PMF.uniformOfFintype F
        let r2 ← PMF.uniformOfFintype F
        pure (r1 • g1, r2 • g2)

section Games

variable {F V HashKey : Type}
variable [Field F] [Fintype F] [DecidableEq F]
variable [AddCommGroup V] [Module F V] [DecidableEq V]

abbrev GameM (F V HashKey Result : Type) :=
  RState (GameState F V HashKey) Result

/-- Common initialization shared literally by every game. -/
noncomputable def initialGameState
    (hf : HashFamily F V HashKey) (g1 g2 : V) :
    PMF (GameState F V HashKey) := do
  let (_pk, sk) ← keyGen hf g1 g2
  pure
    { secretKey := sk
      target := none
      pairBad := false
      rejectionBad := false
      hashBad := false }

/-- Assemble an IND-CCA game from its challenge and decryption rules. The
single-challenge check and prohibition on decrypting the target are shared,
so individual games cannot accidentally implement them differently. -/
noncomputable def gameOracle
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool)
    (challengeRule : Bool → V → V → GameM F V HashKey (Ciphertext V))
    (decryptRule : Ciphertext V → GameM F V HashKey (Option V)) :
    OracleImpl (IndCcaSpec F V HashKey) where
  stateType := GameState F V HashKey
  initialState := initialGameState hf g1 g2
  queries := fun
    | .getPublicKey => do
        let st ← get
        pure (publicKey g1 g2 st.secretKey)
    | .challenge m0 m1 => do
        let st ← get
        if st.target.isSome then
          pure none
        else
          let ct ← challengeRule right m0 m1
          let st' ← get
          set { st' with target := some ct }
          pure (some ct)
    | .decrypt ct => do
        let st ← get
        if st.target = some ct then
          pure none
        else
          decryptRule ct

/-- DDH reduction for the G1--G2Raw hop.  The DDH pair is requested lazily
when the unique challenge query arrives, so adaptively chosen challenge
messages can be inserted without knowing either sampled scalar. -/
noncomputable def CramerShoupDDHReduction
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    OracleReduction (ModuleDDHSpec V) (IndCcaSpec F V HashKey) where
  stateType := GameState F V HashKey
  initialState := OracleReduction.initSample (initialGameState hf g1 g2)
  queries := fun
    | .getPublicKey => do
        let st ← OracleReduction.get
        pure (publicKey g1 g2 st.secretKey)
    | .challenge m0 m1 => do
        let st ← OracleReduction.get
        if st.target.isSome then
          pure none
        else
          let uv ← OracleReduction.query ModuleDDHQuery.query
          let ct := encryptWithSecretPair hf st.secretKey
            (selectedMessage right m0 m1) uv.1 uv.2
          OracleReduction.set { st with target := some ct }
          pure (some ct)
    | .decrypt ct => do
        let st ← OracleReduction.get
        if st.target = some ct then
          pure none
        else
          pure (decrypt hf st.secretKey ct)

noncomputable def normalDecryptRule
    (hf : HashFamily F V HashKey) (ct : Ciphertext V) :
    GameM F V HashKey (Option V) := do
  let st ← get
  pure (decrypt hf st.secretKey ct)

/-- G0 challenge: the actual public-key encryption algorithm. -/
noncomputable def g0Challenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let r ← PMF.uniformOfFintype F
  pure (encryptWithCoins hf (publicKey g1 g2 st.secretKey)
    (selectedMessage right m0 m1) r)

/-- G1 challenge: the same ciphertext expressed using secret exponents. -/
noncomputable def g1Challenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let r ← PMF.uniformOfFintype F
  pure (encryptWithSecretPair hf st.secretKey
    (selectedMessage right m0 m1) (r • g1) (r • g2))

/-- G2Raw is the direct DDH endpoint: the two challenge exponents are
independent. In particular, it does not ask the DDH reduction to recover or
record their exponents. -/
noncomputable def g2RawChallenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let r1 ← PMF.uniformOfFintype F
  let r2 ← PMF.uniformOfFintype F
  pure (encryptWithSecretPair hf st.secretKey
    (selectedMessage right m0 m1) (r1 • g1) (r2 • g2))

/-- Exact instrumentation of G2Raw with the exponent-collision ghost flag. -/
noncomputable def g2PairTrackedChallenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let r1 ← PMF.uniformOfFintype F
  let r2 ← PMF.uniformOfFintype F
  let badNow := decide (r1 = r2)
  set { st with pairBad := st.pairBad || badNow }
  pure (encryptWithSecretPair hf st.secretKey
    (selectedMessage right m0 m1) (r1 • g1) (r2 • g2))

/-- Coupling bridge for conditioning. On the bad branch it resamples a
distinct pair and remembers that this happened in ghost state. Away from
`pairBad`, it is pointwise identical to G2Raw. -/
noncomputable def g2CoupledChallenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let r1 ← PMF.uniformOfFintype F
  let r2 ← PMF.uniformOfFintype F
  if _h : r1 = r2 then
    let pair ← PMF.uniformOfFintype (DistinctPair F)
    set { st with pairBad := true }
    pure (encryptWithSecretPair hf st.secretKey
      (selectedMessage right m0 m1) (pair.val.1 • g1) (pair.val.2 • g2))
  else
    set { st with pairBad := st.pairBad }
    pure (encryptWithSecretPair hf st.secretKey
      (selectedMessage right m0 m1) (r1 • g1) (r2 • g2))

/-- Paper G2: sample a uniformly random pair conditioned to be distinct. -/
noncomputable def g2Challenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let pair ← PMF.uniformOfFintype (DistinctPair F)
  set { st with pairBad := false }
  pure (encryptWithSecretPair hf st.secretKey
    (selectedMessage right m0 m1) (pair.val.1 • g1) (pair.val.2 • g2))

/-- G2 decryption, instrumented with the paper's event R3. -/
noncomputable def g2DecryptRule
    (hf : HashFamily F V HashKey) (w : F) (ct : Ciphertext V) :
    GameM F V HashKey (Option V) := do
  let st ← get
  let badNow := rejectionEvent hf w st.secretKey ct
  set { st with rejectionBad := st.rejectionBad || badNow }
  pure (decrypt hf st.secretKey ct)

/-- G3 decryption uses the special rejection rule and records exactly the
same candidate bad event as G2. -/
noncomputable def g3DecryptRule
    (hf : HashFamily F V HashKey) (w : F) (ct : Ciphertext V) :
    GameM F V HashKey (Option V) := do
  let st ← get
  let badNow := rejectionEvent hf w st.secretKey ct
  set { st with rejectionBad := st.rejectionBad || badNow }
  pure (specialDecrypt hf w st.secretKey ct)

/-- G4 challenge: replace the message-dependent payload by an independent
uniform scalar multiple of `g₁`. -/
noncomputable def g4Challenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (_right : Bool) (_m0 _m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let pair ← PMF.uniformOfFintype (DistinctPair F)
  let r ← PMF.uniformOfFintype F
  set { st with pairBad := false }
  pure (authenticate hf st.secretKey
    (pair.val.1 • g1) (pair.val.2 • g2) (r • g1))

/-- G5 decryption adds the target-collision rejection before G3's special
rule. An `if` on `target.isSome` replaces a match on the challenge state. -/
noncomputable def g5DecryptRule
    (hf : HashFamily F V HashKey) (w : F) (ct : Ciphertext V) :
    GameM F V HashKey (Option V) := do
  let st ← get
  if htarget : st.target.isSome then
    let target := st.target.get htarget
    let collision := targetHashCollision hf st.secretKey target ct
    if collision then
      set { st with hashBad := true }
      pure none
    else
      g3DecryptRule hf w ct
  else
    g3DecryptRule hf w ct

/- The games themselves are intentionally tiny applications of the common
driver. This makes each neighboring pair differ in one named rule only. -/

noncomputable def G0
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g0Challenge hf g1 g2) (normalDecryptRule hf)

noncomputable def G1
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g1Challenge hf g1 g2) (normalDecryptRule hf)

noncomputable def G2Raw
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2RawChallenge hf g1 g2) (normalDecryptRule hf)

noncomputable def G2PairTracked
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2PairTrackedChallenge hf g1 g2) (normalDecryptRule hf)

noncomputable def G2Coupled
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2CoupledChallenge hf g1 g2) (normalDecryptRule hf)

noncomputable def G2
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (normalDecryptRule hf)

noncomputable def G2Tracked
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (g2DecryptRule hf w)

noncomputable def G3
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (g3DecryptRule hf w)

noncomputable def G4
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (_right : Bool) :=
  gameOracle hf g1 g2 false (g4Challenge hf g1 g2) (g3DecryptRule hf w)

noncomputable def G5
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (_right : Bool) :=
  gameOracle hf g1 g2 false (g4Challenge hf g1 g2) (g5DecryptRule hf w)

/-- G4 no longer inspects the challenge bit.  Quantifying both bits makes this
usable without duplicating `true`/`false` versions of the fact. -/
theorem G4_bit_independent
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (right₁ right₂ : Bool) :
    G4 hf g1 g2 w right₁ = G4 hf g1 g2 w right₂ := rfl

/-- G5 is likewise independent of the challenge bit. -/
theorem G5_bit_independent
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (right₁ right₂ : Bool) :
    G5 hf g1 g2 w right₁ = G5 hf g1 g2 w right₂ := rfl

theorem G4_left_eq_right
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) :
    G4 hf g1 g2 w false = G4 hf g1 g2 w true :=
  G4_bit_independent hf g1 g2 w false true

/-!
## Local hop lemmas

Each lemma isolates an exact abstraction, a correct-until-bad argument, or
a probability calculation used in the final chain.
-/

/-- G2Raw--G2PairTracked: exact ghost instrumentation. The abstraction
forgets `pairBad`, so this hop does not consume statistical error. -/
theorem hop_G2Raw_G2PairTracked
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    ObsEq (G2Raw hf g1 g2 right) (G2PairTracked hf g1 g2 right) := by
  obs_eq_by_abstraction ←
    (forgetPairBadAbstraction (F := F) (V := V) (HashKey := HashKey))
  all_goals simp [G2Raw, G2PairTracked, gameOracle,
    g2RawChallenge, g2PairTrackedChallenge, normalDecryptRule,
    forgetPairBadAbstraction, correctAbstractionDiagSimps, sRState, sPMF, *]
  all_goals (try split) <;>
    simp_all [initialGameState, sRState, sPMF]

/-- G2PairTracked--G2Coupled: a correct-until-`pairBad` hop. Its bound is
`1 / |F|`, independent of the adversary's decryption-query count. -/
theorem G2PairTracked_G2Coupled_correctUntilBad
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    IsCorrectUntilBad (IndCcaSpec F V HashKey) pairBadFlag
      (G2PairTracked hf g1 g2 right).initialState
      (G2Coupled hf g1 g2 right).initialState
      (G2PairTracked hf g1 g2 right).queries
      (G2Coupled hf g1 g2 right).queries := by
  classical
  constructor
  · intro i st hb p hp
    cases i <;>
      simp [G2PairTracked, gameOracle, g2PairTrackedChallenge, normalDecryptRule,
        sRState, sPMF] at hp
    all_goals (try split_ifs at hp) <;> simp_all [pairBadFlag]
    all_goals aesop
  · intro i st hb p hp
    cases i <;>
      simp [G2Coupled, gameOracle, g2CoupledChallenge, normalDecryptRule,
        sRState, sPMF] at hp
    all_goals (try split_ifs at hp) <;> simp_all [pairBadFlag]
    all_goals aesop
  · intros; rfl
  · intro i st hb out st' hb'
    cases i with
    | getPublicKey => rfl
    | decrypt ct => rfl
    | challenge m0 m1 =>
      simp [G2PairTracked, G2Coupled, gameOracle, g2PairTrackedChallenge,
        g2CoupledChallenge, sRState, sPMF]
      split_ifs with ht
      · rfl
      · rw [PMF.bind_apply, PMF.bind_apply]
        apply tsum_congr
        intro a
        congr 1
        rw [PMF.bind_apply, PMF.bind_apply]
        apply tsum_congr
        intro b
        have hne (ct : Ciphertext V) :
            st' ≠ { st with target := some ct, pairBad := true } := by
          intro h
          have := congrArg GameState.pairBad h
          simp_all [pairBadFlag]
        by_cases he : a = b
        · simp [he, PMF.bind_bind, PMF.pure_apply, hne, PMF.bind_apply]
        · simp [he]

/-- Bellman valuation for the exponent-pair conditioning event.  Before the
single challenge it reserves exactly `1 / |F|`; after a good challenge the
event can no longer occur, while a state in which it occurred has value one.
The query budget is intentionally unused because the challenge is ask-once. -/
noncomputable def pairBadValuation
    (st : GameState F V HashKey) (_q : ENat) : NNReal :=
  if st.pairBad then 1
  else if st.target.isSome then 0
  else (Fintype.card F : NNReal)⁻¹

/-- The pair valuation is preserved by every query of the tracked game.  The
only probabilistic calculation is that two independent uniform field elements
are equal with probability `1 / |F|`. -/
theorem pairBadValuation_valid
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    IsValidBadEventBound (IndCcaSpec F V HashKey) pairBadFlag
      (G2PairTracked hf g1 g2 right).queries
      (pairBadValuation (F := F) (V := V) (HashKey := HashKey)) := by
  classical
  have hc : (1 : NNReal) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  constructor
  · intro st q
    unfold pairBadValuation
    split_ifs <;> simp_all
  · intro st q hb
    simp_all [pairBadValuation, pairBadFlag]
  · intro i st q
    cases i <;>
      simp [G2PairTracked, gameOracle, g2PairTrackedChallenge, normalDecryptRule,
        sRState, sPMF]
    all_goals (try split_ifs) <;>
      simp_all [pairBadValuation, PMF.expectation_bind]
    by_cases hb : st.pairBad = true
    · simp [hb]
    · have he (a : F) : (PMF.uniformOfFintype F).expectation
          (fun b => ((if a = b then 1 else 0 : NNReal) : ENNReal)) =
          (Fintype.card F : ENNReal)⁻¹ := by
        simp [PMF.expectation, apply_ite]
      simp [hb, he]

/-- Initialization is good and no challenge has yet been issued, hence the
expected initial value of `pairBadValuation` is exactly `1 / |F|`. -/
theorem pairBadValuation_initial
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) (q : ENat) :
    initialBadEventBound
        (G2PairTracked hf g1 g2 right).initialState
        (pairBadValuation (F := F) (V := V) (HashKey := HashKey)) q =
      (Fintype.card F : NNReal)⁻¹ := by
  classical
  apply initialBadEventBound_constant_on_support
  intro st hs
  simp [G2PairTracked, gameOracle, initialGameState] at hs
  obtain ⟨pk, sk, _, rfl⟩ := hs
  rfl

theorem hop_G2PairTracked_G2Coupled
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (q : ENat) :
    ApproxEq q ((Fintype.card F : NNReal)⁻¹)
      (G2PairTracked hf g1 g2 right) (G2Coupled hf g1 g2 right) := by
  rw [← pairBadValuation_initial hf g1 g2 right q]
  by_correct_until_bad pairBadFlag using pairBadValuation
  · exact G2PairTracked_G2Coupled_correctUntilBad hf g1 g2 right
  · exact pairBadValuation_valid hf g1 g2 right

/-- G2Coupled--G2: erase `pairBad`; the visible pair is uniformly distributed
over distinct pairs. This is an exact randomized-abstraction/coupling hop. -/
theorem hop_G2Coupled_G2
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    ObsEq (G2Coupled hf g1 g2 right) (G2 hf g1 g2 right) := by
  obs_eq_by_abstraction
    (forgetPairBadAbstraction (F := F) (V := V) (HashKey := HashKey))
  all_goals simp [G2Coupled, G2, gameOracle, g2CoupledChallenge, g2Challenge,
    normalDecryptRule, forgetPairBadAbstraction, correctAbstractionDiagSimps,
    initialGameState, sRState, sPMF]
  all_goals (try split) <;> simp_all [sRState, sPMF]
  rename_i m0 m1 st ht
  let k : DistinctPair F → PMF (Option (Ciphertext V) × GameState F V HashKey) := fun p =>
    let ct := encryptWithSecretPair hf st.secretKey
      (selectedMessage right m0 m1) (p.val.1 • g1) (p.val.2 • g2)
    pure (some ct, { st with target := some ct, pairBad := false })
  have h := congrArg (fun p : PMF (DistinctPair F) => p.bind k)
    (PMF.uniformOfFintype_resample (fun p : F × F => p.1 ≠ p.2))
  simp only [PMF.bind_bind, PMF.uniformOfFintype_prod_bind] at h
  refine Eq.trans ?_ h
  congr 1
  funext a
  congr 1
  funext b
  by_cases hab : a = b <;> simp [hab, k, PMF.bind_bind]

/-- G2--G2Tracked: exact instrumentation of R3. Forgetting
`rejectionBad` recovers paper G2. -/
theorem hop_G2_G2Tracked
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :
    ObsEq (G2 hf g1 g2 right) (G2Tracked hf g1 g2 w right) := by
  obs_eq_by_abstraction ←
    (forgetRejectionBadAbstraction (F := F) (V := V) (HashKey := HashKey))
  all_goals simp [G2, G2Tracked, gameOracle,
    g2Challenge, g2DecryptRule, normalDecryptRule,
    forgetRejectionBadAbstraction, correctAbstractionDiagSimps, sRState, sPMF, *]
  all_goals (try split) <;>
    simp_all [initialGameState, sRState, sPMF]

omit [Fintype F] [DecidableEq F] in
/-- Outside R3, the ordinary and special decryption rules agree. -/
theorem decrypt_eq_specialDecrypt_of_not_bad
    (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (ct : Ciphertext V)
    (h : rejectionEvent hf w sk ct = false) :
    decrypt hf sk ct = specialDecrypt hf w sk ct := by
  classical
  by_cases hu : ct.u2 = w • ct.u1
  · have hv : valid hf sk ct ↔ collapsedValid hf w sk ct := by
      unfold valid collapsedValid SecretKey.collapsedX SecretKey.collapsedY
      rw [hu]
      dsimp
      have he : (sk.x1 + hf.hash sk.hashKey ct.u1 (w • ct.u1) ct.e * sk.y1) • ct.u1 +
          (sk.x2 + hf.hash sk.hashKey ct.u1 (w • ct.u1) ct.e * sk.y2) • (w • ct.u1) =
          (sk.x1 + w * sk.x2 + hf.hash sk.hashKey ct.u1 (w • ct.u1) ct.e *
            (sk.y1 + w * sk.y2)) • ct.u1 := by module
      rw [he]
    have hz : sk.z1 • ct.u1 + sk.z2 • ct.u2 = sk.collapsedZ w • ct.u1 := by
      rw [hu]
      unfold SecretKey.collapsedZ
      module
    simp only [decrypt, specialDecrypt, if_pos hu, hv, hz]
  · have hv : ¬ valid hf sk ct := by
      simpa [rejectionEvent, hu] using h
    simp [decrypt, specialDecrypt, hu, hv]

/-- The local identical-until-bad statement behind the paper's G2--G3
transition. It deliberately makes no numerical claim about R3 yet. -/
theorem G2Tracked_G3_correctUntilBad
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (right : Bool) :
    IsCorrectUntilBad (IndCcaSpec F V HashKey) rejectionBadFlag
      (G2Tracked hf g1 g2 w right).initialState
      (G3 hf g1 g2 w right).initialState
      (G2Tracked hf g1 g2 w right).queries
      (G3 hf g1 g2 w right).queries := by
  classical
  constructor
  · intro i st hb p hp
    cases i <;>
      simp [G2Tracked, gameOracle, g2Challenge, g2DecryptRule,
        sRState, sPMF] at hp
    all_goals (try split_ifs at hp) <;>
      simp_all [rejectionBadFlag]
    all_goals aesop
  · intro i st hb p hp
    cases i <;>
      simp [G3, gameOracle, g2Challenge, g3DecryptRule,
        sRState, sPMF] at hp
    all_goals (try split_ifs at hp) <;>
      simp_all [rejectionBadFlag]
    all_goals aesop
  · intros; rfl
  · intro i st hb out st' hb'
    cases i with
    | getPublicKey => rfl
    | challenge m0 m1 => rfl
    | decrypt ct =>
      simp only [G2Tracked, G3, gameOracle, g2DecryptRule, g3DecryptRule,
        rejectionBadFlag, sRState, sPMF] at *
      by_cases ht : st.target = some ct
      · simp [ht]
      · by_cases he : rejectionEvent hf w st.secretKey ct = true
        · have hne : st' ≠ { st with rejectionBad := true } := by
            intro h; have := congrArg GameState.rejectionBad h
            simp_all
          simp [ht, he, sPMF, PMF.pure_apply, hne]
        · have he' : rejectionEvent hf w st.secretKey ct = false := by simpa using he
          simp [ht, decrypt_eq_specialDecrypt_of_not_bad hf w st.secretKey ct he']


/-- Once a Bellman valuation for R3 is supplied, the
correct-until-bad theorem turns it directly into the G2--G3 epsilon hop. The
paper's G4/G5 argument will later provide the useful numerical valuation. -/
theorem hop_G2Tracked_G3_of_bound
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (right : Bool) (bound : GameState F V HashKey → ENat → NNReal)
    (hBound : IsValidBadEventBound (IndCcaSpec F V HashKey)
      rejectionBadFlag (G2Tracked hf g1 g2 w right).queries bound)
    (q : ENat) :
    ApproxEq q
      (initialBadEventBound
        (G2Tracked hf g1 g2 w right).initialState bound q)
      (G2Tracked hf g1 g2 w right) (G3 hf g1 g2 w right) := by
  by_correct_until_bad rejectionBadFlag using bound
  · exact G2Tracked_G3_correctUntilBad hf g1 g2 w right
  · exact hBound

/-! ### The hidden authentication coordinate

After the challenge, public verification exponents and the challenge's hash
fix `x₂ + α*y₂`, while `y₂` remains the coordinate to reconstruct. The following
lemmas describe one fresh-coordinate sample. They do not assert that it stays
unconditioned after rejected adaptive queries.
-/

/-- Resample `y₂`, retaining the public exponents and the authentication
combination for a target hash `alpha`. -/
def refreshAuthKey (w alpha : F) (sk : SecretKey F HashKey) (y : F) : SecretKey F HashKey :=
  let x := sk.x2 + alpha * sk.y2 - alpha * y
  { sk with
    x1 := sk.collapsedX w - w * x
    x2 := x
    y1 := sk.collapsedY w - w * y
    y2 := y }

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshAuthKey_hashKey (w alpha : F) (sk : SecretKey F HashKey) (y : F) :
    (refreshAuthKey w alpha sk y).hashKey = sk.hashKey := rfl

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshAuthKey_collapsedZ (w alpha : F) (sk : SecretKey F HashKey) (y : F) :
    (refreshAuthKey w alpha sk y).collapsedZ w = sk.collapsedZ w := rfl

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshAuthKey_collapsedX (w alpha : F) (sk : SecretKey F HashKey) (y : F) :
    (refreshAuthKey w alpha sk y).collapsedX w = sk.collapsedX w := by
  simp [refreshAuthKey, SecretKey.collapsedX]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshAuthKey_collapsedY (w alpha : F) (sk : SecretKey F HashKey) (y : F) :
    (refreshAuthKey w alpha sk y).collapsedY w = sk.collapsedY w := by
  simp [refreshAuthKey, SecretKey.collapsedY]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshAuthKey_targetCombination (w alpha : F)
    (sk : SecretKey F HashKey) (y : F) :
    (refreshAuthKey w alpha sk y).x2 + alpha * (refreshAuthKey w alpha sk y).y2 =
      sk.x2 + alpha * sk.y2 := by
  simp [refreshAuthKey]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshAuthKey_publicKey (g1 g2 : V) (w alpha : F)
    (sk : SecretKey F HashKey) (y : F) (hg2 : g2 = w • g1) :
    publicKey g1 g2 (refreshAuthKey w alpha sk y) = publicKey g1 g2 sk := by
  simp only [publicKey, refreshAuthKey, SecretKey.collapsedX, SecretKey.collapsedY, hg2]
  congr 1 <;> module

omit [Fintype F] [DecidableEq F] in
@[simp] theorem refreshAuthKey_specialDecrypt (hf : HashFamily F V HashKey) (w alpha : F)
    (sk : SecretKey F HashKey) (y : F) (ct : Ciphertext V) :
    specialDecrypt hf w (refreshAuthKey w alpha sk y) ct = specialDecrypt hf w sk ct := by
  simp only [specialDecrypt, collapsedValid, refreshAuthKey_hashKey,
    refreshAuthKey_collapsedX, refreshAuthKey_collapsedY, refreshAuthKey_collapsedZ]
  split_ifs <;> rfl

/-- The constant term of candidate verification after reconstructing the
hidden authentication coordinate. -/
def authOffset (hf : HashFamily F V HashKey) (g1 : V) (hg1 : CyclicGenerator F V g1)
    (w alpha : F) (sk : SecretKey F HashKey) (ct : Ciphertext V) : F :=
  let a := hf.hash sk.hashKey ct.u1 ct.u2 ct.e
  (sk.collapsedX w + a * sk.collapsedY w) * hg1.coordinate ct.u1 +
    (sk.x2 + alpha * sk.y2) * (hg1.coordinate ct.u2 - w * hg1.coordinate ct.u1)

/-- This coefficient is nonzero for an inconsistent ciphertext whose hash
is different from the target's hash. -/
def authSlope (hf : HashFamily F V HashKey) (g1 : V) (hg1 : CyclicGenerator F V g1)
    (w alpha : F) (sk : SecretKey F HashKey) (ct : Ciphertext V) : F :=
  (hf.hash sk.hashKey ct.u1 ct.u2 ct.e - alpha) *
    (hg1.coordinate ct.u2 - w * hg1.coordinate ct.u1)

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
theorem valid_refreshAuthKey_iff (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w alpha : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (y : F) :
    valid hf (refreshAuthKey w alpha sk y) ct ↔
      hg1.coordinate ct.v = authOffset hf g1 hg1 w alpha sk ct +
        authSlope hf g1 hg1 w alpha sk ct * y := by
  have rhs :
      ((refreshAuthKey w alpha sk y).x1 +
          hf.hash sk.hashKey ct.u1 ct.u2 ct.e * (refreshAuthKey w alpha sk y).y1) • ct.u1 +
      ((refreshAuthKey w alpha sk y).x2 +
          hf.hash sk.hashKey ct.u1 ct.u2 ct.e * (refreshAuthKey w alpha sk y).y2) • ct.u2 =
      (authOffset hf g1 hg1 w alpha sk ct + authSlope hf g1 hg1 w alpha sk ct * y) • g1 := by
    simp only [refreshAuthKey, authOffset, authSlope, SecretKey.collapsedX,
      SecretKey.collapsedY]
    conv_lhs => arg 1; arg 2; rw [← hg1.reconstruct ct.u1]
    conv_lhs => arg 2; arg 2; rw [← hg1.reconstruct ct.u2]
    module
  simp only [valid, refreshAuthKey_hashKey]
  rw [rhs]
  constructor
  · intro h
    simpa only [hg1.coordinate_smul] using congrArg hg1.coordinate h
  · intro h
    rw [← hg1.reconstruct ct.v, h]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
theorem authSlope_ne_zero (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w alpha : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (hu : ct.u2 ≠ w • ct.u1)
    (ha : hf.hash sk.hashKey ct.u1 ct.u2 ct.e ≠ alpha) :
    authSlope hf g1 hg1 w alpha sk ct ≠ 0 := by
  apply mul_ne_zero (sub_ne_zero.mpr ha)
  apply sub_ne_zero.mpr
  intro h
  apply hu
  rw [← hg1.reconstruct ct.u2, h, mul_smul, hg1.reconstruct]

/-! ### Rejection through simple oracles

The numerical bound belongs to the simple state. The reconstruction maps sample
hidden concrete keys, so their diagrams average over that hidden randomness.
No pointwise Bellman bound on a fixed concrete secret key is required.

The two diagrams and the simple-state invariant are explicit proof obligations;
this structure does not itself supply the Cramer--Shoup cryptographic invariant.
-/

/-- A rejection-hop witness built entirely from existing randomized abstraction
and correct-until-bad rules. The Boolean records the absorbing failure status;
`data` retains the information needed to answer the observable queries. -/
structure RejectionBridge
    (concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)) where
  data : Type
  initialLeft : PMF (data × Bool)
  initialRight : PMF (data × Bool)
  queriesLeft : QueryImpl (IndCcaSpec F V HashKey) (RState (data × Bool))
  queriesRight : QueryImpl (IndCcaSpec F V HashKey) (RState (data × Bool))
  reconstructLeft : data × Bool → PMF concreteLeft.stateType
  reconstructRight : data × Bool → PMF concreteRight.stateType
  left_correct : correctAbstractionBind
    { stateType := data × Bool, initialState := initialLeft, queries := queriesLeft }
    concreteLeft reconstructLeft
  right_correct : correctAbstractionBind
    { stateType := data × Bool, initialState := initialRight, queries := queriesRight }
    concreteRight reconstructRight
  correct_until_bad : IsCorrectUntilBad (IndCcaSpec F V HashKey) Prod.snd
    initialLeft initialRight queriesLeft queriesRight
  bound : data × Bool → ENat → NNReal
  bound_valid : IsValidBadEventBound (IndCcaSpec F V HashKey) Prod.snd queriesLeft bound

namespace RejectionBridge

noncomputable def leftOracle
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    (bridge : RejectionBridge concreteLeft concreteRight) : OracleImpl (IndCcaSpec F V HashKey) where
  stateType := bridge.data × Bool
  initialState := bridge.initialLeft
  queries := bridge.queriesLeft

noncomputable def rightOracle
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    (bridge : RejectionBridge concreteLeft concreteRight) : OracleImpl (IndCcaSpec F V HashKey) where
  stateType := bridge.data × Bool
  initialState := bridge.initialRight
  queries := bridge.queriesRight

noncomputable def error
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    (bridge : RejectionBridge concreteLeft concreteRight) (q : ENat) : NNReal :=
  initialBadEventBound bridge.initialLeft bridge.bound q

/-- Full game -> simple game -> error step -> simple game -> full game.
The randomized maps run from simple states to distributions of full states. -/
noncomputable def hop
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    (bridge : RejectionBridge concreteLeft concreteRight) (q : ENat) :
    IndistinguishableI Assumptions q concreteLeft concreteRight := by
  game_hopping_basic [concreteLeft, bridge.leftOracle, bridge.rightOracle, concreteRight]
  · obs_eq
    exact (correctAbstractionBindImpliesObsEq _ _ bridge.reconstructLeft
      bridge.left_correct).symm
  · by_correct_until_bad Prod.snd using bridge.bound
    · exact bridge.correct_until_bad
    · exact bridge.bound_valid
  · obs_eq
    exact correctAbstractionBindImpliesObsEq _ _ bridge.reconstructRight bridge.right_correct

@[simp] theorem hop_statisticalError
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    (bridge : RejectionBridge concreteLeft concreteRight) (q : ENat) :
    (bridge.hop Assumptions q).statisticalError = bridge.error q := by
  simp [hop, error, leftOracle, IndistinguishableI.statisticalError,
    Indistinguishable.of_ObsEq]

/-- Instantiate the bridge with the explicit absorbing failure process.
Its Bellman and correct-until-bad proofs are already discharged; only the
concrete randomized abstraction diagrams remain to be supplied. -/
noncomputable def ofFailureProcess
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    {A : Type} (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failedLeft failedRight : QueryImpl (IndCcaSpec F V HashKey) (RState A))
    (reconstructLeft : A × Bool → PMF concreteLeft.stateType)
    (reconstructRight : A × Bool → PMF concreteRight.stateType)
    (hLeft : correctAbstractionBind (failureOracle p hp initial good failedLeft)
      concreteLeft reconstructLeft)
    (hRight : correctAbstractionBind (failureOracle p hp initial good failedRight)
      concreteRight reconstructRight) : RejectionBridge concreteLeft concreteRight where
  data := A
  initialLeft := (failureOracle p hp initial good failedLeft).initialState
  initialRight := (failureOracle p hp initial good failedRight).initialState
  queriesLeft := (failureOracle p hp initial good failedLeft).queries
  queriesRight := (failureOracle p hp initial good failedRight).queries
  reconstructLeft := reconstructLeft
  reconstructRight := reconstructRight
  left_correct := hLeft
  right_correct := hRight
  correct_until_bad := failureOracles_correctUntilBad p hp initial good failedLeft failedRight
  bound := failureValuation p
  bound_valid := failureOracle_bound p hp initial good failedLeft

@[simp] theorem ofFailureProcess_error
    {concreteLeft concreteRight : OracleImpl (IndCcaSpec F V HashKey)}
    {A : Type} (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failedLeft failedRight : QueryImpl (IndCcaSpec F V HashKey) (RState A))
    (reconstructLeft : A × Bool → PMF concreteLeft.stateType)
    (reconstructRight : A × Bool → PMF concreteRight.stateType)
    (hLeft : correctAbstractionBind (failureOracle p hp initial good failedLeft)
      concreteLeft reconstructLeft)
    (hRight : correctAbstractionBind (failureOracle p hp initial good failedRight)
      concreteRight reconstructRight) (q : ENat) :
    (ofFailureProcess p hp initial good failedLeft failedRight
      reconstructLeft reconstructRight hLeft hRight).error q = failureBudget p q :=
  failureOracle_initialBound p hp initial good failedLeft q

end RejectionBridge

/-! ### The message-mask coupling

Refresh the unused mask coordinate before the challenge, preserving the public
coordinate. Distinct challenge exponents make its contribution an invertible
affine map, so the payload is uniform. Both games then forget the hidden
coordinate. All three abstractions retain the bad-event flags.
-/

/-- Resample the hidden mask coordinate while preserving its public coordinate. -/
def refreshMaskKey (w : F) (sk : SecretKey F HashKey) (z : F) : SecretKey F HashKey :=
  { sk with z1 := sk.collapsedZ w - w * z, z2 := z }

omit [Fintype F] [DecidableEq F] in
@[simp] theorem refreshMaskKey_collapsedZ (w : F) (sk : SecretKey F HashKey) (z : F) :
    (refreshMaskKey w sk z).collapsedZ w = sk.collapsedZ w := by
  simp [refreshMaskKey, SecretKey.collapsedZ]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshMaskKey_publicKey (g1 g2 : V) (w : F) (sk : SecretKey F HashKey)
    (z : F) (hg2 : g2 = w • g1) :
    publicKey g1 g2 (refreshMaskKey w sk z) = publicKey g1 g2 sk := by
  simp only [publicKey, refreshMaskKey, SecretKey.collapsedZ, hg2]
  congr 1
  module

omit [Fintype F] [DecidableEq F] in
@[simp] theorem refreshMaskKey_specialDecrypt (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (z : F) (ct : Ciphertext V) :
    specialDecrypt hf w (refreshMaskKey w sk z) ct = specialDecrypt hf w sk ct := by
  simp [specialDecrypt, collapsedValid, SecretKey.collapsedX, SecretKey.collapsedY,
    refreshMaskKey, SecretKey.collapsedZ]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem refreshMaskKey_rejectionEvent (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (z : F) (ct : Ciphertext V) :
    rejectionEvent hf w (refreshMaskKey w sk z) ct = rejectionEvent hf w sk ct := rfl

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
@[simp] theorem refreshMaskKey_authenticate (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (z : F) (u1 u2 e : V) :
    authenticate hf (refreshMaskKey w sk z) u1 u2 e = authenticate hf sk u1 u2 e := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem refreshMaskKey_refresh (w : F) (sk : SecretKey F HashKey) (z z' : F) :
    refreshMaskKey w (refreshMaskKey w sk z) z' = refreshMaskKey w sk z' := by
  simp [refreshMaskKey, SecretKey.collapsedZ]

noncomputable def refreshMask (w : F) (st : GameState F V HashKey) :
    PMF (GameState F V HashKey) := do
  let z ← PMF.uniformOfFintype F
  pure { st with secretKey := refreshMaskKey w st.secretKey z }

/-- Reveal a fresh hidden coordinate only while no challenge has been issued. -/
noncomputable def refreshBeforeChallenge (w : F) (st : GameState F V HashKey) :
    PMF (GameState F V HashKey) :=
  if st.target.isSome then pure st else refreshMask w st

noncomputable def g3FreshChallenge (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let st' ← refreshMask w st
  set st'
  g2Challenge hf g1 g2 right m0 m1

/-- G3 with its hidden mask coordinate sampled lazily at the challenge. -/
noncomputable def G3Fresh (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g3FreshChallenge hf g1 g2 w) (g3DecryptRule hf w)

omit [DecidableEq F] in
private lemma uniform_translate {A : Type} (c : F) (f : F → PMF A) :
    (PMF.uniformOfFintype F).bind (fun x => f (x + c)) = (PMF.uniformOfFintype F).bind f := by
  simpa using (PMF.bind_uniformOfFintype_equiv (Equiv.addRight c) f).symm

omit [DecidableEq F] in
private lemma uniform_refresh {A : Type} (w : F) (f : F → F → PMF A) :
    (PMF.uniformOfFintype F).bind (fun z1 =>
      (PMF.uniformOfFintype F).bind (fun z2 =>
        (PMF.uniformOfFintype F).bind (fun z => f (z1 + w * z2 - w * z) z))) =
    (PMF.uniformOfFintype F).bind (fun z1 => (PMF.uniformOfFintype F).bind (f z1)) := by
  rw [PMF.bind_comm]
  conv_lhs => arg 2; ext z2; rw [PMF.bind_comm]
  simp_rw [show ∀ z1 z2 z : F, z1 + w * z2 - w * z = z1 + (w * z2 - w * z) from
    fun _ _ _ => by ring]
  conv_lhs =>
    arg 2; ext z2; arg 2; ext z
    rw [uniform_translate (w * z2 - w * z) (fun x => f x z)]
  simp only [PMF.bind_const]
  exact PMF.bind_comm _ _ _

omit [DecidableEq F] [DecidableEq V] in
private lemma refreshMask_initial (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) :
    (initialGameState hf g1 g2).bind (refreshMask w) = initialGameState hf g1 g2 := by
  simp [initialGameState, keyGen, refreshMask, refreshMaskKey, SecretKey.collapsedZ,
    sPMF]
  iterate 5 (congr 1; funext)
  rename_i hk x1 x2 y1 y2
  exact uniform_refresh w (fun z1 z2 => pure
    ({ secretKey := ⟨hk, x1, x2, y1, y2, z1, z2⟩
       target := none
       pairBad := false
       rejectionBad := false
       hashBad := false } : GameState F V HashKey))

lemma G3Fresh_G3 (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool)
    (hg2 : g2 = w • g1) : ObsEq (G3Fresh hf g1 g2 w right) (G3 hf g1 g2 w right) := by
  obs_eq_by_rand_abstraction (refreshBeforeChallenge w)
  all_goals simp [G3Fresh, G3, gameOracle, g3FreshChallenge, g2Challenge, g3DecryptRule,
    refreshBeforeChallenge, refreshMask, correctAbstractionDiagSimps, sRState, sPMF]
  all_goals (try split_ifs) <;> simp_all [sPMF, refreshMaskKey_publicKey]
  simpa [initialGameState, refreshBeforeChallenge, sPMF] using
    refreshMask_initial hf g1 (w • g1) w

/-- Forget the hidden coordinate after its contribution to the payload has been sampled. -/
def collapseMaskState (w : F) (st : GameState F V HashKey) : GameState F V HashKey :=
  { st with secretKey := refreshMaskKey w st.secretKey 0 }

/-- Common abstraction of the lazy-mask game and G4. -/
noncomputable def G4Canonical (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) :=
  { G4 hf g1 g2 w false with
    initialState := (initialGameState hf g1 g2).map (collapseMaskState w) }

lemma G4_G4Canonical (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool)
    (hg2 : g2 = w • g1) : ObsEq (G4 hf g1 g2 w right) (G4Canonical hf g1 g2 w) := by
  obs_eq_by_abstraction (collapseMaskState w)
  all_goals simp [G4Canonical, G4, gameOracle, g4Challenge, g3DecryptRule,
    collapseMaskState, correctAbstractionDiagSimps, sRState, sPMF]
  all_goals (try split_ifs) <;> simp_all [sPMF, refreshMaskKey_publicKey]

omit [DecidableEq F] in
private lemma uniform_affine {A : Type} (a b : F) (ha : a ≠ 0) (f : F → PMF A) :
    (PMF.uniformOfFintype F).bind (fun z => f (b + a * z)) =
    (PMF.uniformOfFintype F).bind f := by
  simpa using (PMF.bind_uniformOfFintype_equiv
    ((Equiv.mulLeft₀ a ha).trans (Equiv.addLeft b)) f).symm

open scoped Classical in
/-- For a fresh uniform authentication coordinate, a non-collision forgery
accepts with probability exactly `1 / |F|`. The adaptive bridge must separately
justify its distribution after earlier rejected queries. -/
theorem freshAuth_acceptance (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w alpha : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (hu : ct.u2 ≠ w • ct.u1)
    (ha : hf.hash sk.hashKey ct.u1 ct.u2 ct.e ≠ alpha) :
    ((PMF.uniformOfFintype F).bind (fun y =>
      PMF.pure (decide (valid hf (refreshAuthKey w alpha sk y) ct)))) true =
      (Fintype.card F : ENNReal)⁻¹ := by
  classical
  simp_rw [valid_refreshAuthKey_iff hf g1 hg1 w alpha sk ct]
  rw [uniform_affine _ _ (authSlope_ne_zero hf g1 hg1 w alpha sk ct hu ha)
    (fun v => PMF.pure (decide (hg1.coordinate ct.v = v)))]
  simp [PMF.bind_apply, PMF.pure_apply, eq_comm]

/-- The one hidden coordinate tested by an inconsistent non-collision query. -/
def authGuess (hf : HashFamily F V HashKey) (g1 : V) (hg1 : CyclicGenerator F V g1)
    (w alpha : F) (sk : SecretKey F HashKey) (ct : Ciphertext V) : F :=
  (hg1.coordinate ct.v - authOffset hf g1 hg1 w alpha sk ct) /
    authSlope hf g1 hg1 w alpha sk ct

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
theorem valid_refreshAuthKey_iff_guess (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w alpha : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (y : F) (hu : ct.u2 ≠ w • ct.u1)
    (ha : hf.hash sk.hashKey ct.u1 ct.u2 ct.e ≠ alpha) :
    valid hf (refreshAuthKey w alpha sk y) ct ↔ y = authGuess hf g1 hg1 w alpha sk ct := by
  rw [valid_refreshAuthKey_iff, authGuess, eq_div_iff
    (authSlope_ne_zero hf g1 hg1 w alpha sk ct hu ha)]
  constructor <;> intro h <;> linear_combination -h

open scoped Classical in
/-- Exact conditional acceptance rate when the hidden coordinate is uniform
on a nonempty set of still-compatible values. Earlier rejections can shrink
this set, so the denominator is its current size, rather than always `|F|`. -/
theorem remainingAuth_acceptance (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w alpha : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (remaining : Finset F) (hr : remaining.Nonempty)
    (hu : ct.u2 ≠ w • ct.u1)
    (ha : hf.hash sk.hashKey ct.u1 ct.u2 ct.e ≠ alpha) :
    ((PMF.uniformOfFinset remaining hr).bind (fun y =>
      PMF.pure (decide (valid hf (refreshAuthKey w alpha sk y) ct)))) true =
      if authGuess hf g1 hg1 w alpha sk ct ∈ remaining then
        (remaining.card : ENNReal)⁻¹ else 0 := by
  classical
  simp_rw [valid_refreshAuthKey_iff_guess hf g1 hg1 w alpha sk ct _ hu ha]
  simp [PMF.bind_apply, PMF.pure_apply, PMF.uniformOfFinset_apply, eq_comm]

/-- The randomized reconstruction map for the post-challenge authentication
coordinate. Its compatible set must be maintained by the concrete bridge. -/
noncomputable def reconstructAuthState (w alpha : F) (st : GameState F V HashKey)
    (remaining : Finset F) (hr : remaining.Nonempty) : PMF (GameState F V HashKey) := do
  let y ← PMF.uniformOfFinset remaining hr
  pure { st with secretKey := refreshAuthKey w alpha st.secretKey y }

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
private lemma refreshed_challenge (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hg2 : g2 = w • g1)
    (sk : SecretKey F HashKey) (m : V) (r1 r2 z : F) :
    encryptWithSecretPair hf (refreshMaskKey w sk z) m (r1 • g1) (r2 • g2) =
    authenticate hf sk (r1 • g1) (r2 • g2)
      ((sk.collapsedZ w * r1 + hg1.coordinate m + w * (r2 - r1) * z) • g1) := by
  have he : (refreshMaskKey w sk z).z1 • (r1 • g1) +
      (refreshMaskKey w sk z).z2 • (r2 • g2) + m =
      (sk.collapsedZ w * r1 + hg1.coordinate m + w * (r2 - r1) * z) • g1 := by
    conv_lhs => rw [← hg1.reconstruct m]
    simp only [refreshMaskKey, hg2]
    module
  simp only [refreshMaskKey] at he
  simp only [encryptWithSecretPair, refreshMaskKey]
  rw [he]
  rfl

lemma G3Fresh_G4Canonical (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1) :
    ObsEq (G3Fresh hf g1 g2 w right) (G4Canonical hf g1 g2 w) := by
  obs_eq_by_abstraction (collapseMaskState w)
  all_goals simp [G3Fresh, G4Canonical, G4, gameOracle, g3FreshChallenge, g2Challenge,
    g4Challenge, g3DecryptRule, refreshMask, collapseMaskState,
    correctAbstractionDiagSimps, sRState, sPMF]
  all_goals (try split_ifs) <;> simp_all [sPMF, refreshMaskKey_publicKey]
  rename_i m0 m1 st ht
  rw [PMF.bind_comm]
  congr 1
  funext pair
  have ha : w * (pair.val.2 - pair.val.1) ≠ 0 :=
    mul_ne_zero hw (sub_ne_zero.mpr pair.property.symm)
  simp only [refreshed_challenge hf g1 (w • g1) w hg1 rfl]
  exact uniform_affine _ _ ha (fun r =>
    let ct := authenticate hf st.secretKey (pair.val.1 • g1) (pair.val.2 • (w • g1)) (r • g1)
    pure (some ct,
      { st with
        secretKey := refreshMaskKey w st.secretKey 0
        target := some ct
        pairBad := false }))

/-- G3--G4: the paper's coupling that replaces the message mask by a uniform
payload while preserving both the transcript and `rejectionBad`. -/
theorem hop_G3_G4
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0)
    (hg2 : g2 = w • g1) :
    ObsEq (G3 hf g1 g2 w right) (G4 hf g1 g2 w right) := by
  exact obsEq_trans (G3Fresh_G3 hf g1 g2 w right hg2).symm
    (obsEq_trans (G3Fresh_G4Canonical hf g1 g2 w right hg1 hw hg2)
      (G4_G4Canonical hf g1 g2 w right hg2).symm)

/-- G4--G5 proof goal: build the sole hash-comparison collision-resistance reduction
hop here. -/
def HopG4G5Goal
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :
    Type 1 :=
  IndistinguishableI Assumptions none
    (G4 hf g1 g2 w right) (G5 hf g1 g2 w right)

attribute [local game_hopping_unfold]
  ModuleDDHSpec DDHReal DDHRandom CramerShoupDDHReduction
  G0 G1 G2Raw G2PairTracked G2 G2Tracked gameOracle initialGameState
  g0Challenge g1Challenge g2RawChallenge g2PairTrackedChallenge g2Challenge
  normalDecryptRule g2DecryptRule forgetPairBadAbstraction forgetRejectionBadAbstraction

/-!
## IND-CCA game chain

Run the games forward for the left message, switch bits in G4, and run them
backwards for the right message. Exact hops use state abstractions; DDH hops
use a reduction; statistical hops use correct-until-bad with a Bellman valuation.

The rejection hop uses randomized abstractions to simple oracles. Bellman
reasoning takes place there, and exact abstractions transfer the error back.
Constructing the concrete bridge still requires the hidden-key distribution
invariant and the hash-comparison collision-resistance argument.
-/

set_option maxHeartbeats 1000000 in
-- The complete chain normalizes the abstraction diagrams for all 21 hops.
/-- The IND-CCA chain accepts rejection-hop derivations. These may compose
hash-comparison reductions with statistical simple-oracle bridges, using the
existing rules. The full-secret-state rejection valuation is not required. -/
noncomputable def cramerShoupIndCca_of_rejectionHops
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1)
    (hDDH : IndistinguishableI Assumptions none
      (DDHReal (F := F) g1 g2) (DDHRandom (F := F) g1 g2))
    (q : ENat)
    (rejectionHop : ∀ right, IndistinguishableI Assumptions q
      (G2Tracked hf g1 g2 w right) (G3 hf g1 g2 w right)) :
    IndistinguishableI Assumptions q
      (G0 hf g1 g2 false) (G0 hf g1 g2 true) := by
  classical
  game_hopping_basic [
    G0 hf g1 g2 false,
    G1 hf g1 g2 false,
    (CramerShoupDDHReduction hf g1 g2 false) ◇ (DDHReal (F := F) g1 g2),
    (CramerShoupDDHReduction hf g1 g2 false) ◇ (DDHRandom (F := F) g1 g2),
    G2Raw hf g1 g2 false,
    G2PairTracked hf g1 g2 false,
    G2Coupled hf g1 g2 false,
    G2 hf g1 g2 false,
    G2Tracked hf g1 g2 w false,
    G3 hf g1 g2 w false,
    G4 hf g1 g2 w false,
    G4 hf g1 g2 w true,
    G3 hf g1 g2 w true,
    G2Tracked hf g1 g2 w true,
    G2 hf g1 g2 true,
    G2Coupled hf g1 g2 true,
    G2PairTracked hf g1 g2 true,
    G2Raw hf g1 g2 true,
    (CramerShoupDDHReduction hf g1 g2 true) ◇ (DDHRandom (F := F) g1 g2),
    (CramerShoupDDHReduction hf g1 g2 true) ◇ (DDHReal (F := F) g1 g2),
    G1 hf g1 g2 true,
    G0 hf g1 g2 true]
  · by_abstraction id
    all_goals simp [encryptWithSecretPair_eq_encryptWithCoins]
  · by_abstraction ← (fun x => x.1)
  · reduction hDDH
  · by_abstraction (fun x => x.1)
  · by_abstraction ← forgetPairBadAbstraction
  · by_correct_until_bad pairBadFlag using pairBadValuation
    · exact G2PairTracked_G2Coupled_correctUntilBad hf g1 g2 false
    · exact pairBadValuation_valid hf g1 g2 false
  · obs_eq
    exact hop_G2Coupled_G2 hf g1 g2 false
  · by_abstraction ← forgetRejectionBadAbstraction
  · exact rejectionHop false
  · obs_eq
    exact hop_G3_G4 hf g1 g2 w false hg1 hw hg2
  · exact Indistinguishable.reflexive
  · obs_eq
    exact (hop_G3_G4 hf g1 g2 w true hg1 hw hg2).symm
  · exact Indistinguishable.symmetric (rejectionHop true)
  · by_abstraction forgetRejectionBadAbstraction
  · obs_eq
    exact (hop_G2Coupled_G2 hf g1 g2 true).symm
  · by_correct_until_bad ← pairBadFlag using pairBadValuation
    · exact G2PairTracked_G2Coupled_correctUntilBad hf g1 g2 true
    · exact pairBadValuation_valid hf g1 g2 true
  · by_abstraction forgetPairBadAbstraction
  · by_abstraction ← (fun x => x.1)
  · reduction ← hDDH
  · by_abstraction (fun x => x.1)
  · by_abstraction ← id
    all_goals simp [encryptWithSecretPair_eq_encryptWithCoins]

/-- The chain records two DDH uses, two pair-conditioning errors, and the
rejection-event error for each challenge bit. -/
theorem cramerShoupIndCca_of_rejectionHops_statisticalError
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1)
    (hDDH : IndistinguishableI Assumptions none
      (DDHReal (F := F) g1 g2) (DDHRandom (F := F) g1 g2))
    (q : ENat)
    (rejectionHop : ∀ right, IndistinguishableI Assumptions q
      (G2Tracked hf g1 g2 w right) (G3 hf g1 g2 w right)) :
    (cramerShoupIndCca_of_rejectionHops Assumptions hf g1 g2 w hg1 hw hg2 hDDH
      q rejectionHop).statisticalError =
      2 * hDDH.statisticalError + 2 * (Fintype.card F : NNReal)⁻¹ +
        (rejectionHop false).statisticalError + (rejectionHop true).statisticalError := by
  simp only [cramerShoupIndCca_of_rejectionHops, IndistinguishableI.statisticalError,
    Indistinguishable.of_ObsEq, Indistinguishable.symmetric, Indistinguishable.reflexive]
  have hPair : initialBadEventBound (initialGameState hf g1 g2)
      (pairBadValuation (F := F) (V := V) (HashKey := HashKey)) q =
      (Fintype.card F : NNReal)⁻¹ := pairBadValuation_initial hf g1 g2 false q
  rw [hPair]
  ring

/-- Specialize the chain to rejection hops supplied by simple-state bridges.
This statistical specialization does not discharge hash-security reductions. -/
noncomputable def cramerShoupIndCca
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1)
    (hDDH : IndistinguishableI Assumptions none
      (DDHReal (F := F) g1 g2) (DDHRandom (F := F) g1 g2))
    (rejectionBridge : ∀ right, RejectionBridge (G2Tracked hf g1 g2 w right) (G3 hf g1 g2 w right)) (q : ENat) :
    IndistinguishableI Assumptions q (G0 hf g1 g2 false) (G0 hf g1 g2 true) :=
  cramerShoupIndCca_of_rejectionHops Assumptions hf g1 g2 w hg1 hw hg2 hDDH q
    (fun right => (rejectionBridge right).hop Assumptions q)

theorem cramerShoupIndCca_statisticalError
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1)
    (hDDH : IndistinguishableI Assumptions none
      (DDHReal (F := F) g1 g2) (DDHRandom (F := F) g1 g2))
    (rejectionBridge : ∀ right, RejectionBridge (G2Tracked hf g1 g2 w right) (G3 hf g1 g2 w right)) (q : ENat) :
    (cramerShoupIndCca Assumptions hf g1 g2 w hg1 hw hg2 hDDH rejectionBridge q).statisticalError =
      2 * hDDH.statisticalError + 2 * (Fintype.card F : NNReal)⁻¹ +
        (rejectionBridge false).error q + (rejectionBridge true).error q := by
  simp only [cramerShoupIndCca, cramerShoupIndCca_of_rejectionHops_statisticalError,
    RejectionBridge.hop_statisticalError]

/-- Retain the previous conditional route for comparison. It applies Bellman
reasoning on full states and is not the intended numerical rejection proof. -/
noncomputable def cramerShoupIndCca_of_fullStateBound
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1)
    (hDDH : IndistinguishableI Assumptions none
      (DDHReal (F := F) g1 g2) (DDHRandom (F := F) g1 g2))
    (rejectionBound : Bool → GameState F V HashKey → ENat → NNReal)
    (hRejectionBound : ∀ right, IsValidBadEventBound (IndCcaSpec F V HashKey)
      rejectionBadFlag (G2Tracked hf g1 g2 w right).queries (rejectionBound right))
    (q : ENat) :
    IndistinguishableI Assumptions q (G0 hf g1 g2 false) (G0 hf g1 g2 true) :=
  cramerShoupIndCca_of_rejectionHops Assumptions hf g1 g2 w hg1 hw hg2 hDDH q
    (fun right => IndistinguishableI.approxEq _
      (hop_G2Tracked_G3_of_bound hf g1 g2 w right
        (rejectionBound right) (hRejectionBound right) q))

/-- Legacy name for the game chain, now taking rejection bridges and a query budget. -/
noncomputable abbrev cramerShoupIndCcaSkeleton := @cramerShoupIndCca

end Games

end Hopscotch.CramerShoup
