import Hopscotch.Examples.Constructions.CramerShoup
import Hopscotch.Comp.RemainingCandidates
import Hopscotch.Examples.Misc.CyclicGenerator
import Hopscotch.Examples.SecurityDefinitions.IndCcaPub
import Hopscotch.Examples.SecurityDefinitions.CollisionResistance
import Hopscotch.ApproxEq.CorrectUntilBad
import Hopscotch.ObservationalEq.Defs
import Hopscotch.Indistinguishability.Def
import Hopscotch.Tactic.Defs
import Hopscotch.Tactic.Normalization.PMF.Simprocs
import Mathlib.Probability.Distributions.Uniform

/-!
# Cramer--Shoup IND-CCA

The main games are introduced in order, from G0 to G4, with each game
immediately following its prerequisites. Auxiliary reductions and lazy hybrids
come next, followed by the proofs and the final `cramerShoupIndCca` chain.
The lemmas justify the DDH reduction, exponent conditioning,
hash-comparison reduction, randomized lazy authentication, and message-mask coupling.

The generic candidate-set calculus is in `Hopscotch.Comp.RemainingCandidates`.
The remaining candidate set contains compatible authentication pairs. Its
Bellman value is `min 1 (q * |F| / |S|)` before the challenge and
`min 1 (q / |S|)` afterward. Failed or invalid states have value one.
The lazy rejection hop uses the framework's correct-until-bad theorem with
this Bellman value. Every hop in the final chain is discharged below.
-/

namespace Hopscotch.CramerShoup

open scoped OracleReduction

/-- Common state for the full-key games. The lazy games retain its canonical
frame and reconstruct its hidden authentication coordinates probabilistically. -/
structure GameState (F V HashKey : Type) where
  secretKey : SecretKey F HashKey
  target : Option (Ciphertext V)
  pairBad : Bool
  rejectionBad : Bool

/-- Pick the message selected by the left/right challenge bit. -/
def selectedMessage {V : Type} (right : Bool) (m0 m1 : V) : V :=
  if right then m1 else m0

section Games

variable {F V HashKey : Type}
variable [Field F] [Fintype F] [DecidableEq F]
variable [AddCommGroup V] [Module F V] [DecidableEq V]

/-! ## G0: the original IND-CCA game -/

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
      rejectionBad := false }

/-- Assemble an IND-CCA game from its challenge and decryption rules. The
single-challenge check and prohibition on decrypting the target are shared,
so individual games cannot accidentally implement them differently. -/
noncomputable def gameOracle
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool)
    (challengeRule : Bool → V → V → GameM F V HashKey (Ciphertext V))
    (decryptRule : Ciphertext V → GameM F V HashKey (Option V)) :
    OracleImpl (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) where
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
  pure (encryptWithCoins hf g1 g2 (publicKey g1 g2 st.secretKey)
    (selectedMessage right m0 m1) r)

noncomputable def G0
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g0Challenge hf g1 g2) (normalDecryptRule hf)

/-! ## G1: express the challenge using the secret exponents -/

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

/-- G1 challenge: the same ciphertext expressed using secret exponents. -/
noncomputable def g1Challenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let r ← PMF.uniformOfFintype F
  pure (encryptWithSecretPair hf st.secretKey
    (selectedMessage right m0 m1) (r • g1) (r • g2))

noncomputable def G1
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g1Challenge hf g1 g2) (normalDecryptRule hf)

/-! ## G2: independent exponents, then conditioning -/

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

noncomputable def G2Raw
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2RawChallenge hf g1 g2) (normalDecryptRule hf)

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

noncomputable def G2PairTracked
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2PairTrackedChallenge hf g1 g2) (normalDecryptRule hf)

/-- A pair of distinct exponents, used by the conditioned form of G2. -/
abbrev DistinctPair (F : Type) := { p : F × F // p.1 ≠ p.2 }

instance distinctPairNonempty (F : Type) [Nontrivial F] :
    Nonempty (DistinctPair F) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne F
  exact ⟨⟨(a, b), hab⟩⟩

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

noncomputable def G2Coupled
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2CoupledChallenge hf g1 g2) (normalDecryptRule hf)

/-- Paper G2: sample a uniformly random pair conditioned to be distinct. -/
noncomputable def g2Challenge
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (right : Bool) (m0 m1 : V) : GameM F V HashKey (Ciphertext V) := do
  let st ← get
  let pair ← PMF.uniformOfFintype (DistinctPair F)
  set { st with pairBad := false }
  pure (encryptWithSecretPair hf st.secretKey
    (selectedMessage right m0 m1) (pair.val.1 • g1) (pair.val.2 • g2))

noncomputable def G2
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (normalDecryptRule hf)

/-! ## G2Tracked and G3: record rejection and enforce consistency -/

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
/-- Event R3: ordinary verification accepts a ciphertext that the special
G3 consistency test rejects. -/
noncomputable def rejectionEvent
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V] [DecidableEq V]
    (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (ct : Ciphertext V) : Bool :=
  decide (ct.u2 ≠ w • ct.u1 ∧ valid hf sk ct)

/-- G2 decryption, instrumented with the paper's event R3. -/
noncomputable def g2DecryptRule
    (hf : HashFamily F V HashKey) (w : F) (ct : Ciphertext V) :
    GameM F V HashKey (Option V) := do
  let st ← get
  let badNow := rejectionEvent hf w st.secretKey ct
  set { st with rejectionBad := st.rejectionBad || badNow }
  pure (decrypt hf st.secretKey ct)

noncomputable def G2Tracked
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (g2DecryptRule hf w)

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

/-- G3 decryption uses the special rejection rule and records exactly the
same candidate bad event as G2. -/
noncomputable def g3DecryptRule
    (hf : HashFamily F V HashKey) (w : F) (ct : Ciphertext V) :
    GameM F V HashKey (Option V) := do
  let st ← get
  let badNow := rejectionEvent hf w st.secretKey ct
  set { st with rejectionBad := st.rejectionBad || badNow }
  pure (specialDecrypt hf w st.secretKey ct)

noncomputable def G3
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (g3DecryptRule hf w)

/-! ## G4: replace the message mask by a uniform payload -/

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

noncomputable def G4
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) :=
  gameOracle hf g1 g2 false (g4Challenge hf g1 g2) (g3DecryptRule hf w)

/-! ## Auxiliary reductions and hybrids -/


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

/-- Projections used as the bad predicates in correct-until-bad hops. -/
def pairBadFlag {F V HashKey : Type} (st : GameState F V HashKey) : Bool :=
  st.pairBad

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

/-- DDH reduction for the G1--G2Raw hop.  The DDH pair is requested lazily
when the unique challenge query arrives, so adaptively chosen challenge
messages can be inserted without knowing either sampled scalar. -/
noncomputable def CramerShoupDDHReduction
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    OracleReduction (ModuleDDHSpec V) (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) where
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

/-! ### Collision resistance before authentication guessing -/

/-- Only inconsistent ciphertexts are guarded; consistent decryption is preserved. -/
noncomputable def guardedDecryptRule (real : Bool) (hf : HashFamily F V HashKey)
    (w : F) (ct : Ciphertext V) : GameM F V HashKey (Option V) := do
  let st ← get
  if ct.u2 = w • ct.u1 then
    if real then g2DecryptRule hf w ct else g3DecryptRule hf w ct
  else if h : st.target.isSome then
    if targetHashCollision hf st.secretKey (st.target.get h) ct then pure none
    else if real then g2DecryptRule hf w ct else g3DecryptRule hf w ct
  else if real then g2DecryptRule hf w ct else g3DecryptRule hf w ct

noncomputable def G2Guarded (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (guardedDecryptRule true hf w)

noncomputable def G3Guarded (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2) (guardedDecryptRule false hf w)

/-- Attach the source oracle's sampled public key to the reduction's state.
This also makes the abstraction diagram hold on all states, not just reachable ones. -/
def attachHashKey (hk : HashKey) (st : GameState F V HashKey) : GameState F V HashKey :=
  { st with secretKey := { st.secretKey with hashKey := hk } }

def hashGuardProjection (st : GameState F V HashKey × HashKey) : GameState F V HashKey :=
  attachHashKey st.2 st.1

noncomputable def hashGuardBaseHandler (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V)) (st : GameState F V HashKey) :
    OracleReduction.SRReductionComp
      (HashComparison.PublicSpec HashKey (V × V × V) F) (GameState F V HashKey)
      (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q) := do
  let out ← OracleReduction.sample ((G2Tracked hf g1 g2 w right).queries q st)
  OracleReduction.set out.2
  pure out.1

/-- One comparison detects the target collision. Under message comparison the
guard is impossible; under hash comparison it is precisely the collision guard. -/
noncomputable def CramerShoupHashGuardReduction (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) :
    OracleReduction (HashComparison.PublicSpec HashKey (V × V × V) F)
      (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) where
  stateType := GameState F V HashKey
  initialState := do
    let hk : HashKey ← OracleReduction.initQuery (HashComparison.PublicQuery.getHashKey)
    OracleReduction.initSample (initialGameState { hf with keyGen := PMF.pure hk } g1 g2)
  queries := fun q => do
    let hk : HashKey ← OracleReduction.query (HashComparison.PublicQuery.getHashKey)
    let st ← OracleReduction.get
    let st := attachHashKey hk st
    match q with
    | .getPublicKey => hashGuardBaseHandler hf g1 g2 w right .getPublicKey st
    | .challenge m0 m1 => hashGuardBaseHandler hf g1 g2 w right (.challenge m0 m1) st
    | .decrypt ct =>
        if st.target = some ct then pure none
        else if ct.u2 = w • ct.u1 then
          hashGuardBaseHandler hf g1 g2 w right (.decrypt ct) st
        else if h : st.target.isSome then
          let target := st.target.get h
          let same : Bool ← OracleReduction.query (HashComparison.PublicQuery.compareHashes (hashMessage ct) (hashMessage target))
          if hashMessage ct ≠ hashMessage target ∧ same = true then
            OracleReduction.set st
            pure none
          else hashGuardBaseHandler hf g1 g2 w right (.decrypt ct) st
        else hashGuardBaseHandler hf g1 g2 w right (.decrypt ct) st

noncomputable def hashGuardEndpoint (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2)
    (if real then guardedDecryptRule true hf w else g2DecryptRule hf w)

noncomputable def G3Untracked (hf : HashFamily F V HashKey) (g1 g2 : V)
    (w : F) (right : Bool) :=
  gameOracle hf g1 g2 right (g2Challenge hf g1 g2)
    (fun ct => do let st ← get; pure (specialDecrypt hf w st.secretKey ct))

/-- Bellman valuation for the exponent-pair conditioning event.  Before the
single challenge it reserves exactly `1 / |F|`; after a good challenge the
event can no longer occur, while a state in which it occurred has value one.
The query budget is intentionally unused because the challenge is ask-once. -/
noncomputable def pairBadValuation
    (st : GameState F V HashKey) (_q : ENat) : NNReal :=
  if st.pairBad then 1
  else if st.target.isSome then 0
  else (Fintype.card F : NNReal)⁻¹

/-! ### Auxiliary hybrids for the message-mask coupling -/

/-- Resample the hidden mask coordinate while preserving its public coordinate. -/
def refreshMaskKey (w : F) (sk : SecretKey F HashKey) (z : F) : SecretKey F HashKey :=
  { sk with z1 := sk.collapsedZ w - w * z, z2 := z }

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

/-- Forget the hidden coordinate after its contribution to the payload has been sampled. -/
def collapseMaskState (w : F) (st : GameState F V HashKey) : GameState F V HashKey :=
  { st with secretKey := refreshMaskKey w st.secretKey 0 }

/-- Common abstraction of the lazy-mask game and G4. -/
noncomputable def G4Canonical (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) :=
  { G4 hf g1 g2 w with
    initialState := (initialGameState hf g1 g2).map (collapseMaskState w) }

/-! ### Lazy authentication hybrids -/

/-- The public authentication coordinates remain; the two hidden shares are erased. -/
def lazyAuthFrame (w : F) (st : GameState F V HashKey) : GameState F V HashKey :=
  { st with secretKey := { st.secretKey with
      x1 := st.secretKey.collapsedX w, x2 := 0,
      y1 := st.secretKey.collapsedY w, y2 := 0 } }

def lazyAuthState (w : F) (frame : GameState F V HashKey) (p : F × F) :
    GameState F V HashKey :=
  { frame with secretKey := { frame.secretKey with
      x1 := frame.secretKey.collapsedX w - w * p.1, x2 := p.1,
      y1 := frame.secretKey.collapsedY w - w * p.2, y2 := p.2 } }

abbrev LazyAuthState (F V HashKey : Type) :=
  GameState F V HashKey × RemainingCandidates.Candidates (F × F)

noncomputable def lazyAuthReconstruct (w : F) (st : LazyAuthState F V HashKey) :
    PMF (GameState F V HashKey) :=
  (PMF.uniformOfFinset st.2.val st.2.property).map (lazyAuthState w st.1)

/-- One guarded query with its challenge coins supplied explicitly. -/
noncomputable def guardedQueryStep (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : GameState F V HashKey) :
    IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q × GameState F V HashKey :=
  match q with
  | .getPublicKey => (publicKey g1 g2 st.secretKey, st)
  | .challenge m0 m1 =>
      if st.target.isSome then (none, st)
      else
        let ct := encryptWithSecretPair hf st.secretKey
          (selectedMessage right m0 m1) (coins.val.1 • g1) (coins.val.2 • g2)
        (some ct, { st with target := some ct, pairBad := false })
  | .decrypt ct =>
      let normal :=
        (if real then decrypt hf st.secretKey ct else specialDecrypt hf w st.secretKey ct,
          { st with rejectionBad := st.rejectionBad || rejectionEvent hf w st.secretKey ct })
      if st.target = some ct then (none, st)
      else if ct.u2 = w • ct.u1 then normal
      else if h : st.target.isSome then
        if targetHashCollision hf st.secretKey (st.target.get h) ct then (none, st) else normal
      else normal

noncomputable def lazyAuthObservation (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (frame : GameState F V HashKey) (p : F × F) :
    IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q × GameState F V HashKey :=
  mapSecond (lazyAuthFrame w)
    (guardedQueryStep real hf g1 g2 w right q coins (lazyAuthState w frame p))

/-- Sample the response distribution and retain its compatible-key fiber.
No hidden authentication pair is retained in the lazy state. -/
noncomputable def lazyAuthQueries (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) :
    QueryImpl (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) (RState (LazyAuthState F V HashKey)) := fun q st => by
  classical
  exact (PMF.uniformOfFintype (DistinctPair F)).bind fun coins =>
    let observe := lazyAuthObservation real hf g1 g2 w right q coins st.1
    ((PMF.uniformOfFinset st.2.val st.2.property).map observe).map fun observed =>
      (observed.1, (observed.2, RemainingCandidates.fiber st.2 observe observed))

noncomputable def lazyAuthInitial (hf : HashFamily F V HashKey) :
    PMF (LazyAuthState F V HashKey) := do
  let hk ← hf.keyGen
  let x ← PMF.uniformOfFintype F
  let y ← PMF.uniformOfFintype F
  let z1 ← PMF.uniformOfFintype F
  let z2 ← PMF.uniformOfFintype F
  pure ({ secretKey := ⟨hk, x, 0, y, 0, z1, z2⟩, target := none, pairBad := false, rejectionBad := false },
      ⟨Finset.univ, Finset.univ_nonempty⟩)

noncomputable def lazyGuardedGame (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) : OracleImpl (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) where
  stateType := LazyAuthState F V HashKey
  initialState := lazyAuthInitial hf
  queries := lazyAuthQueries real hf g1 g2 w right

noncomputable def G2Lazy (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  lazyGuardedGame true hf g1 g2 w right

noncomputable def G3Lazy (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool) :=
  lazyGuardedGame false hf g1 g2 w right

/-- Before the challenge, both authentication shares remain hidden. -/
def refreshAuthPair (w : F) (sk : SecretKey F HashKey) (p : F × F) : SecretKey F HashKey :=
  { sk with
    x1 := sk.collapsedX w - w * p.1
    x2 := p.1
    y1 := sk.collapsedY w - w * p.2
    y2 := p.2 }

def authCombination (alpha : F) (p : F × F) : F := p.1 + alpha * p.2

/-- Reachable post-challenge candidate pairs all authenticate the challenge.
Before the challenge there is no extra condition. -/
def lazyAuthInvariant (hf : HashFamily F V HashKey) (w : F)
    (st : LazyAuthState F V HashKey) : Prop :=
  ∀ target, st.1.target = some target →
    target.u2 ≠ w • target.u1 ∧
      ∀ p ∈ st.2.val, valid hf (lazyAuthState w st.1 p).secretKey target

/-- Candidate-set Bellman valuation. Invalid states conservatively have value
one; the one-share bound is only used for compatible post-challenge states. -/
noncomputable def lazyAuthValuation (hf : HashFamily F V HashKey) (w : F)
    (st : LazyAuthState F V HashKey) (q : ENat) : NNReal := by
  classical
  exact if st.1.rejectionBad ∨ ¬ lazyAuthInvariant hf w st then 1 else
    match q with
    | none => 1
    | some n => RemainingCandidates.budget
        (n * if st.1.target.isSome then 1 else Fintype.card F) st.2.val.card

attribute [local game_hopping_unfold]
  G0 G1 G2Raw G2PairTracked G2 G2Tracked gameOracle initialGameState
  g0Challenge g1Challenge g2RawChallenge g2PairTrackedChallenge g2Challenge
  normalDecryptRule g2DecryptRule forgetPairBadAbstraction forgetRejectionBadAbstraction

/-! ## Proofs of the hybrid transitions -/

/-- The public-key and secret-key descriptions of an honest challenge agree. -/
theorem encryptWithSecretPair_eq_encryptWithCoins
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (sk : SecretKey F HashKey) (message : V) (r : F) :
    encryptWithSecretPair hf sk message (r • g1) (r • g2) =
      encryptWithCoins hf g1 g2 (publicKey g1 g2 sk) message r := by
  have he :
      sk.z1 • (r • g1) + sk.z2 • (r • g2) + message =
        r • (sk.z1 • g1 + sk.z2 • g2) + message := by
    module
  simp only [encryptWithSecretPair, encryptWithCoins, publicKey]
  rw [he]
  congr 1
  module

set_option maxHeartbeats 1000000 in
theorem hashGuardReduction_correct (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) :
    correctAbstraction
      (CramerShoupHashGuardReduction hf g1 g2 w right ◇
        HashComparison.publicOracle real hf.keyGen (ciphertextHash hf))
      (hashGuardEndpoint real hf g1 g2 w right) hashGuardProjection := by
  classical
  cases real <;> solveCorrectAbstraction [CramerShoupHashGuardReduction,
    HashComparison.publicOracle, hashGuardEndpoint, hashGuardBaseHandler,
    G2Guarded, G2Tracked, gameOracle, initialGameState, keyGen, guardedDecryptRule,
    g2DecryptRule, g2Challenge, hashGuardProjection, attachHashKey, targetHashCollision,
    hashMessage, ciphertextHash, sReduction, sStateT, StateT.run, StateT.bind,
    StateT.map, StateT.set, RState.modify, OracleReduction.initQuery,
    OracleReduction.initSample, OracleReduction.get, OracleReduction.set,
    OracleReduction.sample, RState.set_apply, RState.map_set_apply, PFunctor.FreeM.lift]
  all_goals aesop

theorem G3Guarded_G3 (hf : HashFamily F V HashKey) (g1 g2 : V)
    (w : F) (right : Bool) : ObsEq (G3Guarded hf g1 g2 w right) (G3 hf g1 g2 w right) := by
  have hl : ObsEq (G3Guarded hf g1 g2 w right) (G3Untracked hf g1 g2 w right) := by
    by_abstraction forgetRejectionBadAbstraction using [G3Guarded, G3Untracked,
      guardedDecryptRule, g3DecryptRule, specialDecrypt]
  have hr : ObsEq (G3 hf g1 g2 w right) (G3Untracked hf g1 g2 w right) := by
    by_abstraction forgetRejectionBadAbstraction using [G3, G3Untracked, g3DecryptRule]
  exact obsEq_trans hl hr.symm

/-- The first rejection hop is solely a hash-comparison reduction. -/
noncomputable def hop_G2Tracked_G2Guarded {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool)
    (hHash : HashComparison.PublicCollisionResistanceI Assumptions none
      hf.keyGen (ciphertextHash hf)) (q : ENat) :
    IndistinguishableI Assumptions q (G2Tracked hf g1 g2 w right)
      (G2Guarded hf g1 g2 w right) := by
  game_hopping_basic [G2Tracked hf g1 g2 w right,
    CramerShoupHashGuardReduction hf g1 g2 w right ◇
      HashComparison.publicIdeal hf.keyGen (ciphertextHash hf),
    CramerShoupHashGuardReduction hf g1 g2 w right ◇
      HashComparison.publicConcrete hf.keyGen (ciphertextHash hf),
    G2Guarded hf g1 g2 w right]
  · by_abstraction ← hashGuardProjection using [hashGuardReduction_correct]
  · reduction ← hHash
  · by_abstraction hashGuardProjection using [hashGuardReduction_correct]

/-!
## Local hop lemmas

Each lemma isolates an exact abstraction, a correct-until-bad argument, or
a probability calculation used in the final chain.
-/

/-- G2PairTracked--G2Coupled: a correct-until-`pairBad` hop. Its bound is
`1 / |F|`, independent of the adversary's decryption-query count. -/
theorem G2PairTracked_G2Coupled_correctUntilBad
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    IsCorrectUntilBad (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) pairBadFlag
      (G2PairTracked hf g1 g2 right).initialState
      (G2Coupled hf g1 g2 right).initialState
      (G2PairTracked hf g1 g2 right).queries
      (G2Coupled hf g1 g2 right).queries := by
  classical
  correct_until_bad [G2PairTracked, G2Coupled, gameOracle, g2PairTrackedChallenge,
    g2CoupledChallenge, normalDecryptRule, pairBadFlag]
  intro i st hb out st' hb'
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

/-- The pair valuation is preserved by every query of the tracked game.  The
only probabilistic calculation is that two independent uniform field elements
are equal with probability `1 / |F|`. -/
theorem pairBadValuation_valid
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    IsValidBadEventBound (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V)) pairBadFlag
      (G2PairTracked hf g1 g2 right).queries
      (pairBadValuation (F := F) (V := V) (HashKey := HashKey)) := by
  classical
  have hc : (1 : NNReal) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  valid_bad_bound [pairBadValuation, pairBadFlag, G2PairTracked, gameOracle,
    g2PairTrackedChallenge, normalDecryptRule]

/-- G2Coupled--G2: erase `pairBad`; the visible pair is uniformly distributed
over distinct pairs. This is an exact randomized-abstraction/coupling hop. -/
theorem hop_G2Coupled_G2
    (hf : HashFamily F V HashKey) (g1 g2 : V) (right : Bool) :
    ObsEq (G2Coupled hf g1 g2 right) (G2 hf g1 g2 right) := by
  by_abstraction forgetPairBadAbstraction using [G2Coupled, g2CoupledChallenge]
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

/-! ### The message-mask coupling

Refresh the unused mask coordinate before the challenge, preserving the public
coordinate. Distinct challenge exponents make its contribution an invertible
affine map, so the payload is uniform. Both games then forget the hidden
coordinate. All three abstractions retain the bad-event flags.
-/

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
@[simp] theorem refreshMaskKey_refresh (w : F) (sk : SecretKey F HashKey) (z z' : F) :
    refreshMaskKey w (refreshMaskKey w sk z) z' = refreshMaskKey w sk z' := by
  simp [refreshMaskKey, SecretKey.collapsedZ]

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
       rejectionBad := false } : GameState F V HashKey))

lemma G3Fresh_G3 (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) (right : Bool)
    (hg2 : g2 = w • g1) : ObsEq (G3Fresh hf g1 g2 w right) (G3 hf g1 g2 w right) := by
  by_rand_abstraction (refreshBeforeChallenge w) using [G3Fresh, G3,
    g3FreshChallenge, g3DecryptRule, refreshBeforeChallenge, refreshMask,
    refreshMaskKey_publicKey, hg2]
  simpa [initialGameState, refreshBeforeChallenge, sPMF] using
    refreshMask_initial hf g1 (w • g1) w

lemma G4_G4Canonical (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg2 : g2 = w • g1) : ObsEq (G4 hf g1 g2 w) (G4Canonical hf g1 g2 w) := by
  by_abstraction (collapseMaskState w) using [G4Canonical, G4, g4Challenge,
    g3DecryptRule, collapseMaskState, refreshMaskKey_publicKey, hg2]

omit [DecidableEq F] in
private lemma uniform_affine {A : Type} (a b : F) (ha : a ≠ 0) (f : F → PMF A) :
    (PMF.uniformOfFintype F).bind (fun z => f (b + a * z)) =
    (PMF.uniformOfFintype F).bind f := by
  simpa using (PMF.bind_uniformOfFintype_equiv
    ((Equiv.mulLeft₀ a ha).trans (Equiv.addLeft b)) f).symm

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
  by_abstraction (collapseMaskState w) using [G3Fresh, G4Canonical, G4,
    g3FreshChallenge, g4Challenge, g3DecryptRule, refreshMask, collapseMaskState,
    refreshMaskKey_publicKey, hg2]
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
    ObsEq (G3 hf g1 g2 w right) (G4 hf g1 g2 w) := by
  exact obsEq_trans (G3Fresh_G3 hf g1 g2 w right hg2).symm
    (obsEq_trans (G3Fresh_G4Canonical hf g1 g2 w right hg1 hw hg2)
      (G4_G4Canonical hf g1 g2 w hg2).symm)

/-! ### Lazy authentication sampling

The lazy games retain compatible authentication pairs instead of a sampled
pair. Each response selects its surviving fiber, including the information
revealed by the challenge and the persistent bad flag. The reconstruction
diagrams below are proved for initialization and every query, on all states.
The remaining statistical hop concerns these explicit lazy oracles.
-/

theorem lazyAuthState_frame (w : F) (st : GameState F V HashKey) :
    lazyAuthState w (lazyAuthFrame w st) (st.secretKey.x2, st.secretKey.y2) = st := by
  cases st
  simp [lazyAuthState, lazyAuthFrame, SecretKey.collapsedX, SecretKey.collapsedY]

theorem guardedQueryStep_key (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : GameState F V HashKey) :
    (guardedQueryStep real hf g1 g2 w right q coins st).2.secretKey = st.secretKey := by
  cases q <;> simp only [guardedQueryStep] <;> split_ifs <;> rfl

theorem guardedQueries_step (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (st : GameState F V HashKey) :
    (if real then (G2Guarded hf g1 g2 w right).queries q st
      else (G3Guarded hf g1 g2 w right).queries q st) =
      (PMF.uniformOfFintype (DistinctPair F)).map
        (fun coins => guardedQueryStep real hf g1 g2 w right q coins st) := by
  classical
  cases real <;> cases q <;>
    simp [G2Guarded, G3Guarded, gameOracle, g2Challenge, guardedDecryptRule,
      g2DecryptRule, g3DecryptRule, guardedQueryStep, sRState, sPMF]
  all_goals (try split_ifs) <;> simp_all [sRState, sPMF]

theorem lazyAuthObservation_reconstruct (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (frame : GameState F V HashKey) (p : F × F) :
    mapSecond (fun st => lazyAuthState w st p)
      (lazyAuthObservation real hf g1 g2 w right q coins frame p) =
      guardedQueryStep real hf g1 g2 w right q coins (lazyAuthState w frame p) := by
  apply Prod.ext
  · rfl
  · have hk := guardedQueryStep_key real hf g1 g2 w right q coins (lazyAuthState w frame p)
    change lazyAuthState w (lazyAuthFrame w
      (guardedQueryStep real hf g1 g2 w right q coins (lazyAuthState w frame p)).2) p = _
    have hp : ((guardedQueryStep real hf g1 g2 w right q coins (lazyAuthState w frame p)).2.secretKey.x2,
        (guardedQueryStep real hf g1 g2 w right q coins (lazyAuthState w frame p)).2.secretKey.y2) = p := by
      rw [hk]
      exact Prod.eta p
    simpa only [hp] using lazyAuthState_frame w
      (guardedQueryStep real hf g1 g2 w right q coins (lazyAuthState w frame p)).2

theorem lazyAuthQueries_correct (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (st : LazyAuthState F V HashKey) :
    (lazyAuthQueries real hf g1 g2 w right q st).bind (bindSecond (lazyAuthReconstruct w)) =
      (lazyAuthReconstruct w st).bind (fun full =>
        if real then (G2Guarded hf g1 g2 w right).queries q full
        else (G3Guarded hf g1 g2 w right).queries q full) := by
  classical
  simp_rw [guardedQueries_step]
  simp only [lazyAuthQueries, lazyAuthReconstruct, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]
  conv_rhs => simp only [PMF.map_eq_bind_pure]; rw [PMF.bind_comm]
  congr 1
  funext coins
  let observe := lazyAuthObservation real hf g1 g2 w right q coins st.1
  let finish : (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q × GameState F V HashKey) × (F × F) →
      IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q × GameState F V HashKey :=
    fun z => (z.1.1, lazyAuthState w z.1.2 z.2)
  have h := congrArg (PMF.map finish) (RemainingCandidates.fiber_reconstruct st.2 observe)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  change _ = _ at h
  calc
    _ = (PMF.uniformOfFinset st.2.val st.2.property).map
        (fun p => finish (observe p, p)) := by
      simpa [bindSecond, lazyAuthReconstruct, observe, finish, sPMF] using h
    _ = _ := by
      apply congrArg (PMF.map · (PMF.uniformOfFinset st.2.val st.2.property))
      funext p
      exact lazyAuthObservation_reconstruct real hf g1 g2 w right q coins st.1 p

private theorem lazy_uniform_univ {A : Type} [Fintype A] [Nonempty A]
    (h : (Finset.univ : Finset A).Nonempty) :
    PMF.uniformOfFinset Finset.univ h = PMF.uniformOfFintype A := rfl

theorem lazyAuthInitial_correct (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F) :
    (lazyAuthInitial hf).bind (lazyAuthReconstruct w) = initialGameState hf g1 g2 := by
  classical
  simp [lazyAuthInitial, lazyAuthReconstruct, lazyAuthState, initialGameState, keyGen,
    SecretKey.collapsedX, SecretKey.collapsedY, lazy_uniform_univ, sPMF]
  congr 1
  funext hk
  rw [PMF.bind_comm]
  conv_lhs =>
    arg 2; ext a
    rw [PMF.bind_uniformOfFintype_equiv (Equiv.addRight (w * a))]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [PMF.bind_comm]
  congr 1
  funext x
  congr 1
  funext a
  rw [PMF.bind_comm]
  conv_lhs =>
    arg 2; ext b
    rw [PMF.bind_uniformOfFintype_equiv (Equiv.addRight (w * b))]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [PMF.bind_comm]

end Games

end Hopscotch.CramerShoup


namespace Hopscotch.CramerShoup

variable {F V HashKey : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [DecidableEq V]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
lemma authenticate_refreshAuthPair (hf : HashFamily F V HashKey) (w : F)
    (sk : SecretKey F HashKey) (p : F × F) (u1 u2 e : V) :
    authenticate hf (refreshAuthPair w sk p) u1 u2 e =
      authenticate hf (refreshAuthPair w sk
        (authCombination (hf.hash sk.hashKey u1 u2 e) p, 0)) u1 u2 e := by
  simp only [authenticate, refreshAuthPair, authCombination, SecretKey.collapsedX,
    SecretKey.collapsedY]
  congr 1
  module

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
lemma valid_refreshAuthPair_iff (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (p : F × F) :
    valid hf (refreshAuthPair w sk p) ct ↔
      hg1.coordinate ct.v =
        (sk.collapsedX w + hf.hash sk.hashKey ct.u1 ct.u2 ct.e * sk.collapsedY w) *
          hg1.coordinate ct.u1 +
        authCombination (hf.hash sk.hashKey ct.u1 ct.u2 ct.e) p *
          (hg1.coordinate ct.u2 - w * hg1.coordinate ct.u1) := by
  have rhs :
      ((refreshAuthPair w sk p).x1 +
          hf.hash sk.hashKey ct.u1 ct.u2 ct.e * (refreshAuthPair w sk p).y1) • ct.u1 +
      ((refreshAuthPair w sk p).x2 +
          hf.hash sk.hashKey ct.u1 ct.u2 ct.e * (refreshAuthPair w sk p).y2) • ct.u2 =
      ((sk.collapsedX w + hf.hash sk.hashKey ct.u1 ct.u2 ct.e * sk.collapsedY w) *
        hg1.coordinate ct.u1 + authCombination (hf.hash sk.hashKey ct.u1 ct.u2 ct.e) p *
          (hg1.coordinate ct.u2 - w * hg1.coordinate ct.u1)) • g1 := by
    simp only [refreshAuthPair, authCombination, SecretKey.collapsedX, SecretKey.collapsedY]
    conv_lhs => arg 1; arg 2; rw [← hg1.reconstruct ct.u1]
    conv_lhs => arg 2; arg 2; rw [← hg1.reconstruct ct.u2]
    module
  simp only [valid, refreshAuthPair]
  simp only [refreshAuthPair] at rhs
  rw [rhs]
  constructor
  · intro h
    simpa only [hg1.coordinate_smul] using congrArg hg1.coordinate h
  · intro h
    rw [← hg1.reconstruct ct.v, h]

open scoped Classical in
/-- Before the challenge, a successful inconsistent decryption fixes one
linear combination of the two authentication shares. -/
theorem preChallenge_accepting_injective (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (hu : ct.u2 ≠ w • ct.u1) (remaining : Finset (F × F)) :
    Set.InjOn Prod.snd
      (↑(remaining.filter (fun p => valid hf (refreshAuthPair w sk p) ct)) : Set (F × F)) := by
  classical
  have hd : hg1.coordinate ct.u2 - w * hg1.coordinate ct.u1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hu
    rw [← hg1.reconstruct ct.u2, h, mul_smul, hg1.reconstruct]
  intro p hp q hq hy
  have hp' := (valid_refreshAuthPair_iff hf g1 hg1 w sk ct p).mp (Finset.mem_filter.mp hp).2
  have hq' := (valid_refreshAuthPair_iff hf g1 hg1 w sk ct q).mp (Finset.mem_filter.mp hq).2
  have hl := add_left_cancel (hp'.symm.trans hq')
  have hc := (mul_left_inj' hd).mp hl
  apply Prod.ext
  · dsimp [authCombination] at hc
    change p.2 = q.2 at hy
    rw [hy] at hc
    exact add_right_cancel hc
  · exact hy

open scoped Classical in
/-- A pre-challenge query removes at most |F| candidate pairs, uniformly for
all queries chosen from the abstract state. -/
theorem preChallenge_accepting_card_le (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w : F) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) (hu : ct.u2 ≠ w • ct.u1) (remaining : Finset (F × F)) :
    (remaining.filter (fun p => valid hf (refreshAuthPair w sk p) ct)).card ≤ Fintype.card F := by
  classical
  rw [← Finset.card_image_of_injOn
    (preChallenge_accepting_injective hf g1 hg1 w sk ct hu remaining)]
  exact Finset.card_le_univ _

end Hopscotch.CramerShoup


namespace Hopscotch.CramerShoup

variable {F V HashKey : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [DecidableEq V]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
/-- Two distinct hash values and two inconsistent valid ciphertexts fix
both authentication shares. This is the single-guess property after the challenge. -/
theorem postChallenge_accepting_unique (hf : HashFamily F V HashKey) (g1 : V)
    (hg1 : CyclicGenerator F V g1) (w : F) (sk : SecretKey F HashKey)
    (target ct : Ciphertext V) (ht : target.u2 ≠ w • target.u1)
    (hu : ct.u2 ≠ w • ct.u1)
    (ha : hf.hash sk.hashKey ct.u1 ct.u2 ct.e ≠
      hf.hash sk.hashKey target.u1 target.u2 target.e)
    (p q : F × F)
    (hpt : valid hf (refreshAuthPair w sk p) target)
    (hqt : valid hf (refreshAuthPair w sk q) target)
    (hpc : valid hf (refreshAuthPair w sk p) ct)
    (hqc : valid hf (refreshAuthPair w sk q) ct) : p = q := by
  have delta_ne (a : Ciphertext V) (h : a.u2 ≠ w • a.u1) :
      hg1.coordinate a.u2 - w * hg1.coordinate a.u1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    apply h
    rw [← hg1.reconstruct a.u2, he, mul_smul, hg1.reconstruct]
  have same_combination (a : Ciphertext V) (h : a.u2 ≠ w • a.u1)
      (hp : valid hf (refreshAuthPair w sk p) a)
      (hq : valid hf (refreshAuthPair w sk q) a) :
      authCombination (hf.hash sk.hashKey a.u1 a.u2 a.e) p =
        authCombination (hf.hash sk.hashKey a.u1 a.u2 a.e) q := by
    have hp' := (valid_refreshAuthPair_iff hf g1 hg1 w sk a p).mp hp
    have hq' := (valid_refreshAuthPair_iff hf g1 hg1 w sk a q).mp hq
    exact (mul_left_inj' (delta_ne a h)).mp (add_left_cancel (hp'.symm.trans hq'))
  have hc := same_combination ct hu hpc hqc
  have ht' := same_combination target ht hpt hqt
  dsimp [authCombination] at hc ht'
  have hy : p.2 = q.2 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show
        (hf.hash sk.hashKey ct.u1 ct.u2 ct.e -
          hf.hash sk.hashKey target.u1 target.u2 target.e) * (p.2 - q.2) = 0 by
        linear_combination hc - ht')).resolve_left
    exact sub_ne_zero.mpr ha
  apply Prod.ext
  · rw [hy] at hc
    exact add_right_cancel hc
  · exact hy

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
theorem ciphertext_eq_of_same_input_of_valid (hf : HashFamily F V HashKey)
    (sk : SecretKey F HashKey) (ct target : Ciphertext V)
    (hi : hashMessage ct = hashMessage target)
    (hc : valid hf sk ct) (ht : valid hf sk target) : ct = target := by
  rcases ct with ⟨u1, u2, e, v⟩
  rcases target with ⟨t1, t2, te, tv⟩
  simp only [hashMessage, Prod.mk.injEq] at hi
  rcases hi with ⟨h1, h2, he⟩
  subst u1
  subst u2
  subst e
  have hv : v = tv := hc.trans ht.symm
  subst v
  rfl

omit [Fintype F] in
/-- The ordinary query driver preserves challenge authentication. -/
lemma guardedQueryStep_authInvariant (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (hg1 : CyclicGenerator F V g1) (w : F) (hw : w ≠ 0)
    (hg2 : g2 = w • g1) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : GameState F V HashKey)
    (hst : ∀ target, st.target = some target →
      target.u2 ≠ w • target.u1 ∧ valid hf st.secretKey target) :
    ∀ target, (guardedQueryStep real hf g1 g2 w right q coins st).2.target = some target →
      target.u2 ≠ w • target.u1 ∧
        valid hf (guardedQueryStep real hf g1 g2 w right q coins st).2.secretKey target := by
  cases q with
  | getPublicKey => exact hst
  | decrypt ct =>
    simp only [guardedQueryStep]
    split_ifs <;> exact hst
  | challenge m0 m1 =>
    simp only [guardedQueryStep]
    split_ifs with h
    · exact hst
    · intro target ht
      simp only [Option.some.injEq] at ht
      subst target
      constructor
      · intro he
        change coins.val.2 • g2 = w • (coins.val.1 • g1) at he
        have hc := congrArg hg1.coordinate he
        simp only [hg2, smul_smul, hg1.coordinate_smul] at hc
        have hc' : w * coins.val.2 = w * coins.val.1 := by
          simpa only [mul_comm] using hc
        exact coins.property ((mul_right_inj' hw).mp hc').symm
      · rfl

open scoped Classical in
/-- Conditioning on an observation retains only keys authenticating its
recorded challenge. The total default for an empty fiber is never used here. -/
lemma lazyAuthInvariant_observe (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (hg1 : CyclicGenerator F V g1) (w : F) (hw : w ≠ 0)
    (hg2 : g2 = w • g1) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : LazyAuthState F V HashKey)
    (hs : lazyAuthInvariant hf w st) (p : F × F) (hp : p ∈ st.2.val) :
    lazyAuthInvariant hf w
      ((lazyAuthObservation real hf g1 g2 w right q coins st.1 p).2,
        RemainingCandidates.fiber st.2 (lazyAuthObservation real hf g1 g2 w right q coins st.1)
          (lazyAuthObservation real hf g1 g2 w right q coins st.1 p)) := by
  classical
  let observe := lazyAuthObservation real hf g1 g2 w right q coins st.1
  have hfiber : (st.2.val.filter (fun a => observe a = observe p)).Nonempty :=
    ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  change ∀ target, (observe p).2.target = some target → _
  intro target ht
  have full_inv (a : F × F) (ha : a ∈ st.2.val) :=
    guardedQueryStep_authInvariant real hf g1 g2 hg1 w hw hg2 right q coins
      (lazyAuthState w st.1 a) (fun t he => ⟨(hs t he).1, (hs t he).2 a ha⟩)
  have reconstruct (a : F × F) :=
    congrArg Prod.snd (lazyAuthObservation_reconstruct real hf g1 g2 w right q coins st.1 a)
  have htp : (guardedQueryStep real hf g1 g2 w right q coins
      (lazyAuthState w st.1 p)).2.target = some target := by
    change (observe p).2.target = some target
    exact ht
  refine ⟨(full_inv p hp target htp).1, ?_⟩
  intro a ha
  change a ∈ (RemainingCandidates.fiber st.2 observe (observe p)).val at ha
  rw [RemainingCandidates.fiber, dif_pos hfiber] at ha
  rcases Finset.mem_filter.mp ha with ⟨ha, hobs⟩
  have hta : (guardedQueryStep real hf g1 g2 w right q coins
      (lazyAuthState w st.1 a)).2.target = some target := by
    change (observe a).2.target = some target
    rw [hobs]
    exact ht
  have hva := (full_inv a ha target hta).2
  rw [← reconstruct a] at hva
  change valid hf (lazyAuthState w (observe p).2 a).secretKey target
  change valid hf (lazyAuthState w (observe a).2 a).secretKey target at hva
  rwa [hobs] at hva

omit [DecidableEq F] [DecidableEq V] in
lemma lazyAuthValuation_le_one (hf : HashFamily F V HashKey) (w : F)
    (st : LazyAuthState F V HashKey) (q : ENat) : lazyAuthValuation hf w st q ≤ 1 := by
  classical
  cases q <;> unfold lazyAuthValuation
  all_goals split_ifs <;> first | exact le_rfl | exact RemainingCandidates.budget_le_one _ _

omit [DecidableEq F] [DecidableEq V] in
lemma lazyAuthValuation_of_bad (hf : HashFamily F V HashKey) (w : F)
    (st : LazyAuthState F V HashKey) (q : ENat) (hb : st.1.rejectionBad = true) :
    lazyAuthValuation hf w st q = 1 := by
  classical
  simp [lazyAuthValuation, hb]

end Hopscotch.CramerShoup


namespace Hopscotch.CramerShoup

variable {F V HashKey : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [DecidableEq V]

omit [Fintype F] [DecidableEq F] [DecidableEq V] [AddCommGroup V] [Module F V] in
@[simp] lemma lazyAuthFrame_state (w : F) (st : GameState F V HashKey) (p : F × F) :
    lazyAuthFrame w (lazyAuthState w st p) = lazyAuthFrame w st := by
  cases st
  simp [lazyAuthFrame, lazyAuthState, SecretKey.collapsedX, SecretKey.collapsedY]

omit [Fintype F] [DecidableEq F] [DecidableEq V] in
lemma lazyAuthState_publicKey (g1 g2 : V) (w : F) (st : GameState F V HashKey)
    (p : F × F) (hg2 : g2 = w • g1) :
    publicKey g1 g2 (lazyAuthState w st p).secretKey = publicKey g1 g2 st.secretKey := by
  simp only [publicKey, lazyAuthState, SecretKey.collapsedX, SecretKey.collapsedY, hg2]
  congr 1 <;> module

omit [Fintype F] [DecidableEq F] in
lemma lazyAuthState_specialDecrypt (hf : HashFamily F V HashKey) (w : F)
    (st : GameState F V HashKey) (p : F × F) (ct : Ciphertext V) :
    specialDecrypt hf w (lazyAuthState w st p).secretKey ct =
      specialDecrypt hf w st.secretKey ct := by
  simp [specialDecrypt, collapsedValid, lazyAuthState,
    SecretKey.collapsedX, SecretKey.collapsedY, SecretKey.collapsedZ]

lemma lazyAuthObservation_decrypt_target (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (ct : Ciphertext V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (p : F × F) :
    (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st p).2.target = st.target := by
  simp only [lazyAuthObservation, guardedQueryStep, mapSecond]
  split_ifs <;> rfl

lemma lazyAuthObservation_decrypt_factor_valid (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (ct : Ciphertext V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (p r : F × F)
    (hv : valid hf (lazyAuthState w st p).secretKey ct ↔
      valid hf (lazyAuthState w st r).secretKey ct) :
    lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st p =
      lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st r := by
  have hd : decrypt hf (lazyAuthState w st p).secretKey ct =
      decrypt hf (lazyAuthState w st r).secretKey ct := by
    simp only [decrypt]
    rw [propext hv]
    rfl
  have he : rejectionEvent hf w (lazyAuthState w st p).secretKey ct =
      rejectionEvent hf w (lazyAuthState w st r).secretKey ct := by
    simp only [rejectionEvent]
    rw [propext hv]
  simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
    show (lazyAuthState w st p).target = st.target from rfl,
    show (lazyAuthState w st r).target = st.target from rfl,
    show targetHashCollision hf (lazyAuthState w st p).secretKey =
      targetHashCollision hf st.secretKey from rfl,
    show targetHashCollision hf (lazyAuthState w st r).secretKey =
      targetHashCollision hf st.secretKey from rfl]
  split_ifs <;> simp only [lazyAuthFrame_state, lazyAuthState_specialDecrypt, hd, he]
  all_goals simp [lazyAuthFrame, lazyAuthState, SecretKey.collapsedX, SecretKey.collapsedY]

lemma lazyAuthObservation_decrypt_partition (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (ct : Ciphertext V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (hb : st.rejectionBad = false)
    (p r : F × F) :
    lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st p =
      lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st r ↔
    (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st p).2.rejectionBad =
      (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st r).2.rejectionBad := by
  constructor
  · intro h
    exact congrArg (fun z : Option V × GameState F V HashKey => z.2.rejectionBad) h
  · intro he
    by_cases hu : ct.u2 = w • ct.u1
    · have hnp : rejectionEvent hf w (lazyAuthState w st p).secretKey ct = false :=
        by simp [rejectionEvent, hu]
      have hnr : rejectionEvent hf w (lazyAuthState w st r).secretKey ct = false :=
        by simp [rejectionEvent, hu]
      have hdp := (decrypt_eq_specialDecrypt_of_not_bad hf w _ ct hnp).trans
        (lazyAuthState_specialDecrypt hf w st p ct)
      have hdr := (decrypt_eq_specialDecrypt_of_not_bad hf w _ ct hnr).trans
        (lazyAuthState_specialDecrypt hf w st r ct)
      simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
        show (lazyAuthState w st p).target = st.target from rfl,
        show (lazyAuthState w st r).target = st.target from rfl]
      split_ifs <;> simp only [hdp, hdr, hnp, hnr, lazyAuthState_specialDecrypt, lazyAuthFrame_state]
      all_goals simp [lazyAuthFrame, lazyAuthState, SecretKey.collapsedX, SecretKey.collapsedY]
    · simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
        show (lazyAuthState w st p).target = st.target from rfl,
        show (lazyAuthState w st r).target = st.target from rfl,
        show targetHashCollision hf (lazyAuthState w st p).secretKey =
          targetHashCollision hf st.secretKey from rfl,
        show targetHashCollision hf (lazyAuthState w st r).secretKey =
          targetHashCollision hf st.secretKey from rfl, hu, ↓reduceIte] at he ⊢
      split_ifs at he ⊢ <;> try simp [lazyAuthFrame_state]
      all_goals
        have hv : valid hf (lazyAuthState w st p).secretKey ct ↔
            valid hf (lazyAuthState w st r).secretKey ct := by
          simpa [lazyAuthFrame, lazyAuthState, rejectionEvent, hb, hu] using he
        have h := lazyAuthObservation_decrypt_factor_valid real hf g1 g2 w right ct coins st p r hv
        simp_all [lazyAuthObservation, guardedQueryStep, mapSecond,
          show (lazyAuthState w st p).target = st.target from rfl,
          show (lazyAuthState w st r).target = st.target from rfl,
          show targetHashCollision hf (lazyAuthState w st p).secretKey =
            targetHashCollision hf st.secretKey from rfl,
          show targetHashCollision hf (lazyAuthState w st r).secretKey =
            targetHashCollision hf st.secretKey from rfl, hu, ↓reduceIte]

lemma lazyAuthObservation_decrypt_hit (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (ct : Ciphertext V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (hb : st.rejectionBad = false)
    (p : F × F)
    (hh : (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st p).2.rejectionBad = true) :
    ct.u2 ≠ w • ct.u1 ∧ valid hf (lazyAuthState w st p).secretKey ct ∧ st.target ≠ some ct := by
  simp only [lazyAuthObservation, guardedQueryStep, mapSecond] at hh
  split_ifs at hh <;> simp_all [lazyAuthFrame, rejectionEvent, lazyAuthState]

lemma lazyAuthObservation_decrypt_hit_target (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (ct target : Ciphertext V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (hb : st.rejectionBad = false)
    (ht : st.target = some target) (p : F × F)
    (hh : (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st p).2.rejectionBad = true) :
    targetHashCollision hf st.secretKey target ct = false := by
  simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
    show (lazyAuthState w st p).target = st.target from rfl, ht,
    Option.isSome_some, Option.get_some, ↓reduceDIte,
    show targetHashCollision hf (lazyAuthState w st p).secretKey =
      targetHashCollision hf st.secretKey from rfl] at hh
  split_ifs at hh <;> simp_all [lazyAuthFrame, rejectionEvent, lazyAuthState]

open scoped Classical in
lemma lazyAuthObservation_decrypt_hit_card (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (hg1 : CyclicGenerator F V g1) (w : F) (right : Bool) (ct : Ciphertext V)
    (coins : DistinctPair F) (st : LazyAuthState F V HashKey)
    (hb : st.1.rejectionBad = false) (hs : lazyAuthInvariant hf w st) :
    (st.2.val.filter (fun p =>
      (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st.1 p).2.rejectionBad = true)).card ≤
        if st.1.target.isSome then 1 else Fintype.card F := by
  let hit := fun p =>
    (lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st.1 p).2.rejectionBad
  cases ht : st.1.target with
  | none =>
    simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    by_cases hu : ct.u2 = w • ct.u1
    · have he : st.2.val.filter (fun p => hit p = true) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact (lazyAuthObservation_decrypt_hit real hf g1 g2 w right ct coins st.1 hb p
          (Finset.mem_filter.mp hp).2).1 hu
      change (st.2.val.filter (fun p => hit p = true)).card ≤ _
      simp [he]
    · calc
        _ ≤ (st.2.val.filter (fun p => valid hf (refreshAuthPair w st.1.secretKey p) ct)).card := by
          apply Finset.card_le_card
          intro p hp
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
            (lazyAuthObservation_decrypt_hit real hf g1 g2 w right ct coins st.1 hb p
              (Finset.mem_filter.mp hp).2).2.1⟩
        _ ≤ _ := preChallenge_accepting_card_le hf g1 hg1 w st.1.secretKey ct hu st.2.val
  | some target =>
    simp only [ht, Option.isSome_some, ↓reduceIte]
    apply Finset.card_le_one.mpr
    intro p hp r hr
    have hhp := (Finset.mem_filter.mp hp).2
    have hhr := (Finset.mem_filter.mp hr).2
    have hpc := lazyAuthObservation_decrypt_hit real hf g1 g2 w right ct coins st.1 hb p hhp
    have hrc := lazyAuthObservation_decrypt_hit real hf g1 g2 w right ct coins st.1 hb r hhr
    have ha : hf.hash st.1.secretKey.hashKey ct.u1 ct.u2 ct.e ≠
        hf.hash st.1.secretKey.hashKey target.u1 target.u2 target.e := by
      intro he
      have hnc := lazyAuthObservation_decrypt_hit_target real hf g1 g2 w right ct target
        coins st.1 hb ht p hhp
      have hi : hashMessage ct = hashMessage target := by
        simpa [targetHashCollision, hashMessage, he] using hnc
      have hc := ciphertext_eq_of_same_input_of_valid hf
        (lazyAuthState w st.1 p).secretKey ct target hi hpc.2.1
        ((hs target ht).2 p (Finset.mem_filter.mp hp).1)
      exact hpc.2.2 (ht.trans (congrArg some hc.symm))
    exact postChallenge_accepting_unique hf g1 hg1 w st.1.secretKey target ct
      (hs target ht).1 hpc.1 ha p r
      ((hs target ht).2 p (Finset.mem_filter.mp hp).1)
      ((hs target ht).2 r (Finset.mem_filter.mp hr).1) hpc.2.1 hrc.2.1

lemma lazyAuthObservation_challenge_factor (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (m0 m1 : V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (ht : st.target = none)
    (p r : F × F)
    (he : authCombination (hf.hash st.secretKey.hashKey (coins.val.1 • g1) (coins.val.2 • g2)
        (st.secretKey.z1 • (coins.val.1 • g1) + st.secretKey.z2 • (coins.val.2 • g2) +
          selectedMessage right m0 m1)) p =
      authCombination (hf.hash st.secretKey.hashKey (coins.val.1 • g1) (coins.val.2 • g2)
        (st.secretKey.z1 • (coins.val.1 • g1) + st.secretKey.z2 • (coins.val.2 • g2) +
          selectedMessage right m0 m1)) r) :
    lazyAuthObservation real hf g1 g2 w right (.challenge m0 m1) coins st p =
      lazyAuthObservation real hf g1 g2 w right (.challenge m0 m1) coins st r := by
  let e := st.secretKey.z1 • (coins.val.1 • g1) + st.secretKey.z2 • (coins.val.2 • g2) +
    selectedMessage right m0 m1
  have hc : encryptWithSecretPair hf (lazyAuthState w st p).secretKey
      (selectedMessage right m0 m1) (coins.val.1 • g1) (coins.val.2 • g2) =
    encryptWithSecretPair hf (lazyAuthState w st r).secretKey
      (selectedMessage right m0 m1) (coins.val.1 • g1) (coins.val.2 • g2) := by
    change authenticate hf (refreshAuthPair w st.secretKey p) _ _ e =
      authenticate hf (refreshAuthPair w st.secretKey r) _ _ e
    rw [authenticate_refreshAuthPair hf w st.secretKey p _ _ e,
      authenticate_refreshAuthPair hf w st.secretKey r _ _ e, he]
  simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
    show (lazyAuthState w st p).target = st.target from rfl,
    show (lazyAuthState w st r).target = st.target from rfl,
    ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hc]
  simp [lazyAuthFrame, lazyAuthState, SecretKey.collapsedX, SecretKey.collapsedY]

lemma lazyAuthObservation_challenge_fields (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (m0 m1 : V)
    (coins : DistinctPair F) (st : GameState F V HashKey) (ht : st.target = none)
    (p : F × F) :
    (lazyAuthObservation real hf g1 g2 w right (.challenge m0 m1) coins st p).2.target.isSome = true ∧
      (lazyAuthObservation real hf g1 g2 w right (.challenge m0 m1) coins st p).2.rejectionBad = st.rejectionBad := by
  simp [lazyAuthObservation, guardedQueryStep, mapSecond, lazyAuthState, lazyAuthFrame, ht]

open scoped Classical in
lemma lazyAuthValuation_good (hf : HashFamily F V HashKey) (w : F)
    (st : LazyAuthState F V HashKey) (hb : st.1.rejectionBad = false)
    (hs : lazyAuthInvariant hf w st) (n : Nat) :
    lazyAuthValuation hf w st n = RemainingCandidates.budget
      (n * if st.1.target.isSome then 1 else Fintype.card F) st.2.val.card := by
  simp [lazyAuthValuation, hb, hs]

open scoped Classical in
lemma lazyAuthQueries_expectation (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (st : LazyAuthState F V HashKey)
    (f : IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q ×
      LazyAuthState F V HashKey → ENNReal) :
    (lazyAuthQueries real hf g1 g2 w right q st).expectation f =
      (PMF.uniformOfFintype (DistinctPair F)).expectation (fun coins =>
        (PMF.uniformOfFinset st.2.val st.2.property).expectation (fun p =>
          let observe := lazyAuthObservation real hf g1 g2 w right q coins st.1
          f ((observe p).1, (observe p).2, RemainingCandidates.fiber st.2 observe (observe p)))) := by
  simp only [lazyAuthQueries, PMF.expectation_bind, RemainingCandidates.expectation_map]

open scoped Classical in
lemma lazyAuthCoin_safe_bound (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (hg1 : CyclicGenerator F V g1) (w : F) (hw : w ≠ 0)
    (hg2 : g2 = w • g1) (right : Bool) (q : IndCcaPubQ V (Ciphertext V)) (coins : DistinctPair F)
    (st : LazyAuthState F V HashKey) (hb : st.1.rejectionBad = false)
    (hs : lazyAuthInvariant hf w st) (n : Nat)
    (hc : ∀ p r, lazyAuthObservation real hf g1 g2 w right q coins st.1 p =
      lazyAuthObservation real hf g1 g2 w right q coins st.1 r)
    (ht : ∀ p, (lazyAuthObservation real hf g1 g2 w right q coins st.1 p).2.target = st.1.target)
    (hfBad : ∀ p, (lazyAuthObservation real hf g1 g2 w right q coins st.1 p).2.rejectionBad = st.1.rejectionBad) :
    (PMF.uniformOfFinset st.2.val st.2.property).expectation (fun p =>
      let observe := lazyAuthObservation real hf g1 g2 w right q coins st.1
      (lazyAuthValuation hf w ((observe p).2, RemainingCandidates.fiber st.2 observe (observe p)) n : ENNReal)) ≤
        (lazyAuthValuation hf w st ((n + 1 : Nat) : ENat) : ENNReal) := by
  rw [lazyAuthValuation_good hf w st hb hs (n + 1)]
  calc
    _ ≤ (PMF.uniformOfFinset st.2.val st.2.property).expectation (fun _ =>
        (RemainingCandidates.budget ((n + 1) * if st.1.target.isSome then 1 else Fintype.card F)
          st.2.val.card : ENNReal)) := by
      apply RemainingCandidates.expectation_le_on_support
      intro p hp
      have hp' := (PMF.mem_support_uniformOfFinset_iff _ _).mp hp
      have hi := lazyAuthInvariant_observe real hf g1 g2 hg1 w hw hg2 right q coins st hs p hp'
      dsimp only
      rw [lazyAuthValuation_good hf w _ ((hfBad p).trans hb) hi n,
        RemainingCandidates.fiber_const st.2 _ hc p, ht p]
      apply ENNReal.coe_le_coe.mpr
      apply RemainingCandidates.budget_mono_n
      exact Nat.mul_le_mul_right _ (Nat.le_succ n)
    _ = _ := PMF.expectation_const _ _

open scoped Classical in
lemma lazyAuthCoin_bound (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (hg1 : CyclicGenerator F V g1) (w : F) (hw : w ≠ 0)
    (hg2 : g2 = w • g1) (right : Bool) (q : IndCcaPubQ V (Ciphertext V)) (coins : DistinctPair F)
    (st : LazyAuthState F V HashKey) (hb : st.1.rejectionBad = false)
    (hs : lazyAuthInvariant hf w st) (n : Nat) :
    (PMF.uniformOfFinset st.2.val st.2.property).expectation (fun p =>
      let observe := lazyAuthObservation real hf g1 g2 w right q coins st.1
      (lazyAuthValuation hf w ((observe p).2, RemainingCandidates.fiber st.2 observe (observe p)) n : ENNReal)) ≤
        (lazyAuthValuation hf w st ((n + 1 : Nat) : ENat) : ENNReal) := by
  cases q with
  | getPublicKey =>
    apply lazyAuthCoin_safe_bound real hf g1 g2 hg1 w hw hg2 right .getPublicKey coins st hb hs n
    · intro p r
      simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
        lazyAuthState_publicKey g1 g2 w st.1 p hg2,
        lazyAuthState_publicKey g1 g2 w st.1 r hg2, lazyAuthFrame_state]
    · intro p; rfl
    · intro p; rfl
  | challenge m0 m1 =>
    cases ht : st.1.target with
    | some target =>
      apply lazyAuthCoin_safe_bound real hf g1 g2 hg1 w hw hg2 right (.challenge m0 m1) coins st hb hs n
      · intro p r
        simp only [lazyAuthObservation, guardedQueryStep, mapSecond,
          show (lazyAuthState w st.1 p).target = st.1.target from rfl,
          show (lazyAuthState w st.1 r).target = st.1.target from rfl,
          ht, Option.isSome_some, ↓reduceIte, lazyAuthFrame_state]
      · intro p; simp [lazyAuthObservation, guardedQueryStep, mapSecond, lazyAuthFrame, lazyAuthState, ht]
      · intro p; simp [lazyAuthObservation, guardedQueryStep, mapSecond, lazyAuthFrame, lazyAuthState, ht]
    | none =>
      let observe := lazyAuthObservation real hf g1 g2 w right (.challenge m0 m1) coins st.1
      let alpha := hf.hash st.1.secretKey.hashKey (coins.val.1 • g1) (coins.val.2 • g2)
        (st.1.secretKey.z1 • (coins.val.1 • g1) + st.1.secretKey.z2 • (coins.val.2 • g2) +
          selectedMessage right m0 m1)
      let label := authCombination alpha
      have hfactor : ∀ p r, label p = label r → observe p = observe r :=
        fun p r he => lazyAuthObservation_challenge_factor real hf g1 g2 w right m0 m1 coins st.1 ht p r he
      rw [lazyAuthValuation_good hf w st hb hs (n + 1)]
      simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      calc
        _ ≤ (PMF.uniformOfFinset st.2.val st.2.property).expectation
            (fun p => (RemainingCandidates.budget n (RemainingCandidates.fiber st.2 label (label p)).val.card : ENNReal)) := by
          apply RemainingCandidates.expectation_le_on_support
          intro p hp
          have hp' := (PMF.mem_support_uniformOfFinset_iff _ _).mp hp
          have hi := lazyAuthInvariant_observe real hf g1 g2 hg1 w hw hg2 right (.challenge m0 m1) coins st hs p hp'
          have hfields := lazyAuthObservation_challenge_fields real hf g1 g2 w right m0 m1 coins st.1 ht p
          rw [lazyAuthValuation_good hf w _ (hfields.2.trans hb) hi n]
          simp only [hfields.1, ↓reduceIte, mul_one]
          apply ENNReal.coe_le_coe.mpr
          apply RemainingCandidates.budget_antitone n _ _ (RemainingCandidates.card_pos _)
          exact RemainingCandidates.fiber_card_le_of_factor st.2 observe label hfactor p hp'
        _ ≤ _ := by
          have h := RemainingCandidates.budget_challenge_step st.2 label n
          simpa only [RemainingCandidates.expectation_map] using h
  | decrypt ct =>
    let observe := lazyAuthObservation real hf g1 g2 w right (.decrypt ct) coins st.1
    let hit := fun p => (observe p).2.rejectionBad
    let c := if st.1.target.isSome then 1 else Fintype.card F
    have hpartition : ∀ p r, observe p = observe r ↔ hit p = hit r :=
      lazyAuthObservation_decrypt_partition real hf g1 g2 w right ct coins st.1 hb
    rw [lazyAuthValuation_good hf w st hb hs (n + 1)]
    calc
      _ ≤ (PMF.uniformOfFinset st.2.val st.2.property).expectation (fun p =>
          if hit p then 1 else
            (RemainingCandidates.budget (n * c) (st.2.val.filter (fun r => hit r = false)).card : ENNReal)) := by
        apply RemainingCandidates.expectation_le_on_support
        intro p hp
        have hp' := (PMF.mem_support_uniformOfFinset_iff _ _).mp hp
        by_cases hhit : hit p = true
        · simp only [hhit, ↓reduceIte]
          exact ENNReal.coe_le_coe.mpr (lazyAuthValuation_le_one hf w _ _)
        · have hmiss : hit p = false := Bool.eq_false_of_not_eq_true hhit
          have hi := lazyAuthInvariant_observe real hf g1 g2 hg1 w hw hg2 right (.decrypt ct) coins st hs p hp'
          dsimp only
          rw [lazyAuthValuation_good hf w _ hmiss hi n]
          rw [RemainingCandidates.fiber_eq_of_partition st.2 observe hit hpartition p,
            RemainingCandidates.fiber_val_of_mem st.2 hit p hp', hmiss]
          simp only [lazyAuthObservation_decrypt_target, hmiss, Bool.false_eq_true, ↓reduceIte]
          exact le_rfl
      _ ≤ _ := RemainingCandidates.subset_budget_expectation st.2 hit n c
        (lazyAuthObservation_decrypt_hit_card real hf g1 g2 hg1 w right ct coins st hb hs)

open scoped Classical in
/-- The explicit lazy query kernel preserves the candidate-set Bellman value. -/
lemma lazyAuthValuation_valid (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (hg1 : CyclicGenerator F V g1) (w : F) (hw : w ≠ 0)
    (hg2 : g2 = w • g1) (right : Bool) :
    IsValidBadEventBound (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V))
      (fun st : LazyAuthState F V HashKey => st.1.rejectionBad)
      (lazyAuthQueries real hf g1 g2 w right) (lazyAuthValuation hf w) := by
  valid_bad_bound [lazyAuthValuation] using [
    lazyAuthValuation_le_one hf w, lazyAuthValuation_of_bad hf w]
  rename_i st n _ hgood
  rw [lazyAuthQueries_expectation]
  bound_expectation
  rename_i coins _
  exact lazyAuthCoin_bound real hf g1 g2 hg1 w hw hg2 right _ coins st hgood.1 hgood.2 n

lemma lazyAuthObservation_bad (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : GameState F V HashKey) (p : F × F) :
    (lazyAuthObservation real hf g1 g2 w right q coins st p).2.rejectionBad =
      (lazyAuthObservation true hf g1 g2 w right q coins st p).2.rejectionBad := by
  cases q <;> simp only [lazyAuthObservation, guardedQueryStep, mapSecond]
  all_goals split_ifs <;> rfl

lemma lazyAuthObservation_bad_absorbing (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : GameState F V HashKey) (p : F × F)
    (hb : st.rejectionBad = true) :
    (lazyAuthObservation real hf g1 g2 w right q coins st p).2.rejectionBad = true := by
  cases q <;> simp only [lazyAuthObservation, guardedQueryStep, mapSecond]
  all_goals (try split_ifs) <;> simp [lazyAuthFrame, lazyAuthState, hb]

lemma lazyAuthObservation_agree (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (coins : DistinctPair F) (st : GameState F V HashKey) (p : F × F)
    (hb : (lazyAuthObservation true hf g1 g2 w right q coins st p).2.rejectionBad = false) :
    lazyAuthObservation true hf g1 g2 w right q coins st p =
      lazyAuthObservation false hf g1 g2 w right q coins st p := by
  cases q with
  | getPublicKey => rfl
  | challenge m0 m1 => rfl
  | decrypt ct =>
    simp only [lazyAuthObservation, guardedQueryStep,
      Bool.false_eq_true, ↓reduceIte, mapSecond] at hb ⊢
    split_ifs at hb ⊢
    all_goals first | rfl |
      (dsimp only [lazyAuthFrame] at hb
       rw [decrypt_eq_specialDecrypt_of_not_bad hf w _ ct (Bool.or_eq_false_iff.mp hb).2])

open scoped Classical in
lemma lazyAuthQueries_bad_absorbing (real : Bool) (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) (q : IndCcaPubQ V (Ciphertext V))
    (st : LazyAuthState F V HashKey) (hb : st.1.rejectionBad = true)
    (z : IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V) q × LazyAuthState F V HashKey)
    (hz : z ∈ (lazyAuthQueries real hf g1 g2 w right q st).support) :
    z.2.1.rejectionBad = true := by
  simp only [lazyAuthQueries, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hz
  rcases hz with ⟨coins, _, observed, ⟨p, _, rfl⟩, rfl⟩
  exact lazyAuthObservation_bad_absorbing real hf g1 g2 w right q coins st.1 p hb

/-- Both lazy kernels agree outside the absorbing rejection event. -/
lemma G2Lazy_G3Lazy_correctUntilBad (hf : HashFamily F V HashKey)
    (g1 g2 : V) (w : F) (right : Bool) :
    IsCorrectUntilBad (IndCcaPubSpec (PublicKey F V HashKey) V (Ciphertext V))
      (fun st : LazyAuthState F V HashKey => st.1.rejectionBad)
      (G2Lazy hf g1 g2 w right).initialState (G3Lazy hf g1 g2 w right).initialState
      (G2Lazy hf g1 g2 w right).queries (G3Lazy hf g1 g2 w right).queries := by
  classical
  correct_until_bad [] using [
    lazyAuthQueries_bad_absorbing true hf g1 g2 w right,
    lazyAuthQueries_bad_absorbing false hf g1 g2 w right]
  intro q st _ out st' hb'
  change lazyAuthQueries true hf g1 g2 w right q st (out, st') =
    lazyAuthQueries false hf g1 g2 w right q st (out, st')
  simp only [lazyAuthQueries, PMF.bind_apply]
  apply tsum_congr
  intro coins
  congr 1
  exact RemainingCandidates.fiber_lift_eq_of_good st.2
    (lazyAuthObservation true hf g1 g2 w right q coins st.1)
    (lazyAuthObservation false hf g1 g2 w right q coins st.1)
    GameState.rejectionBad
    (fun p => (lazyAuthObservation_bad false hf g1 g2 w right q coins st.1 p).symm)
    (lazyAuthObservation_agree hf g1 g2 w right q coins st.1) (out, st') hb'

end Hopscotch.CramerShoup

namespace Hopscotch.CramerShoup

open scoped OracleReduction

variable {F V HashKey : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [DecidableEq V]

attribute [local game_hopping_unfold]
  ModuleDDHSpec DDHReal DDHRandom CramerShoupDDHReduction
  G0 G1 G2Raw G2PairTracked G2 G2Tracked gameOracle initialGameState
  g0Challenge g1Challenge g2RawChallenge g2PairTrackedChallenge g2Challenge
  normalDecryptRule g2DecryptRule forgetPairBadAbstraction forgetRejectionBadAbstraction

/-! ## IND-CCA security -/

-- Elaborating the explicit chain requires more than the default heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- IND-CCA by DDH, hash-comparison security, and the proved lazy rejection bound. -/
noncomputable def cramerShoupIndCca
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    (hf : HashFamily F V HashKey) (g1 g2 : V) (w : F)
    (hg1 : CyclicGenerator F V g1) (hw : w ≠ 0) (hg2 : g2 = w • g1)
    (hDDH : IndistinguishableI Assumptions none
      (DDHReal (F := F) g1 g2) (DDHRandom (F := F) g1 g2))
    (hHash : HashComparison.PublicCollisionResistanceI Assumptions none
      hf.keyGen (ciphertextHash hf)) (q : ENat) :
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
    G2Guarded hf g1 g2 w false,
    G2Lazy hf g1 g2 w false,
    G3Lazy hf g1 g2 w false,
    G3Guarded hf g1 g2 w false,
    G3 hf g1 g2 w false,
    G4 hf g1 g2 w,
    G3 hf g1 g2 w true,
    G3Guarded hf g1 g2 w true,
    G3Lazy hf g1 g2 w true,
    G2Lazy hf g1 g2 w true,
    G2Guarded hf g1 g2 w true,
    G2Tracked hf g1 g2 w true,
    G2 hf g1 g2 true,
    G2Coupled hf g1 g2 true,
    G2PairTracked hf g1 g2 true,
    G2Raw hf g1 g2 true,
    (CramerShoupDDHReduction hf g1 g2 true) ◇ (DDHRandom (F := F) g1 g2),
    (CramerShoupDDHReduction hf g1 g2 true) ◇ (DDHReal (F := F) g1 g2),
    G1 hf g1 g2 true,
    G0 hf g1 g2 true]
  · by_abstraction id using [encryptWithSecretPair_eq_encryptWithCoins]
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
  · exact hop_G2Tracked_G2Guarded Assumptions hf g1 g2 w false hHash q
  · by_rand_abstraction ← (lazyAuthReconstruct w) using [
      (lazyAuthInitial_correct hf g1 g2 w),
      (lazyAuthQueries_correct true hf g1 g2 w false)]
  · by_correct_until_bad (fun st : LazyAuthState F V HashKey => st.1.rejectionBad)
      using (lazyAuthValuation hf w)
    · exact G2Lazy_G3Lazy_correctUntilBad hf g1 g2 w false
    · exact lazyAuthValuation_valid true hf g1 g2 hg1 w hw hg2 false
  · by_rand_abstraction (lazyAuthReconstruct w) using [
      (lazyAuthInitial_correct hf g1 g2 w),
      (lazyAuthQueries_correct false hf g1 g2 w false)]
  · obs_eq
    exact G3Guarded_G3 hf g1 g2 w false
  · obs_eq
    exact hop_G3_G4 hf g1 g2 w false hg1 hw hg2
  · obs_eq
    exact (hop_G3_G4 hf g1 g2 w true hg1 hw hg2).symm
  · obs_eq
    exact (G3Guarded_G3 hf g1 g2 w true).symm
  · by_rand_abstraction ← (lazyAuthReconstruct w) using [
      (lazyAuthInitial_correct hf g1 g2 w),
      (lazyAuthQueries_correct false hf g1 g2 w true)]
  · by_correct_until_bad ← (fun st : LazyAuthState F V HashKey => st.1.rejectionBad)
      using (lazyAuthValuation hf w)
    · exact G2Lazy_G3Lazy_correctUntilBad hf g1 g2 w true
    · exact lazyAuthValuation_valid true hf g1 g2 hg1 w hw hg2 true
  · by_rand_abstraction (lazyAuthReconstruct w) using [
      (lazyAuthInitial_correct hf g1 g2 w),
      (lazyAuthQueries_correct true hf g1 g2 w true)]
  · exact Indistinguishable.symmetric
      (hop_G2Tracked_G2Guarded Assumptions hf g1 g2 w true hHash q)
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
  · by_abstraction ← id using [encryptWithSecretPair_eq_encryptWithCoins]

end Hopscotch.CramerShoup
