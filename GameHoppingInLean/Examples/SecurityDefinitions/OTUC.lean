import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc
import GameHoppingInLean.Misc.SimpAttrs

/-- One-time uniform ciphertext (OTUC) oracle spec.
The query indexed by `n` takes an `n`-bit message and returns an `n`-bit ciphertext. -/
inductive OTUCDomain : Type
| ctxt (n : ℕ) (msg : BitVec n)

def OTUCSpec (C : ℕ → Type) : OracleSpec OTUCDomain :=
  fun ⟨n, _m⟩ => C n

/-- Convenience query constructor for the OTUC `ctxt(m)` query. -/
@[reducible, inline] def otucCtxt {C : ℕ → Type} {n : ℕ} (m : BitVec n) :
    OracleComp (OTUCSpec C) (C n) :=
  (OTUCSpec C).query ⟨n, m⟩

/-- OTUC real oracle: on each query, sample a fresh key from the scheme and encrypt the message. -/
@[game_hopping_unfold]
noncomputable def OTUC_Real {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨_n, m⟩ => do
          let k ← liftM scheme.keyGen
          scheme.encrypt k m

/-- OTUC random oracle: ignore the message and return a uniformly random `n`-bit ciphertext. -/
@[game_hopping_unfold]
noncomputable def OTUC_Rand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (_scheme : SymEncScheme K C) :
    RStateOracle (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, _m⟩ => do
          PMF.uniformOfFintype (C n)

/-- The oracle pair corresponding to the OTUC assumption, for use in an `Assumptions` set. -/
noncomputable def OTUCAssumption {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    RStateOracle (OTUCSpec C) × RStateOracle (OTUCSpec C) :=
  (OTUC_Real scheme, OTUC_Rand scheme)

noncomputable def OTUCAssumptionFull {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    SingleAssumption :=
  ⟨OTUCDomain, OTUCSpec C, OTUCAssumption scheme⟩

noncomputable def OTUCAssumption' {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    IndistinguishabilityAssumptions where
  Idx := Unit
  assumptions := fun _ => OTUCAssumptionFull scheme

/-- OTUC indistinguishability definition as an instance of `Indistinguishable`. -/
def OTUCDef
    (Assumptions : IndistinguishabilityAssumptions)
    {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) : Type 1 :=
  Indistinguishable Assumptions
     (OTUC_Real scheme) (OTUC_Rand scheme)
