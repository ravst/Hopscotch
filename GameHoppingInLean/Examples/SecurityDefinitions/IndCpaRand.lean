import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc
import GameHoppingInLean.Misc.SimpAttrs

/-- IND-CPA "real vs random ciphertext" oracle spec.
The query indexed by `n` takes a single `n`-bit message and returns an `n`-bit ciphertext. -/
inductive IndCpaRandDomain : Type
| ctxt (n : ℕ) (msg : BitVec n)

def IndCpaRandSpec (C : ℕ → Type) : OracleSpec IndCpaRandDomain :=
  fun ⟨n, _q⟩ =>
    C n

/-- Convenience query constructor for the `ctxt(m)` oracle query. -/
@[reducible, inline] def ctxt {C : ℕ → Type} {n : ℕ} (m : BitVec n) :
    OracleComp (IndCpaRandSpec C) (C n) :=
  (IndCpaRandSpec C).query ⟨n, m⟩

/-- IND-CPA "real ciphertext" oracle for the `ctxt(m)` interface. Returns `Enc_k(m)`. -/
noncomputable def IndCpaRandReal {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaRandSpec C) where
  stateType := K
  initialState := scheme.keyGen
  queries := fun ⟨_n, m⟩ => do
           let key <- get
           scheme.encrypt key m


/-- IND-CPA "random ciphertext" oracle for the `ctxt(m)` interface.
Ignores the message and returns a uniformly random `n`-bit ciphertext. -/
noncomputable def IndCpaRandRand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (_scheme : SymEncScheme K C) :
    RStateOracle (IndCpaRandSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, _m⟩ => do
          PMF.uniformOfFintype (C n)

/-- The oracle pair corresponding to the IND-CPA-rand security definition, for use in an
`Assumptions` set. -/
noncomputable def IndCpaRandAssumption {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaRandSpec C) × RStateOracle (IndCpaRandSpec C) :=
  (IndCpaRandReal scheme, IndCpaRandRand scheme)

noncomputable def IndCpaRandSingleAssumption {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    SingleAssumption :=
  ⟨IndCpaRandDomain, IndCpaRandSpec C, IndCpaRandAssumption scheme⟩

noncomputable def IndCpaRandAssumptionFam {K : ℕ → Type} {C : ℕ → ℕ → Type}
    (schemeFam : SymEncSchemeFamily K C)
    [∀ κ n, Fintype (C κ n)] [∀ κ n, Nonempty (C κ n)]
    : IndAssumptionsFam :=
    fun κ =>
    {
    Idx := Unit
    assumptions := fun _ => IndCpaRandSingleAssumption (schemeFam.scheme κ)
    }

/-- IND-CPA-rand security definition as an instance of `Indistinguishable`. -/
def IndCpaRandDef
    (Assumptions : IndAssumptions)
    {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) : Type 1 :=
  IndistinguishableSingle Assumptions
    (IndCpaRandReal scheme) (IndCpaRandRand scheme)

/-- IND-CPA-rand security definition for a security-parameter family. -/
def IndCpaRandIFam
    (Assumptions : IndAssumptionsFam)
    {K : ℕ → Type} {C : ℕ → ℕ → Type}
    [∀ κ n, Fintype (C κ n)] [∀ κ n, Nonempty (C κ n)]
    (schemeFam : SymEncSchemeFamily K C) : Type 1 :=
  Indistinguishable
    (I := fun _ => IndCpaRandDomain)
    (O := fun κ => IndCpaRandSpec (C κ))
    Assumptions
    (fun κ => (IndCpaRandReal (schemeFam.scheme κ) : RStateOracle (IndCpaRandSpec (C κ))))
    (fun κ => (IndCpaRandRand (schemeFam.scheme κ) : RStateOracle (IndCpaRandSpec (C κ))))
