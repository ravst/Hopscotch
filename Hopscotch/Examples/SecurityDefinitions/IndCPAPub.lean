import Hopscotch.Indistinguishability.Def
import Hopscotch.Examples.Schemes.PubEnc

/-- Query indices for the public-key IND-CPA interface. -/
inductive IndCpaPubQ (M : Type) where
  | getPk
  | eavesdrop (msg_pair : M × M)

/-- Public-key IND-CPA oracle spec with a public-key reveal query and an
unrestricted left/right eavesdropping query. -/
def IndCpaPubSpec (PubK M C : Type) : OracleSpec (IndCpaPubQ M)
  | .getPk => PubK
  | .eavesdrop _ => C

/-- Convenience query constructor for revealing the public key. -/
@[reducible, inline] def indCpaPubGetPk {PubK M C : Type} :
    OracleComp (IndCpaPubSpec PubK M C) PubK :=
  (IndCpaPubSpec PubK M C).query .getPk

/-- Convenience query constructor for public-key IND-CPA `eavesdrop(m₀, m₁)`. -/
@[reducible, inline] def indCpaPubEavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    OracleComp (IndCpaPubSpec PubK M C) C :=
  (IndCpaPubSpec PubK M C).query (.eavesdrop (m₀, m₁))

/-- Left public-key IND-CPA oracle:
* `getPk` returns the public key
* `eavesdrop(m₀, m₁)` returns `Enc_pk(m₀)` for every query. -/
noncomputable def IndCpaPubL {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    OracleImpl (IndCpaPubSpec PubK M C) where
  stateType := PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure pk
  queries := fun
      | .getPk => do
          get
      | .eavesdrop (m₀, _m₁) => do
          let pk <- get
          scheme.encrypt pk m₀


/-- Right public-key IND-CPA oracle:
* `getPk` returns the public key
* `eavesdrop(m₀, m₁)` returns `Enc_pk(m₁)` for every query. -/
noncomputable def IndCpaPubR {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    OracleImpl (IndCpaPubSpec PubK M C) where
  stateType := PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure pk
  queries := fun
      | .getPk => do
          get
      | .eavesdrop (_m₀, m₁) => do
          let pk <- get
          scheme.encrypt pk m₁


/-- The oracle pair corresponding to the public-key IND-CPA security definition,
for use in an `Assumptions` set. -/
noncomputable def IndCpaPubAssumption {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    OracleImpl (IndCpaPubSpec PubK M C) × OracleImpl (IndCpaPubSpec PubK M C) :=
  (IndCpaPubL scheme, IndCpaPubR scheme)

noncomputable def IndCpaPubAssumptionFull {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    SingleAssumption where
  i := IndCpaPubAssumption scheme

noncomputable def IndCpaPubAssumption' {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    IndAssumptions Unit where
  assumptions := fun _ => IndCpaPubAssumptionFull scheme

noncomputable def IndCpaPubAssumptionFam
    {PubK SecK M C : ℕ → Type}
    (schemeFam : PubEncSchemeFamily PubK SecK M C) :
    IndAssumptionsFam where
  Idx := Unit
  val κ := IndCpaPubAssumption' (schemeFam.scheme κ)

/-- Public-key IND-CPA security definition as an instance of `Indistinguishable`. -/
def IndCpaPubDef
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  IndistinguishableSingle Assumptions
    (IndCpaPubL scheme)
    (IndCpaPubR scheme)

def IndCpaPubIFam
    (AssumptionsFam : IndAssumptionsFam)
    {PubK SecK M C : ℕ → Type}
    (schemeFam : PubEncSchemeFamily PubK SecK M C) : Type 1 :=
  Indistinguishable (AssumptionsFam)
      (fun κ => IndCpaPubL (schemeFam.scheme κ))
      (fun κ => IndCpaPubR (schemeFam.scheme κ))

def IndCpaPubBoundedIFam
    (AssumptionsFam : IndAssumptionsFam)
    {PubK SecK M C : ℕ → Type}
    (schemeFam : PubEncSchemeFamily PubK SecK M C) : Type 1 :=
  IndistinguishableWithQueryBound AssumptionsFam
      (fun κ => IndCpaPubL (schemeFam.scheme κ))
      (fun κ => IndCpaPubR (schemeFam.scheme κ))
