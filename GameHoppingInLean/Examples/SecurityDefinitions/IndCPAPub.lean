import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.PubEnc

/-- Query indices for the public-key IND-CPA interface. -/
inductive IndCpaPubQ where
  | getPk
  | eavesdrop

/-- Public-key IND-CPA oracle spec with a public-key reveal query and an
unrestricted left/right eavesdropping query. -/
def IndCpaPubSpec (PubK M C : Type) : OracleSpec IndCpaPubQ
  | .getPk => (Unit, PubK)
  | .eavesdrop => (M × M, C)

/-- Convenience query constructor for revealing the public key. -/
@[reducible, inline] def indCpaPubGetPk {PubK M C : Type} :
    OracleComp (IndCpaPubSpec PubK M C) PubK :=
  (IndCpaPubSpec PubK M C).query .getPk ()

/-- Convenience query constructor for public-key IND-CPA `eavesdrop(m₀, m₁)`. -/
@[reducible, inline] def indCpaPubEavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    OracleComp (IndCpaPubSpec PubK M C) C :=
  (IndCpaPubSpec PubK M C).query .eavesdrop (m₀, m₁)

/-- Left public-key IND-CPA oracle:
* `getPk` returns the public key
* `eavesdrop(m₀, m₁)` returns `Enc_pk(m₀)` for every query. -/
noncomputable def IndCpaPubL {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaPubSpec PubK M C) where
  stateType := PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure pk
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          get
      | .eavesdrop, (m₀, _m₁) => do
          let pk <- get
          scheme.encrypt pk m₀
  }

/-- Right public-key IND-CPA oracle:
* `getPk` returns the public key
* `eavesdrop(m₀, m₁)` returns `Enc_pk(m₁)` for every query. -/
noncomputable def IndCpaPubR {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaPubSpec PubK M C) where
  stateType := PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure pk
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          get
      | .eavesdrop, (_m₀, m₁) => do
          let pk <- get
          scheme.encrypt pk m₁
  }

/-- The oracle pair corresponding to the public-key IND-CPA security definition,
for use in an `Assumptions` set. -/
noncomputable def IndCpaPubAssumption {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaPubSpec PubK M C) × RStateOracle (IndCpaPubSpec PubK M C) :=
  (IndCpaPubL scheme, IndCpaPubR scheme)

noncomputable def IndCpaPubAssumptionFull {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    SingleAssumption where
  I := IndCpaPubQ
  O := IndCpaPubSpec PubK M C
  i := IndCpaPubAssumption scheme

noncomputable def IndCpaPubAssumption' {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    IndistinguishabilityAssumptions where
  Idx := Unit
  assumptions := fun _ => IndCpaPubAssumptionFull scheme

/-- Public-key IND-CPA security definition as an instance of `Indistinguishable`. -/
def IndCpaPubDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  Indistinguishable Assumptions Reductions
    (IndCpaPubSpec PubK M C)
    (IndCpaPubL scheme)
    (IndCpaPubR scheme)

/-- The bounded step version of `IndCpaPubDef` but for a fixed number of steps --/
def IndCpaPubDefQ
   (Assumptions : IndistinguishabilityAssumptions)
   (Reductions : IndistinguishabilityReductions)
    {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  IndistinguishableQ Assumptions Reductions
    (IndCpaPubSpec PubK M C)
    (IndCpaPubL scheme)
    (IndCpaPubR scheme)
