import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec

universe u

def simpleReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) :=
  QueryImpl O₂ (OracleComp O₁)

noncomputable def applySimpleReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : simpleReduction O₁ O₂) (oracle : RStateOracle O₁) : RStateOracle O₂ where
  stateType := oracle.stateType
  initialState := oracle.initialState
  queries := {
    impl q := OracleComp.simulateQ oracle.queries (reduction.impl q)
  }

/-- Oracle indices for a source oracle set, plus reduction randomness and reduction-state effects. -/
inductive withCoinFlipAndStateI (I : Type u) : Type u
  | oracle (i : I)
  | coinFlip
  | getState
  | setState

/-- Include an existing oracle index into the extended index type with randomness and state. -/
def withCoinFlipAndState {I : Type u} : I → withCoinFlipAndStateI I :=
  withCoinFlipAndStateI.oracle

/-- Extend an oracle spec with reduction coin-flips and reduction-local `get`/`set` operations. -/
def withCoinFlipAndStateSpec {I : Type u} (s : Type) (O : OracleSpec I) :
    OracleSpec (withCoinFlipAndStateI I)
  | .oracle i => O i
  | .coinFlip => (Unit, Bool)
  | .getState => (Unit, s)
  | .setState => (s, Unit)

@[simp] lemma withCoinFlipAndStateSpec_apply_withCoinFlipAndState
    {I : Type u} {s : Type} (O : OracleSpec I) (i : I) :
    withCoinFlipAndStateSpec s O (withCoinFlipAndState i) = O i := rfl

@[simp] lemma withCoinFlipAndStateSpec_apply_coinFlip
    {I : Type u} {s : Type} (O : OracleSpec I) :
    withCoinFlipAndStateSpec s O withCoinFlipAndStateI.coinFlip = (Unit, Bool) := rfl

@[simp] lemma withCoinFlipAndStateSpec_apply_getState
    {I : Type u} {s : Type} (O : OracleSpec I) :
    withCoinFlipAndStateSpec s O withCoinFlipAndStateI.getState = (Unit, s) := rfl

@[simp] lemma withCoinFlipAndStateSpec_apply_setState
    {I : Type u} {s : Type} (O : OracleSpec I) :
    withCoinFlipAndStateSpec s O withCoinFlipAndStateI.setState = (s, Unit) := rfl

/-- Computations available to a stateful randomized reduction over source oracle spec `O`. -/
abbrev SRReductionComp {I : Type u} (O : OracleSpec I) (s : Type) :=
  OracleComp (withCoinFlipAndStateSpec s O)

namespace SRReduction

/-- Query the underlying source oracle from inside a stateful randomized reduction. -/
@[reducible, inline] def query {I : Type u} {O : OracleSpec I} {s : Type}
    (i : I) (t : O.domain i) : SRReductionComp O s (O.range i) :=
  (withCoinFlipAndStateSpec s O).query (withCoinFlipAndStateI.oracle i) t

/-- Flip a fair coin from inside a stateful randomized reduction. -/
@[reducible, inline] def coinFlip {I : Type u} {O : OracleSpec I} {s : Type} :
    SRReductionComp O s Bool :=
  (withCoinFlipAndStateSpec s O).query withCoinFlipAndStateI.coinFlip ()

/-- Read the reduction's local internal state. -/
@[reducible, inline] def get {I : Type u} {O : OracleSpec I} {s : Type} :
    SRReductionComp O s s :=
  (withCoinFlipAndStateSpec s O).query withCoinFlipAndStateI.getState ()

/-- Write the reduction's local internal state. -/
@[reducible, inline] def set {I : Type u} {O : OracleSpec I} {s : Type} (st : s) :
    SRReductionComp O s Unit :=
  (withCoinFlipAndStateSpec s O).query withCoinFlipAndStateI.setState st

/-- Modify the reduction's local internal state. -/
def modify {I : Type u} {O : OracleSpec I} {s : Type} (f : s → s) :
    SRReductionComp O s Unit := do
  let st ← get (O := O) (s := s)
  set (O := O) (s := s) (f st)

end SRReduction

/-- A reduction that can query the source oracles, flip coins, and use local `get`/`set` state. -/
structure SRReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) where
  stateType : Type
  initialState : PMF stateType
  queries : QueryImpl O₂ (SRReductionComp O₁ stateType)

namespace SRReduction

/-- Build an `SRReduction` while inferring the reduction state type from `initialState`. -/
def mk' {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {s : Type}
    (initialState : PMF s) (queries : QueryImpl O₂ (SRReductionComp O₁ s)) : SRReduction O₁ O₂ where
  stateType := s
  initialState := initialState
  queries := queries

end SRReduction

/-- Syntax sugar for `SRReduction.query i t`. -/
syntax "srQuery(" term ", " term ")" : term
/-- Syntax sugar for `SRReduction.coinFlip`. -/
syntax "srCoin!" : term
/-- Syntax sugar for `SRReduction.get`. -/
syntax "srGet!" : term
/-- Syntax sugar for `srSet(x)` = `SRReduction.set x`. -/
syntax "srSet(" term ")" : term
/-- Syntax sugar for `srModify(f)` = `SRReduction.modify f`. -/
syntax "srModify(" term ")" : term

macro_rules
  | `(srQuery($i, $t)) => `(SRReduction.query $i $t)
  | `(srCoin!) => `(SRReduction.coinFlip)
  | `(srGet!) => `(SRReduction.get)
  | `(srSet($st)) => `(SRReduction.set $st)
  | `(srModify($f)) => `(SRReduction.modify $f)

/-- Apply a stateful randomized reduction to an underlying stateful oracle implementation. -/
noncomputable def applySRReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : SRReduction O₁ O₂) (oracle : RStateOracle O₁) : RStateOracle O₂ where
  stateType := reduction.stateType × oracle.stateType
  initialState := do
    let sᵣ ← reduction.initialState
    let sₒ ← oracle.initialState
    pure (sᵣ, sₒ)
  queries := {
    impl q :=
      let aux : QueryImpl (withCoinFlipAndStateSpec reduction.stateType O₁)
          (RState (reduction.stateType × oracle.stateType)) := {
        impl := fun
          | OracleSpec.query (withCoinFlipAndStateI.oracle i) t => fun st => do
              let (u, sₒ') ← StateT.run (oracle.queries.impl (OracleSpec.query i t)) st.2
              pure (u, (st.1, sₒ'))
          | OracleSpec.query withCoinFlipAndStateI.coinFlip _ => RState.coinFlip
          | OracleSpec.query withCoinFlipAndStateI.getState _ => fun st => pure (st.1, st)
          | OracleSpec.query withCoinFlipAndStateI.setState sᵣ' => fun st => pure ((), (sᵣ', st.2))
      }
      OracleComp.simulateQ aux (reduction.queries.impl q)
  }
