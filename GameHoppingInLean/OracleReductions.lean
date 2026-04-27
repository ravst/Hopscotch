import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec

universe u

def simpleReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) :=
  QueryImpl3 O₂ (OracleComp O₁)

noncomputable def applySimpleReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : simpleReduction O₁ O₂) (oracle : RStateOracle O₁) : RStateOracle O₂ where
  stateType := oracle.stateType
  initialState := oracle.initialState
  queries := {
    impl i q :=
      OracleComp.simulateQ (query_impl_convert oracle.queries)
        (reduction.impl i q)
  }

/-- Oracle indices for a source oracle set plus a generic "sample from a PMF" operation. -/
inductive withPMFI (I : Type u) : Type (max u 1)
  | oracle (i : I)
  | sample (α : Type)

/-- Include an existing oracle index into the extended index type with PMF sampling. -/
def withPMF {I : Type u} : I → withPMFI I :=
  withPMFI.oracle

/-- Extend an oracle spec with a generic PMF sampling query. -/
def withPMFSpec {I : Type u} (O : OracleSpec I) : OracleSpec (withPMFI I)
  | .oracle i => O i
  | .sample α => (PMF α, α)

@[simp] lemma withPMFSpec_apply_withPMF {I : Type u} (O : OracleSpec I) (i : I) :
    withPMFSpec O (withPMF i) = O i := rfl

@[simp] lemma withPMFSpec_apply_sample {I : Type u} (O : OracleSpec I) (α : Type) :
    withPMFSpec O (withPMFI.sample α) = (PMF α, α) := rfl

/-- Computations available to a randomized (stateless) reduction over source oracle spec `O`. -/
abbrev RReductionComp {I : Type u} (O : OracleSpec I) :=
  OracleComp (withPMFSpec O)

namespace RReduction

/-- Query the underlying source oracle from inside a randomized reduction. -/
@[reducible, inline] def query {I : Type u} {O : OracleSpec I}
    (i : I) (t : O.domain i) : RReductionComp O (O.range i) :=
  (withPMFSpec O).query (withPMFI.oracle i) t

/-- Sample from an arbitrary `PMF` from inside a randomized reduction. -/
@[reducible, inline] def sample {I : Type u} {O : OracleSpec I} {α : Type}
    (p : PMF α) : RReductionComp O α :=
  (withPMFSpec O).query (withPMFI.sample α) p

end RReduction

/-- A reduction that can query the source oracles and draw samples from arbitrary `PMF`s,
but does not maintain its own internal state. -/
def RReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) :=
  QueryImpl3 O₂ (RReductionComp O₁)

noncomputable def addPMFtoImpl {I : Type} {O : OracleSpec I} {stateType : Type} (impl : QueryImpl3 O (RState stateType)):
  QueryImpl3 (withPMFSpec O) (RState stateType) :=
  {
  impl := fun
    | withPMFI.oracle i, t => impl.impl i t
    | withPMFI.sample _α, p =>
        (liftM (m := PMF) (n := RState stateType) p)
  }

/-- Apply a randomized (stateless) reduction to an underlying stateful oracle implementation. -/
noncomputable def applyRReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : RReduction O₁ O₂) (oracle : RStateOracle O₁) : RStateOracle O₂ where
  stateType := oracle.stateType
  initialState := oracle.initialState
  queries := {
    impl i q :=
      OracleComp.simulateQ (query_impl_convert (addPMFtoImpl oracle.queries)) (reduction.impl i q)
  }

/-- Oracle indices for a source oracle set, plus PMF sampling and reduction-state effects. -/
inductive withCoinFlipAndStateI (I : Type u) : Type (max u 1)
  | oracle (i : I)
  | sample (α : Type)
  | getState
  | setState

/-- Include an existing oracle index into the extended index type with randomness and state. -/
def withCoinFlipAndState {I : Type u} : I → withCoinFlipAndStateI I :=
  withCoinFlipAndStateI.oracle

/-- Extend an oracle spec with PMF sampling and reduction-local `get`/`set` operations. -/
def withCoinFlipAndStateSpec {I : Type u} (s : Type) (O : OracleSpec I) :
    OracleSpec (withCoinFlipAndStateI I)
  | .oracle i => O i
  | .sample α => (PMF α, α)
  | .getState => (Unit, s)
  | .setState => (s, Unit)

@[simp] lemma withCoinFlipAndStateSpec_apply_withCoinFlipAndState
    {I : Type u} {s : Type} (O : OracleSpec I) (i : I) :
    withCoinFlipAndStateSpec s O (withCoinFlipAndState i) = O i := rfl

@[simp] lemma withCoinFlipAndStateSpec_apply_sample
    {I : Type u} {s : Type} (O : OracleSpec I) (α : Type) :
    withCoinFlipAndStateSpec s O (withCoinFlipAndStateI.sample α) = (PMF α, α) := rfl

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

/-- Sample from an arbitrary `PMF` from inside a stateful randomized reduction. -/
@[reducible, inline] def sample {I : Type u} {O : OracleSpec I} {s : Type} {α : Type}
    (p : PMF α) : SRReductionComp O s α :=
  (withCoinFlipAndStateSpec s O).query (withCoinFlipAndStateI.sample α) p

/-- Flip a fair coin from inside a stateful randomized reduction. -/
@[reducible, inline] noncomputable def coinFlip {I : Type u} {O : OracleSpec I} {s : Type} :
    SRReductionComp O s Bool :=
  sample (O := O) (s := s) (PMF.uniformOfFintype Bool)

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

def addToStateL {I : Type u} {O : OracleSpec I} {s1 t : Type} (x : SRReductionComp O s1 t) (s2 : Type)
  : SRReductionComp O (s1 ⊕ s2) t :=
  sorry
def addToStateR {I : Type u} {O : OracleSpec I} {s1 t : Type} (x : SRReductionComp O s1 t) (s2 : Type)
  : SRReductionComp O (s2 ⊕ s1) t :=
  sorry


end SRReduction

/-- A reduction that can query the source oracles, flip coins, and use local `get`/`set` state. -/
structure SRReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) where
  stateType : Type
  initialState : PMF stateType
  queries : QueryImpl3 O₂ (SRReductionComp O₁ stateType)

namespace SRReduction

/-- Build an `SRReduction` while inferring the reduction state type from `initialState`. -/
def mk' {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {s : Type}
    (initialState : PMF s) (queries : QueryImpl3 O₂ (SRReductionComp O₁ s)) : SRReduction O₁ O₂ where
  stateType := s
  initialState := initialState
  queries := queries

end SRReduction

/-- Syntax sugar for `SRReduction.query i t`. -/
syntax "srQuery(" term ", " term ")" : term
/-- Syntax sugar for `SRReduction.coinFlip`. -/
syntax "srCoin!" : term
/-- Syntax sugar for `SRReduction.sample p`. -/
syntax "srSample(" term ")" : term
/-- Syntax sugar for `SRReduction.get`. -/
syntax "srGet!" : term
/-- Syntax sugar for `srSet(x)` = `SRReduction.set x`. -/
syntax "srSet(" term ")" : term
/-- Syntax sugar for `srModify(f)` = `SRReduction.modify f`. -/
syntax "srModify(" term ")" : term

macro_rules
  | `(srQuery($i, $t)) => `(SRReduction.query $i $t)
  | `(srCoin!) => `(SRReduction.coinFlip)
  | `(srSample($p)) => `(SRReduction.sample $p)
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
    impl (i : I₂) (t : O₂.domain i) :=
      let aux : QueryImpl3 (withCoinFlipAndStateSpec reduction.stateType O₁)
          (RState (reduction.stateType × oracle.stateType)) := {
        impl := fun
          | (withCoinFlipAndStateI.oracle i2), t2 => do
              let st <- get
              let (u, sₒ') ← StateT.run (oracle.queries.impl i2 t2) st.2
              RState.modify (fun x ↦ ⟨x.1, sₒ'⟩)
              pure u
          | (withCoinFlipAndStateI.sample _α), p =>
              (liftM (m := PMF) (n := RState (reduction.stateType × oracle.stateType)) p)
          | withCoinFlipAndStateI.getState, _ => (fun x => x.1) <$> get
          | withCoinFlipAndStateI.setState, sᵣ' => RState.modify (fun x => ⟨sᵣ', x.2⟩)
      }
      OracleComp.simulateQ (query_impl_convert aux) (reduction.queries.impl i t)
  }

/-- A reduction that may query the source oracle while computing its initial state, and whose
subsequent query handling is a stateful randomized reduction. -/
structure ComplexInitReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) where
  stateType : Type
  initialState : RReductionComp O₁ stateType
  queries : QueryImpl3 O₂ (SRReductionComp O₁ stateType)

namespace ComplexInitReduction

/-- Build a `ComplexInitReduction` while inferring the reduction state type. -/
def mk' {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {s : Type}
    (initialState : RReductionComp O₁ s) (queries : QueryImpl3 O₂ (SRReductionComp O₁ s)) :
    ComplexInitReduction O₁ O₂ where
  stateType := s
  initialState := initialState
  queries := queries

def identity {I : Type} (O : OracleSpec I) : ComplexInitReduction O O :=
  {
    stateType := Unit
    initialState := pure ()
    queries := {
      impl := fun a x =>
        let x : OracleSpec.OracleQuery (withCoinFlipAndStateSpec Unit O) _ :=  OracleSpec.query (withCoinFlipAndStateI.oracle a) x
        have H : (withCoinFlipAndStateSpec Unit O).range (withCoinFlipAndStateI.oracle a) = (O a).2 := rfl
        let y : OracleSpec.OracleQuery (withCoinFlipAndStateSpec Unit O) (O.range a) := H ▸ x
        y
    }
  }

end ComplexInitReduction

@[simp]
noncomputable def liftToWithCoinFlipAndStateSpec {I : Type} {O : OracleSpec I} {stateType : Type}
  (impl : QueryImpl3 O (RState stateType)) (addState : Type)
  : QueryImpl3 (withCoinFlipAndStateSpec addState O) (RState (addState × stateType))
  := {
    impl := fun
      | (withCoinFlipAndStateI.oracle i2), t2 => do
          let st <- get
          let (u, sₒ') ← StateT.run (impl.impl i2 t2) st.2
          RState.modify (fun x ↦ ⟨x.1, sₒ'⟩)
          pure u
      | (withCoinFlipAndStateI.sample _α), p =>
          (liftM (m := PMF) (n := RState (addState × stateType)) p)
      | withCoinFlipAndStateI.getState, _ => (fun x => x.1) <$> get
      | withCoinFlipAndStateI.setState, sᵣ' => RState.modify (fun x => ⟨sᵣ', x.2⟩)
  }

/-- Apply a reduction whose initialization may query the underlying oracle. -/
noncomputable def applyComplexInitReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : ComplexInitReduction O₁ O₂) (oracle : RStateOracle O₁) : RStateOracle O₂ where
  stateType := reduction.stateType × oracle.stateType
  initialState := do
    let sₒ ← oracle.initialState
    let aux : QueryImpl3 (withPMFSpec O₁) (RState oracle.stateType) := {
      impl := fun
        | withPMFI.oracle i, t => oracle.queries.impl i t
        | withPMFI.sample _α, p =>
            (liftM (m := PMF) (n := RState oracle.stateType) p)
    }
    let (sᵣ, sₒ') ← StateT.run (OracleComp.simulateQ (query_impl_convert aux) reduction.initialState) sₒ
    pure (sᵣ, sₒ')
  queries := {
    impl (i : I₂) (t : O₂.domain i) :=
      let liftedOracle := liftToWithCoinFlipAndStateSpec oracle.queries reduction.stateType
      OracleComp.simulateQ (query_impl_convert liftedOracle) (reduction.queries.impl i t)
  }

def mymonad2 {I : Type} (O : OracleSpec I) (state : Type) (Output : Type) : Type _ := (OracleComp O (RState state Output))

def mymonad0 {I : Type} (O : OracleSpec I) (state : Type) (Output : Type) : Type _ := (MyBetterRState state) (OracleComp O Output)
def mymonadE {I : Type} (O : OracleSpec I) (state : Type 1) (Output : Type) : Type _ := (RState state) (OracleComp O Output)

def mymonad1 {I : Type _} (O : OracleSpec I) (state : Type) : Type _ -> Type _ := StateT state (OracleComp O)
instance inst {I : Type _} (O : OracleSpec I) (state : Type) [Monad (OracleComp O)] : Monad (mymonad1 O state) := StateT.instMonad

def defaultImpl {I : Type} {O : OracleSpec I} {state : Type}
  : QueryImpl3 (withCoinFlipAndStateSpec state O) (@mymonad1 (withPMFI I) (withPMFSpec O) state) where
  impl
  | withCoinFlipAndStateI.oracle i, a =>
    StateT.lift (FreeMonad.roll (OracleSpec.query (withPMFI.oracle i) a) (fun x => return x))
  | .sample i, a =>
    StateT.lift (FreeMonad.roll (OracleSpec.query (withPMFI.sample i) a) (fun x => return x))
  | .getState, () =>
    do
      let x <- StateT.get
      return x
  | .setState, a =>
    do
      let _ <- StateT.set a
      return ()

def lower {I : Type _} {O : OracleSpec I} {state : Type} {Output : Type}
  (comp : OracleComp (withCoinFlipAndStateSpec state O) Output) (init : state) : OracleComp (withPMFSpec O) Output :=
    let x : mymonad1 (withPMFSpec O) state Output := OracleComp.simulateQ (query_impl_convert (@defaultImpl I O state)) comp
    let y : OracleComp (withPMFSpec O) (Output × state) := x init
    y <&> (fun x => x.1)

def addPMFtoImpl2 {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2} {stateType : Type} (impl : QueryImpl3 O1 (SRReductionComp O2 stateType)):
  QueryImpl3 (withPMFSpec O1) (SRReductionComp O2 stateType) :=
  {
  impl := fun
    | withPMFI.oracle i, t => impl.impl i t
    | withPMFI.sample α, p =>
        do
          let query : (withCoinFlipAndStateSpec stateType O2).OracleQuery α :=
            OracleSpec.query (withCoinFlipAndStateI.sample α) p
          let x <- query
          return x
          -- FreeMonad.roll query (fun x =>
          -- return x)
  }


/-- Apply a reduction whose initialization may query the underlying oracle. -/
def applyComplexInitReduction2 {Output I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : ComplexInitReduction O₁ O₂) (dist : OracleComp (withPMFSpec O₂) Output)
    : OracleComp (withPMFSpec O₁) Output :=
    let x : OracleComp (withCoinFlipAndStateSpec reduction.stateType O₁) Output :=
      OracleComp.simulateQ (query_impl_convert (addPMFtoImpl2 reduction.queries)) dist
    let y : reduction.stateType → OracleComp (withPMFSpec O₁) Output := lower x
    do
      let sample : reduction.stateType <- reduction.initialState
      y sample

lemma applyComplexInitReduction2_identity  {Output I : Type} {O : OracleSpec I}
  (dist : OracleComp (withPMFSpec O) Output)
  : applyComplexInitReduction2 (ComplexInitReduction.identity O) dist = dist := by sorry


/-- Apply a reduction whose initialization may query the underlying oracle. -/
def ComplexInitReduction2_compose {I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : ComplexInitReduction O₁ O₂) (r2 : ComplexInitReduction O₂ O₃) : ComplexInitReduction O₁ O₃ := by sorry

/-- Apply a reduction whose initialization may query the underlying oracle. -/
lemma ComplexInitReduction2_compose_apply {Output I₁ I₂ I₃ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {O₃ : OracleSpec I₃}
    (r1 : ComplexInitReduction O₁ O₂) (r2 : ComplexInitReduction O₂ O₃)
    (dist : OracleComp (withPMFSpec O₃) Output) :
    applyComplexInitReduction2 (ComplexInitReduction2_compose r1 r2) dist =
    applyComplexInitReduction2 r1 (applyComplexInitReduction2 r2 dist)
       := by sorry
