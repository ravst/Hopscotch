import GameHoppingInLean.Comp.StatefulRandomOracle
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec
import ToMathlib.PFunctor.Free

universe u

/- # Oracle Reductions

In this file, we define an oracle reduction, i.e. an implementation of an oracle
based on another underlying oracle. When implementing a query, the reduction is
allowed to use randomness, access its own internal state, and query the underlying oracle.

-/

/- # Definitions from the future
We use lean version 2.4.28, as this version is supported by Aristotle.
The following definitions are from newer version of VCVIo (not used due to 4.28 restriction)
-/

protected def OracleSpec.query {ι : Type u} {spec : OracleSpec.{u, v} ι}
  (t : spec.Domain) : OracleQuery spec (spec.Range t) :=
  OracleQuery.mk t id

protected lemma OracleSpec.query_def {ι : Type u} {spec : OracleSpec.{u, v} ι}
  (t : spec.Domain) :
    OracleSpec.query t = ⟨t, id⟩ := rfl

@[match_pattern, reducible]
def OracleComp.queryBind {α} {ι : Type u} {spec : OracleSpec.{u, v} ι}
  (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    OracleComp spec α :=
  PFunctor.FreeM.roll t k


/- ## Definition of Reduction Computation
Consider a reduction from spec A to B. When implementing queries of A, we need computation that can
a) access B
b) query randomness
c) keep state.
  We do this by extending spec A by operations (b) and (c). Spec of such extension is called `withPMFAndStateSpec`
  Then the key type `OracleReduction` is defined as a function from queries to A into handlers. -/


/- The list of allowed operations for a reduction -/
inductive withPMFAndStateI (I : Type u) (S : Type) : Type (max u 1)
  | oracle (i : I)
  | sample {α : Type} (d : PMF α)
  | getState
  | setState (st : S)

/- Return type for each of the operations -/
def withPMFAndStateSpec {I : Type u} (S : Type) (O : OracleSpec I) :
    OracleSpec (withPMFAndStateI I S)
  | .oracle i => O i
  | @withPMFAndStateI.sample _ _ α _ => α
  | .getState => S
  | .setState _ => Unit

/- When initializing its local state, a reduction is allowed to query the underlying oracle and sample randomness,
but it does not have access to its local state yet. -/
/- The type `withPMFI` represent the limited set of operations available during initialization -/
inductive withPMFI (I : Type u) : Type (max u (v + 1))
  | oracle (i : I)
  | sample {α : Type v} (d : PMF α)

def withPMFSpec {I : Type u} (O : OracleSpec I) : OracleSpec (withPMFI I)
  | .oracle i => O i
  | @withPMFI.sample _ α _ => α

/-- The definition of a reduction from an oracle `O₂` to an oracle `O₁`. -/
structure OracleReduction {I₁ I₂ : Type} (O₁ : OracleSpec I₁) (O₂ : OracleSpec I₂) where
  stateType : Type
  initialState : OracleComp (withPMFSpec O₁) stateType
  queries : QueryImpl O₂ (OracleComp (withPMFAndStateSpec stateType O₁))

/-- Computations available to a stateful randomized reduction over source oracle spec `O`. -/
abbrev OracleReduction.SRReductionComp {I : Type u} (O : OracleSpec I) (s : Type) :=
  OracleComp (withPMFAndStateSpec s O)


/- ## Syntax sugars for reductions operations -/

namespace OracleReduction

/-- Query the underlying source oracle from initialization code. -/
@[reducible, inline] def initQuery {I : Type u} {O : OracleSpec I}
    (i : I) : OracleComp (withPMFSpec O) (O.Range i) :=
  (withPMFSpec O).query (withPMFI.oracle i)

/-- Sample from an arbitrary `PMF` from initialization code. -/
@[reducible, inline] def initSample {I : Type u} {O : OracleSpec I} {α : Type}
    (p : PMF α) : OracleComp (withPMFSpec O) α :=
  (withPMFSpec O).query (withPMFI.sample p)

/-- Query the underlying source oracle while answering a reduction query. -/
@[reducible, inline] def query {I : Type u} {O : OracleSpec I} {s : Type}
    (i : I) : OracleComp (withPMFAndStateSpec s O) (O.Range i) :=
  (withPMFAndStateSpec s O).query (withPMFAndStateI.oracle i)

/-- Sample from an arbitrary `PMF` while answering a reduction query. -/
@[reducible, inline] def sample {I : Type u} {O : OracleSpec I} {s : Type} {α : Type}
    (p : PMF α) : OracleComp (withPMFAndStateSpec s O) α :=
  (withPMFAndStateSpec s O).query (withPMFAndStateI.sample p)

/-- Flip a fair coin while answering a reduction query. -/
@[reducible, inline] noncomputable def coinFlip {I : Type u} {O : OracleSpec I} {s : Type} :
    OracleComp (withPMFAndStateSpec s O) Bool :=
  sample (PMF.uniformOfFintype Bool)

/-- Read the reduction's local internal state. -/
@[reducible, inline] def get {I : Type u} {O : OracleSpec I} {s : Type} :
    OracleComp (withPMFAndStateSpec s O) s :=
  (withPMFAndStateSpec s O).query withPMFAndStateI.getState

/-- Write the reduction's local internal state. -/
@[reducible, inline] def set {I : Type u} {O : OracleSpec I} {s : Type} (st : s) :
    OracleComp (withPMFAndStateSpec s O) Unit :=
  (withPMFAndStateSpec s O).query (withPMFAndStateI.setState st)

/-- Modify the reduction's local internal state. -/
def modify {I : Type u} {O : OracleSpec I} {s : Type} (f : s → s) :
    OracleComp (withPMFAndStateSpec s O) Unit := do
  let st ← get (O := O) (s := s)
  set (O := O) (s := s) (f st)

/-- Syntax sugar for `OracleReduction.initQuery i`. -/
syntax "orInitQuery(" term ")" : term
/-- Syntax sugar for `OracleReduction.initSample p`. -/
syntax "orInitSample(" term ")" : term
/-- Syntax sugar for `OracleReduction.query i`. -/
syntax "orQuery(" term ")" : term
/-- Syntax sugar for `OracleReduction.sample p`. -/
syntax "orSample(" term ")" : term
/-- Syntax sugar for `OracleReduction.coinFlip`. -/
syntax "orCoin!" : term
/-- Syntax sugar for `OracleReduction.get`. -/
syntax "orGet!" : term
/-- Syntax sugar for `OracleReduction.set x`. -/
syntax "orSet(" term ")" : term
/-- Syntax sugar for `OracleReduction.modify f`. -/
syntax "orModify(" term ")" : term

macro_rules
  | `(orInitQuery($i)) => `(OracleReduction.initQuery $i)
  | `(orInitSample($p)) => `(OracleReduction.initSample $p)
  | `(orQuery($i)) => `(OracleReduction.query $i)
  | `(orSample($p)) => `(OracleReduction.sample $p)
  | `(orCoin!) => `(OracleReduction.coinFlip)
  | `(orGet!) => `(OracleReduction.get)
  | `(orSet($st)) => `(OracleReduction.set $st)
  | `(orModify($f)) => `(OracleReduction.modify $f)

/-- Build an `OracleReduction` while inferring the reduction state type. -/
def mk' {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂} {s : Type}
    (initialState : OracleComp (withPMFSpec O₁) s)
    (queries : QueryImpl O₂ (OracleComp (withPMFAndStateSpec s O₁))) :
    OracleReduction O₁ O₂ where
  stateType := s
  initialState := initialState
  queries := queries

noncomputable def identity {I : Type} (O : OracleSpec I) : OracleReduction O O where
  stateType := Unit
  initialState := pure ()
  queries := fun i => query i

end OracleReduction

/- ## Applying a reduction -/

/- A reduction from O₂ to O₁ can be applied to an implementation of an oracle for O₂ to obtain
an implementation of an oracle for O₁. Below we define this operation as a function `apply`.
  That requires combining computation over different specs (extended by withPMFAndStateSpec and not).
  To do this we lift computation `RState stateType` into `RState (reduction_state × stateType)` and then implement all operations from `withPMFAndStateSpec A` in `RState (reduction_state × stateType)`.
 -/

noncomputable def addPMFtoImpl {I : Type} {O : OracleSpec I} {stateType : Type}
  (impl : QueryImpl O (RState stateType)) :
  QueryImpl (withPMFSpec O) (RState stateType) := fun
    | withPMFI.oracle t => impl t
    | withPMFI.sample p =>
        (liftM (m := PMF) (n := RState stateType) p)

namespace OracleReduction


/-- First we show how to interpret reduction operations as computation in RState -/
noncomputable def liftWithPMFAndState {I : Type} {O : OracleSpec I} {stateType : Type}
    (impl : QueryImpl O (RState stateType)) (addState : Type) :
    QueryImpl (withPMFAndStateSpec addState O) (RState (addState × stateType)) := fun
  | withPMFAndStateI.oracle i => do
      let st ← StateT.get
      let (u, sₒ') ← liftM (StateT.run (impl i) st.2)
      RState.modify (fun x ↦ ⟨x.1, sₒ'⟩)
      pure u
  | withPMFAndStateI.sample p =>
      liftM p
  | withPMFAndStateI.getState =>
      (fun x => x.1) <$> StateT.get
  | withPMFAndStateI.setState sᵣ' =>
      RState.modify (fun x => ⟨sᵣ', x.2⟩)


/-- Apply an oracle reduction to an underlying stateful oracle implementation. -/
noncomputable def apply {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : OracleReduction O₁ O₂) (oracle : OracleImpl O₁) : OracleImpl O₂ where
  stateType := reduction.stateType × oracle.stateType
  initialState := do
    /- The initial state of the inner oracle is computed using its initialization function -/
    let sₒ ← oracle.initialState
    /- The local state of the reduction is computed using the reduction's initialization function -/
    let (sᵣ, sₒ') ←
      liftM (StateT.run (simulateQ (addPMFtoImpl oracle.queries) reduction.initialState) sₒ)
    /- The two states are combined -/
    pure (sᵣ, sₒ')
  queries := fun i =>
    simulateQ (liftWithPMFAndState oracle.queries reduction.stateType) (reduction.queries i)

/-- Infix notation for applying an oracle reduction to an oracle. -/
infixl:70 " ◇ " => OracleReduction.apply


/- # Composition of reduction with adversary
 To compose reduction with its user, we run simulateQ using oracle reduction.queries. That gives us a combined object as computation using interface `withPMFAndStateSpec reduction_state O₁` instead of `O₁`.
  Then, we remove the state passing by implementing `OracleComp (withPMFAndStateSpec reduction_state O₁)` in `statefulOracleComp (withPMFSpec O) state`. -/

@[reducible]
def statefulOracleComp {I : Type _} (O : OracleSpec I) (state : Type) : Type _ -> Type _ := StateT state (OracleComp O)
instance {I : Type _} (O : OracleSpec I) (state : Type) [Monad (OracleComp O)] : Monad (statefulOracleComp O state) := StateT.instMonad

def statefulOracleComp_pure {I : Type _} (O : OracleSpec I)
  (x : α) : (pure x : statefulOracleComp O I α) = (fun s ↦ PFunctor.FreeM.pure (x, s)) := by
    rfl

def statefulOracleComp_bind {S β α : Type _} {I : Type _} (O : OracleSpec I)
  (x : statefulOracleComp O S β) (f : β -> statefulOracleComp O S α) (s : S) :
  (x >>= f) s = (x s) >>= (fun (a, b) => f a b) := by
    rfl

def defaultImpl {I : Type} {O : OracleSpec I} {state : Type}
  : QueryImpl (withPMFAndStateSpec state O) (statefulOracleComp (withPMFSpec O) state) := fun
  | .oracle a =>
    StateT.lift (OracleComp.queryBind (withPMFI.oracle a) (fun x => return x))
    -- the same as `StateT.lift (OracleComp.lift (OracleSpec.query (withPMFI.oracle a)))`, choose which to use
  | .sample a =>
    StateT.lift (OracleComp.queryBind (withPMFI.sample a) (fun x => return x))
  | .getState =>
    do
      let x <- StateT.get
      return x
  | .setState a =>
    do
      let _ <- StateT.set a
      return ()

def addPMFtoImpl2 {stateType : Type}
  (impl : QueryImpl O₂ (SRReductionComp O₁ stateType)) :
  QueryImpl (withPMFSpec O₂) (SRReductionComp O₁ stateType) := fun
| withPMFI.oracle t => impl t
| withPMFI.sample p =>
    OracleComp.lift (OracleSpec.query (withPMFAndStateI.sample p))

def lower_state_passing {I₁ state Output : Type} {O₁ : OracleSpec I₁}
    (comp : OracleComp (withPMFAndStateSpec state O₁) Output) (init : state) :
    OracleComp (withPMFSpec O₁) Output :=
  let x : statefulOracleComp (withPMFSpec O₁) state Output :=
    simulateQ (@defaultImpl I₁ O₁ state) comp
  let y : OracleComp (withPMFSpec O₁) (Output × state) := x init
  y <&> (fun x => x.1)

/-- Next, we show how to apply oracle reduction, the other way around, i.e. to the adversary -/
def applyReductionToAdversary {Output I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    (reduction : OracleReduction O₁ O₂) (dist : OracleComp (withPMFSpec O₂) Output)
    : OracleComp (withPMFSpec O₁) Output :=
    let x : OracleComp (withPMFAndStateSpec reduction.stateType O₁) Output :=
      simulateQ (addPMFtoImpl2 reduction.queries) dist
    do
      let sample : reduction.stateType <- reduction.initialState
      lower_state_passing x sample

end OracleReduction
