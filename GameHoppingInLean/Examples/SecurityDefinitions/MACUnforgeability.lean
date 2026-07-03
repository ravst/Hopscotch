import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.MAC
import GameHoppingInLean.Misc.SimpAttrs

/-- A length-indexed `(message, tag)` pair stored by the ideal oracle. -/
abbrev MACTaggedMessage (Tag : Type) := Σ n : ℕ, BitVec n × Tag

/-- State of the ideal MAC oracle: secret key and the set of issued `(message, tag)` pairs. -/
structure MACUFIdealState (K Tag : Type) where
  key : K
  seen : Finset (MACTaggedMessage Tag)

/-- Query domain for the MAC unforgeability interface. -/
inductive MACUFQ (Tag : Type) where
  | getTag (n : ℕ) (m : BitVec n)
  | checkTag (n : ℕ) (m : BitVec n) (t : Tag)

/-- Oracle spec with two query kinds:
* `getTag n m`: output tag `t : Tag`
* `checkTag n m t`: output verification bit -/
def MACUFSpec (Tag : Type) : OracleSpec (MACUFQ Tag)
  | .getTag _ _ => Tag
  | .checkTag _ _ _ => Bool

/-- Convenience query constructor for `GetTag(m)`. -/
@[reducible, inline] def getTagQ {Tag : Type} {n : ℕ} (m : BitVec n) :
    OracleComp (MACUFSpec Tag) Tag :=
  (MACUFSpec Tag).query (.getTag n m)

/-- Convenience query constructor for `CheckTag(m, t)`. -/
@[reducible, inline] def checkTagQ {Tag : Type} {n : ℕ} (m : BitVec n) (t : Tag) :
    OracleComp (MACUFSpec Tag) Bool :=
  (MACUFSpec Tag).query (.checkTag n m t)

/-- Real MAC oracle:
* `GetTag(m)` returns `tag_k(m)`
* `CheckTag(m, t)` returns deterministic `check_k(m, t)` -/
noncomputable def MACUFReal {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    RStateOracle (MACUFSpec Tag) where
  stateType := K
  initialState := scheme.keyGen
  queries := fun
      | MACUFQ.getTag _ m => do
          let key ← get
          pure (scheme.tag key m)
      | MACUFQ.checkTag _ m t => do
          let key ← get
          pure (scheme.check key m t)

/-- Ideal MAC oracle:
* stores key and a set of previously returned `(message, tag)` pairs
* `GetTag(m)` returns `tag_k(m)` and records `(m, tag_k(m))`
* `CheckTag(m, t)` returns `true` iff `(m, t)` is in the recorded set -/
noncomputable def MACUFIdeal {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    RStateOracle (MACUFSpec Tag) where
  stateType := MACUFIdealState K Tag
  initialState := do
    let key ← scheme.keyGen
    pure { key := key, seen := ∅ }
  queries := fun
      | MACUFQ.getTag n m => do
          let st ← get
          let t := scheme.tag st.key m
          set { st with seen := insert (⟨n, (m, t)⟩ : MACTaggedMessage Tag) st.seen }
          pure t
      | MACUFQ.checkTag n m t => do
          let st ← get
          pure (decide ((⟨n, (m, t)⟩ : MACTaggedMessage Tag) ∈ st.seen))

/-- The oracle pair corresponding to the MAC unforgeability assumption. -/
noncomputable def MACUFAssumption {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    RStateOracle (MACUFSpec Tag) × RStateOracle (MACUFSpec Tag) :=
  (MACUFReal scheme, MACUFIdeal scheme)

noncomputable def MACUFAssumptionFull {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    SingleAssumption :=
  ⟨MACUFQ Tag, MACUFSpec Tag, MACUFAssumption scheme⟩

noncomputable def MACUFAssumption' {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    IndistinguishabilityAssumptions where
  Idx := Unit
  assumptions := fun _ => MACUFAssumptionFull scheme

/-- MAC unforgeability security definition as an instance of `Indistinguishable`. -/
def MACUFDef
    (Assumptions : IndistinguishabilityAssumptions)
    {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) : Type 1 :=
  Indistinguishable Assumptions
   (MACUFReal scheme) (MACUFIdeal scheme)

/-- Pointwise MAC-UF assumptions for a MAC family. -/
noncomputable def MACUFAssumptionFam {K Tag : ℕ → Type}
    [∀ κ, DecidableEq (Tag κ)]
    (schemeFam : MACSchemeFamily K Tag) (κ : ℕ) :
    IndistinguishabilityAssumptions :=
  MACUFAssumption' (schemeFam.scheme κ)

/-- MAC unforgeability for a MAC family. -/
def MACUFIFam
    (Assumptions : (κ : ℕ) → IndistinguishabilityAssumptions)
    {K Tag : ℕ → Type} [∀ κ, DecidableEq (Tag κ)]
    (schemeFam : MACSchemeFamily K Tag) : Type 1 :=
  ∀ κ,
    IndistinguishableI (Assumptions κ) none
      (MACUFReal (schemeFam.scheme κ)) (MACUFIdeal (schemeFam.scheme κ))
