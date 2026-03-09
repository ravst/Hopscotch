import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.MAC

/-- Query indices for the MAC unforgeability interface. -/
inductive MACUFQ where
  | getTag (n : ℕ)
  | checkTag (n : ℕ)

/-- A length-indexed `(message, tag)` pair stored by the ideal oracle. -/
abbrev MACTaggedMessage (Tag : Type) := Σ n : ℕ, BitVec n × Tag

/-- State of the ideal MAC oracle: secret key and the set of issued `(message, tag)` pairs. -/
structure MACUFIdealState (K Tag : Type) where
  key : K
  seen : Finset (MACTaggedMessage Tag)

/-- Oracle spec with two query kinds:
* `getTag n`: input message `m : BitVec n`, output tag `t : Tag`
* `checkTag n`: input `(m, t)`, output verification bit -/
def MACUFSpec (Tag : Type) : OracleSpec MACUFQ
  | .getTag n => (BitVec n, Tag)
  | .checkTag n => (BitVec n × Tag, Bool)

/-- Convenience query constructor for `GetTag(m)`. -/
@[reducible, inline] def getTagQ {Tag : Type} {n : ℕ} (m : BitVec n) :
    OracleComp (MACUFSpec Tag) Tag :=
  (MACUFSpec Tag).query (.getTag n) m

/-- Convenience query constructor for `CheckTag(m, t)`. -/
@[reducible, inline] def checkTagQ {Tag : Type} {n : ℕ} (m : BitVec n) (t : Tag) :
    OracleComp (MACUFSpec Tag) Bool :=
  (MACUFSpec Tag).query (.checkTag n) (m, t)

/-- Real MAC oracle:
* `GetTag(m)` returns `tag_k(m)`
* `CheckTag(m, t)` returns deterministic `check_k(m, t)` -/
noncomputable def MACUFReal {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    RStateOracle (MACUFSpec Tag) where
  stateType := K
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query (MACUFQ.getTag _) m => do
          let key ← get
          pure (scheme.tag key m)
      | OracleSpec.query (MACUFQ.checkTag _) (m, t) => do
          let key ← get
          pure (scheme.check key m t)
  }

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
  queries := {
    impl := fun
      | OracleSpec.query (MACUFQ.getTag n) m => do
          let st ← get
          let t := scheme.tag st.key m
          set { st with seen := insert (⟨n, (m, t)⟩ : MACTaggedMessage Tag) st.seen }
          pure t
      | OracleSpec.query (MACUFQ.checkTag n) (m, t) => do
          let st ← get
          pure (decide ((⟨n, (m, t)⟩ : MACTaggedMessage Tag) ∈ st.seen))
  }

/-- The oracle pair corresponding to the MAC unforgeability assumption. -/
noncomputable def MACUFAssumption {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) :
    RStateOracle (MACUFSpec Tag) × RStateOracle (MACUFSpec Tag) :=
  (MACUFReal scheme, MACUFIdeal scheme)

/-- MAC unforgeability security definition as an instance of `Indistinguishable`. -/
def MACUFDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {K Tag : Type} [DecidableEq Tag] (scheme : MACScheme K Tag) : Prop :=
  Indistinguishable Assumptions Reductions
    (MACUFSpec Tag) (MACUFReal scheme) (MACUFIdeal scheme)
