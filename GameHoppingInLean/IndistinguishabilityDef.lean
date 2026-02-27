import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence

/-- For each oracle spec `O`, a set of oracle pairs on `O` that may be assumed
indistinguishable. -/
abbrev IndistinguishabilityAssumptions :=
  {I : Type} → (O : OracleSpec I) → Set (RStateOracle O × RStateOracle O)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed stateful randomized reductions
from `O₁` to `O₂`. -/
abbrev IndistinguishabilitySRReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) → Set (SRReduction O₁ O₂)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed randomized (stateless) reductions
from `O₁` to `O₂`. -/
abbrev IndistinguishabilityRandomReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) → Set (RReduction O₁ O₂)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed simple reductions
from `O₁` to `O₂`. -/
abbrev IndistinguishabilitySimpleReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) → Set (simpleReduction O₁ O₂)

/-- Reduction sets used in indistinguishability proofs. -/
structure IndistinguishabilityReductions where
  reductions : IndistinguishabilitySRReductions
  simpleReductions : IndistinguishabilitySimpleReductions
  randomReductions : IndistinguishabilityRandomReductions

/-- Inductively generated indistinguishability relation for a fixed oracle spec.

Indexed by:
* `Assumptions`: assumption pairs, per oracle spec.
* `Reductions`: allowed reductions (simple, randomized-stateless, stateful-randomized),
  per source/target oracle specs.

The relation is homogeneous in `O`, but reduction steps may move to a different spec
by changing the index parameter of the conclusion. -/
inductive Indistinguishable
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions) :
    {I : Type} → (O : OracleSpec I) → RStateOracle O → RStateOracle O → Prop
  | assumption {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      (ro₁, ro₂) ∈ Assumptions O →
      Indistinguishable Assumptions Reductions O ro₁ ro₂
  | obsEq {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      ObsEq ro₁ ro₂ →
      Indistinguishable Assumptions Reductions O ro₁ ro₂
  | simpleReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : simpleReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} :
      Indistinguishable Assumptions Reductions O₁ ro₁ ro₂ →
      r ∈ Reductions.simpleReductions O₁ O₂ →
      Indistinguishable Assumptions Reductions O₂
        (applySimpleReduction r ro₁) (applySimpleReduction r ro₂)
  | reduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : SRReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} :
      Indistinguishable Assumptions Reductions O₁ ro₁ ro₂ →
      r ∈ Reductions.reductions O₁ O₂ →
      Indistinguishable Assumptions Reductions O₂
        (applySRReduction r ro₁) (applySRReduction r ro₂)
  | randReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : RReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} :
      Indistinguishable Assumptions Reductions O₁ ro₁ ro₂ →
      r ∈ Reductions.randomReductions O₁ O₂ →
      Indistinguishable Assumptions Reductions O₂
        (applyRReduction r ro₁) (applyRReduction r ro₂)
  | symm {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      Indistinguishable Assumptions Reductions O ro₁ ro₂ →
      Indistinguishable Assumptions Reductions O ro₂ ro₁
  | trans {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : RStateOracle O} :
      Indistinguishable Assumptions Reductions O ro₁ ro₂ →
      Indistinguishable Assumptions Reductions O ro₂ ro₃ →
      Indistinguishable Assumptions Reductions O ro₁ ro₃

namespace Indistinguishable

theorem of_ObsEq
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
    ObsEq ro₁ ro₂ →
    Indistinguishable Assumptions Reductions O ro₁ ro₂ :=
  Indistinguishable.obsEq

theorem transitive
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {I : Type} {O : OracleSpec I} :
    Transitive (Indistinguishable Assumptions Reductions O) :=
  fun _ _ _ => Indistinguishable.trans

theorem symmetric
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {I : Type} {O : OracleSpec I} :
    Symmetric (Indistinguishable Assumptions Reductions O) :=
  fun _ _ => Indistinguishable.symm

end Indistinguishable
