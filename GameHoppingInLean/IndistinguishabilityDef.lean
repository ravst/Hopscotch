import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence

/-- For each oracle spec `O`, a set of oracle pairs on `O` that may be assumed
indistinguishable. -/
abbrev IndistinguishabilityAssumptions :=
  {I : Type} → (O : OracleSpec I) → Set (RStateOracle O × RStateOracle O)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed stateful randomized reductions
from `O₁` to `O₂`. -/
abbrev IndistinguishabilityReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) → Set (SRReduction O₁ O₂)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed simple reductions
from `O₁` to `O₂`. -/
abbrev IndistinguishabilitySimpleReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) → Set (simpleReduction O₁ O₂)

/-- Inductively generated indistinguishability relation for a fixed oracle spec.

Indexed by:
* `Assumptions`: assumption pairs, per oracle spec.
* `SimpleReductions`: allowed simple reductions, per source/target oracle specs.
* `Reductions`: allowed stateful randomized reductions, per source/target oracle specs.

The relation is homogeneous in `O`, but reduction steps may move to a different spec
by changing the index parameter of the conclusion. -/
inductive Indistinguishable
    (Assumptions : IndistinguishabilityAssumptions)
    (SimpleReductions : IndistinguishabilitySimpleReductions)
    (Reductions : IndistinguishabilityReductions) :
    {I : Type} → (O : OracleSpec I) → RStateOracle O → RStateOracle O → Prop
  | assumption {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      (ro₁, ro₂) ∈ Assumptions O →
      Indistinguishable Assumptions SimpleReductions Reductions O ro₁ ro₂
  | obsEq {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      ObsEq ro₁ ro₂ →
      Indistinguishable Assumptions SimpleReductions Reductions O ro₁ ro₂
  | simpleReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : simpleReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} :
      Indistinguishable Assumptions SimpleReductions Reductions O₁ ro₁ ro₂ →
      r ∈ SimpleReductions O₁ O₂ →
      Indistinguishable Assumptions SimpleReductions Reductions O₂
        (applySimpleReduction r ro₁) (applySimpleReduction r ro₂)
  | reduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : SRReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} :
      Indistinguishable Assumptions SimpleReductions Reductions O₁ ro₁ ro₂ →
      r ∈ Reductions O₁ O₂ →
      Indistinguishable Assumptions SimpleReductions Reductions O₂
        (applySRReduction r ro₁) (applySRReduction r ro₂)
  | symm {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      Indistinguishable Assumptions SimpleReductions Reductions O ro₁ ro₂ →
      Indistinguishable Assumptions SimpleReductions Reductions O ro₂ ro₁
  | trans {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : RStateOracle O} :
      Indistinguishable Assumptions SimpleReductions Reductions O ro₁ ro₂ →
      Indistinguishable Assumptions SimpleReductions Reductions O ro₂ ro₃ →
      Indistinguishable Assumptions SimpleReductions Reductions O ro₁ ro₃

namespace Indistinguishable

theorem of_ObsEq
    {Assumptions : IndistinguishabilityAssumptions}
    {SimpleReductions : IndistinguishabilitySimpleReductions}
    {Reductions : IndistinguishabilityReductions}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
    ObsEq ro₁ ro₂ →
    Indistinguishable Assumptions SimpleReductions Reductions O ro₁ ro₂ :=
  Indistinguishable.obsEq

theorem transitive
    {Assumptions : IndistinguishabilityAssumptions}
    {SimpleReductions : IndistinguishabilitySimpleReductions}
    {Reductions : IndistinguishabilityReductions}
    {I : Type} {O : OracleSpec I} :
    Transitive (Indistinguishable Assumptions SimpleReductions Reductions O) :=
  fun _ _ _ => Indistinguishable.trans

theorem symmetric
    {Assumptions : IndistinguishabilityAssumptions}
    {SimpleReductions : IndistinguishabilitySimpleReductions}
    {Reductions : IndistinguishabilityReductions}
    {I : Type} {O : OracleSpec I} :
    Symmetric (Indistinguishable Assumptions SimpleReductions Reductions O) :=
  fun _ _ => Indistinguishable.symm

end Indistinguishable
