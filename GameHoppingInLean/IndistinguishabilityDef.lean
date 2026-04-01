import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence

/-- For each oracle spec `O`, a set of oracle pairs on `O` that may be assumed
indistinguishable. -/
abbrev IndistinguishabilityAssumptions :=
  {I : Type} → (O : OracleSpec I) → Set (RStateOracleFam O × RStateOracleFam O)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed stateful randomized reductions
from `O₁` to `O₂`. -/
abbrev IndistinguishabilitySRReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) → Set (SRReduction O₁ O₂)

/-- For each pair of specs `(O₁, O₂)`, a set of allowed reductions whose initialization may
query the source oracle. -/
abbrev IndistinguishabilityComplexInitReductions :=
  {I₁ I₂ : Type} → (O₁ : OracleSpec I₁) → (O₂ : OracleSpec I₂) →
    Set (ComplexInitReduction O₁ O₂)

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
  complexInitReductions : IndistinguishabilityComplexInitReductions
  simpleReductions : IndistinguishabilitySimpleReductions
  randomReductions : IndistinguishabilityRandomReductions

/-- Inductively generated indistinguishability relation for a fixed oracle spec.

Indexed by:
* `Assumptions`: assumption pairs, per oracle spec.
* `Reductions`: allowed reductions (simple, randomized-stateless, stateful-randomized,
  complex-initialization),
  per source/target oracle specs.

The relation is homogeneous in `O`, but reduction steps may move to a different spec
by changing the index parameter of the conclusion. -/

def ro_seq_fixed {I : Type} {O : OracleSpec I} (l : ℕ)
    (ro : Finset.range (1+l) -> RStateOracle O) (i : ℕ) (H : i <= l) : RStateOracle O :=
    ro ⟨i, by simp [Finset.range, H]; exact Nat.lt_one_add_iff.mpr H⟩


universe u v w


inductive Indistinguishable
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions) (κ : ℕ) :
    (q_b : Option ℕ) -> {I : Type} → (O : OracleSpec I) → RStateOracle O → RStateOracle O → Type 1
  | assumption {I : Type 0} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : Option ℕ):
      (as : (RStateOracleFam O × RStateOracleFam O)) -> (as ∈ Assumptions O) ->
      (ro₁ = as.1 κ /\ ro₂ = as.2 κ) ->
      Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂
  | obsEq {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : Option ℕ):
      ObsEq ro₁ ro₂ →
      Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂
  | simpleReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : simpleReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} (q_b : Option ℕ):
      Indistinguishable Assumptions Reductions κ none O₁ ro₁ ro₂ →
      r ∈ Reductions.simpleReductions O₁ O₂ →
      Indistinguishable Assumptions Reductions κ q_b O₂
        (applySimpleReduction r ro₁) (applySimpleReduction r ro₂)
  | reduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : SRReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} (q_b : Option ℕ):
      Indistinguishable Assumptions Reductions κ none O₁ ro₁ ro₂ →
      r ∈ Reductions.reductions O₁ O₂ →
      Indistinguishable Assumptions Reductions κ q_b O₂
        (applySRReduction r ro₁) (applySRReduction r ro₂)
  | complexInitReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : ComplexInitReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} (q_b : Option ℕ):
      Indistinguishable Assumptions Reductions κ none O₁ ro₁ ro₂ →
      r ∈ Reductions.complexInitReductions O₁ O₂ →
      Indistinguishable Assumptions Reductions κ q_b O₂
        (applyComplexInitReduction r ro₁) (applyComplexInitReduction r ro₂)
  | randReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : RReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} (q_b : Option ℕ):
      Indistinguishable Assumptions Reductions κ none O₁ ro₁ ro₂ →
      r ∈ Reductions.randomReductions O₁ O₂ →
      Indistinguishable Assumptions Reductions κ q_b O₂
        (applyRReduction r ro₁) (applyRReduction r ro₂)
  | symm {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : Option ℕ):
      Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂ →
      Indistinguishable Assumptions Reductions κ q_b O ro₂ ro₁
  | trans {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : RStateOracle O} (q_b : Option ℕ):
      Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂ →
      Indistinguishable Assumptions Reductions κ q_b O ro₂ ro₃ →
      Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₃
  | longSequence {I : Type} {O : OracleSpec I} (l : ℕ) (ro : Finset.range (1+l) -> RStateOracle O)
    (ro_start : RStateOracle O) (ro_end :  RStateOracle O ) (q_b : Option ℕ):
    (Hstart : Indistinguishable Assumptions Reductions κ q_b O ro_start (ro ⟨0, by simp [Finset.range]⟩)) ->
    (Hend : Indistinguishable Assumptions Reductions κ q_b O ro_end (ro ⟨l, by simp [Finset.range]⟩)) ->
    (forall i, (Hi: i < l) ->
      Indistinguishable Assumptions Reductions κ q_b O
        (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed l ro (i+1) Hi)
    ) ->
    Indistinguishable Assumptions Reductions κ q_b O ro_start ro_end


namespace Indistinguishable

def of_ObsEq
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {κ q_b :  ℕ}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
    ObsEq ro₁ ro₂ →
    Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂ :=
  Indistinguishable.obsEq q_b

def transitive
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {κ q_b :  ℕ}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : RStateOracle O}:
    (Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂) ->
    (Indistinguishable Assumptions Reductions κ q_b O ro₂ ro₃) ->
    (Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₃) :=
  fun Ha Hb => Indistinguishable.trans q_b Ha Hb

def symmetric
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {κ q_b :  ℕ}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}:
    (Indistinguishable Assumptions Reductions κ q_b O ro₁ ro₂) ->
    (Indistinguishable Assumptions Reductions κ q_b O ro₂ ro₁) :=
  fun Ha => Indistinguishable.symm q_b Ha

end Indistinguishable
