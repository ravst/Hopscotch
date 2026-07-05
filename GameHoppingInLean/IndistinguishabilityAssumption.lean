import GameHoppingInLean.OracleReductions


/- ## Indisringuishability Assumptions -/

/- A single indistinguishability assumption, consists of an oracle specification over a set of queries,
and a pair of oracles of that specifications, which we assume to be indistinguishable.
-/
structure SingleAssumption where
  {I : Type}
  {O : OracleSpec I}
  i : RStateOracle O × RStateOracle O

def SingleAssumption.reverse (x : SingleAssumption) : SingleAssumption :=
  {x with i := (x.i.2, x.i.1)}

/- Indistinguishability Assumptions are modeled as an indexed family of single assumptions.
The index type is arbitrary, but we require it to be decidable, so that it is easier to
count how many times each assumption is used in a proof. -/
structure IndAssumptions where
  Idx : Type
  [decEq : DecidableEq Idx]
  assumptions : Idx -> SingleAssumption

abbrev IndAssumptionsFam :=
  (κ : ℕ) → IndAssumptions

namespace IndAssumptions

def empty : IndAssumptions := {
  Idx := Empty,
  assumptions := fun x => Empty.elim x
  }

instance {A : IndAssumptions} : DecidableEq A.Idx := A.decEq



/-- Disjoint union of two assumption families. The resulting index type is the sum of the
original index types, and each side is selected by `Sum.inl` or `Sum.inr`. -/
def oplus (A B : IndAssumptions) : IndAssumptions where
  Idx := Sum A.Idx B.Idx
  assumptions := fun
    | Sum.inl i => A.assumptions i
    | Sum.inr i => B.assumptions i

end IndAssumptions

class OPlus (α : Type u) where
  oplus : α → α → α

instance : OPlus IndAssumptions where
  oplus := IndAssumptions.oplus

instance : OPlus IndAssumptionsFam where
  oplus A B := fun κ => OPlus.oplus (A κ) (B κ)

infixl:65 " ⊕ " => OPlus.oplus
