import GameHoppingInLean.OracleReductions


/- ## Indisringuishability Assumptions -/

/- A single indistinguishability assumption, consists of an oracle specification over a set of queries,
and a pair of oracles of that specifications, which we assume to be indistinguishable.
-/
structure SingleAssumption where
  I : Type
  O : OracleSpec I
  i : RStateOracle O × RStateOracle O

/- Indistinguishability Assumptions are modeled as an indexed family of single assumptions.
The index type is arbitrary, but we require it to be decidable, so that it is easier to
count how many times each assumption is used in a proof. -/
structure IndistinguishabilityAssumptions where
  Idx : Type
  [decEq : DecidableEq Idx]
  assumptions : Idx -> SingleAssumption

namespace IndistinguishabilityAssumptions

def empty : IndistinguishabilityAssumptions := {
  Idx := Empty,
  assumptions := fun x => Empty.elim x
  }

instance {A : IndistinguishabilityAssumptions} : DecidableEq A.Idx := A.decEq

/-- Disjoint union of two assumption families. The resulting index type is the sum of the
original index types, and each side is selected by `Sum.inl` or `Sum.inr`. -/
def oplus (A B : IndistinguishabilityAssumptions) : IndistinguishabilityAssumptions where
  Idx := Sum A.Idx B.Idx
  assumptions := fun
    | Sum.inl i => A.assumptions i
    | Sum.inr i => B.assumptions i


infixl:65 " ⊕ " => IndistinguishabilityAssumptions.oplus

end IndistinguishabilityAssumptions
