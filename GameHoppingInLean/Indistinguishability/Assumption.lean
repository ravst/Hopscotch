import GameHoppingInLean.Comp.OracleReductions


/- ## Indistinguishability Assumptions
Our proofs of indistinguishability involves list of assumption, that could be used in the proof. Here, we define the type of such assumptions.
A single indistinguishability assumption, consists of an oracle specification over a set of queries,
and a pair of oracles of that specifications, which we assume to be indistinguishable.
-/
structure SingleAssumption where
  {I : Type}
  {O : OracleSpec I}
  i : OracleImpl O × OracleImpl O

def SingleAssumption.reverse (x : SingleAssumption) : SingleAssumption :=
  {x with i := (x.i.2, x.i.1)}

/- Indistinguishability Assumptions are modeled as an indexed family of single assumptions.
The index type is arbitrary, but we require it to be decidable, so that it is possible to
count how many times each assumption is used in a proof. -/
structure IndAssumptions (Idx : Type) where
  [decEq : DecidableEq Idx]
  assumptions : Idx -> SingleAssumption

/-- Fiamly of assumptions, one for each vlaue of security parameter κ. We require that the whole family have the same Idx, so we can relata the use of single assumption for different security parameter with each other. -/
structure IndAssumptionsFam where
  Idx : Type
  val : (κ : ℕ) → IndAssumptions Idx

namespace IndAssumptions

def empty : IndAssumptions Empty := {
  assumptions := fun x => Empty.elim x
  }


/- Local instance: use `haveI : DecidableEq Idx := Assumptions.decEq` in functions
that need it, rather than relying on global typeclass search, to avoid loops. -/
instance {Idx : Type} {A : IndAssumptions Idx} : DecidableEq Idx := A.decEq

/-- Disjoint union of two assumption families. The resulting index type is the sum of the
original index types, and each side is selected by `Sum.inl` or `Sum.inr`. -/
def oplus {AIdx BIdx : Type} (A : IndAssumptions AIdx) (B : IndAssumptions BIdx) :
  IndAssumptions (Sum AIdx BIdx) where
  assumptions := fun
    | Sum.inl i => A.assumptions i
    | Sum.inr i => B.assumptions i
  decEq :=
    have _X : DecidableEq AIdx := A.decEq
    have _Y : DecidableEq BIdx := B.decEq
    inferInstance

def oplusFam (A B : IndAssumptionsFam) : IndAssumptionsFam where
  Idx := Sum A.Idx B.Idx
  val κ := oplus (A.val κ) (B.val κ)

end IndAssumptions



class OPlus (α : Type u) where
  oplus : α → α → α

-- instance : OPlus IndAssumptions where
--   oplus := IndAssumptions.oplus

instance : OPlus IndAssumptionsFam where
  oplus A B := IndAssumptions.oplusFam A B

infixl:65 " ⊕ " => IndAssumptions.oplusFam
