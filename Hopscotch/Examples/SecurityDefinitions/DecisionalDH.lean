import Hopscotch.Indistinguishability.Def
import Hopscotch.Examples.Misc.Groups

/-- Query indices for the decisional Diffie-Hellman interface. -/
inductive DecisionalDHQ where
  | query

/-- DDH oracle spec: the single query returns a triple of group elements. -/
def DecisionalDHSpec (G : Type) : OracleSpec DecisionalDHQ
  | .query => G × G × G

/-- Convenience query constructor for the DDH oracle interface. -/
@[reducible, inline] def dhQuery {G : Type} :
    OracleComp (DecisionalDHSpec G) (G × G × G) :=
  (DecisionalDHSpec G).query .query

/-- Real DDH oracle: sample exponents `a, b` and return `(g^a, g^b, g^(ab))`. -/
noncomputable def dhReal {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    OracleImpl (DecisionalDHSpec G) where
  stateType := Unit
  initialState := pure ()
  queries := fun
    | .query => do
      let a <- sampleExponent G
      let b <- sampleExponent G
      pure (g ^ a, g ^ b, g ^ (a * b))

/-- Random DDH oracle: sample exponents `a, b, c` and return `(g^a, g^b, g^c)`. -/
noncomputable def dhRand {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    OracleImpl (DecisionalDHSpec G) where
  stateType := Unit
  initialState := pure ()
  queries := fun
    | .query => do
      let a <- sampleExponent G
      let b <- sampleExponent G
      let c <- sampleExponent G
      pure (g ^ a, g ^ b, g ^ c)

/-- The oracle pair corresponding to the DDH assumption, for use in an `Assumptions` set. -/
noncomputable def DecisionalDHAssumption {G : Type}
    [Group G] [Fintype G] [Nontrivial G] (g : G) :
    OracleImpl (DecisionalDHSpec G) × OracleImpl (DecisionalDHSpec G) :=
  (dhReal g, dhRand g)

noncomputable def DecisionalDHAssumptionFull {G : Type}
    [Group G] [Fintype G] [Nontrivial G] (g : G) :
    SingleAssumption :=
  { i := DecisionalDHAssumption g }

noncomputable def DecisionalDHAssumption' {G : Type}
    [Group G] [Fintype G] [Nontrivial G] (g : G) :
    IndAssumptions Unit where
  assumptions := fun _ => DecisionalDHAssumptionFull g

noncomputable def DecisionalDHAssumptionFam (Γ : GroupGeneratorFamily) :
    IndAssumptionsFam where
  Idx := Unit
  val κ := by
    letI := Γ.group κ
    letI := Γ.fintype κ
    letI := Γ.nontrivial κ
    exact DecisionalDHAssumption' (Γ.gen κ)

/-- DDH security definition as an instance of `Indistinguishable`. -/
def DecisionalDHDef
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) : Type 1 :=
  IndistinguishableSingle Assumptions
    (dhReal g) (dhRand g)

def DecisionalDHIFam
    {Idx : Type} (Assumptions : (κ : ℕ) → IndAssumptions Idx)
    (Γ : GroupGeneratorFamily) : Type 1 :=
  ∀ κ,
    letI := Γ.group κ
    letI := Γ.fintype κ
    letI := Γ.nontrivial κ
    IndistinguishableI (Assumptions κ) none
      (dhReal (Γ.gen κ)) (dhRand (Γ.gen κ))
