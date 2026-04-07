import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Misc.Groups

/-- Query indices for the decisional Diffie-Hellman interface. -/
inductive DecisionalDHQ where
  | querry

/-- DDH oracle spec: the single query returns a triple of group elements. -/
def DecisionalDHSpec (G : Type) : OracleSpec DecisionalDHQ
  | .querry => (Unit, G × G × G)

/-- Convenience query constructor for the DDH oracle interface. -/
@[reducible, inline] def dhQuerry {G : Type} :
    OracleComp (DecisionalDHSpec G) (G × G × G) :=
  (DecisionalDHSpec G).query .querry ()

/-- Real DDH oracle: sample exponents `a, b` and return `(g^a, g^b, g^(ab))`. -/
noncomputable def dhReal {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    RStateOracle (DecisionalDHSpec G) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun _ _ => do
      let a <- sampleExponent G
      let b <- sampleExponent G
      pure (g ^ a, g ^ b, g ^ (a * b))
  }

/-- Random DDH oracle: sample exponents `a, b, c` and return `(g^a, g^b, g^c)`. -/
noncomputable def dhRand {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    RStateOracle (DecisionalDHSpec G) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun _ _ => do
      let a <- sampleExponent G
      let b <- sampleExponent G
      let c <- sampleExponent G
      pure (g ^ a, g ^ b, g ^ c)
  }

/-- The oracle pair corresponding to the DDH assumption, for use in an `Assumptions` set. -/
noncomputable def DecisionalDHAssumption {G : Type}
    [Group G] [Fintype G] [Nontrivial G] (g : G) :
    RStateOracle (DecisionalDHSpec G) × RStateOracle (DecisionalDHSpec G) :=
  (dhReal g, dhRand g)

/-- DDH security definition as an instance of `Indistinguishable`. -/
def DecisionalDHDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) : Type 1 :=
  Indistinguishable Assumptions Reductions
    (DecisionalDHSpec G) (dhReal g) (dhRand g)
