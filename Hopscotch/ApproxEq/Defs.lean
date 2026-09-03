import Hopscotch.ComputationalIndistinguishability.AdversaryAdvantageDefs
import Hopscotch.Comp.FreeMDepth

/- # Approximate Equivalence -/

/-- Two oracle implementations are approximately equal up to advantage `ε` for
adversaries making at most `q_b` queries. -/
def ApproxEq
    {I : Type}
    {O : OracleSpec I}
    (q_b : ENat)
    (ε : NNReal)
    (o₁ o₂ : OracleImpl O) : Prop :=
  ∀ d : adversaryT O,
    FreeM.depth d ≤ q_b →
    |advantage d o₁ o₂| ≤ (ε : Real)
