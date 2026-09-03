import Hopscotch.ApproxEq.Defs
import Hopscotch.Comp.PMFExpectation

/- # The correct-until-bad technique -/

/-- Two stateful oracle kernels with the same state space agree until `bad` becomes true.
Bad states must be absorbing, their initial distributions must agree pointwise outside the
bad set, and their transition subdistributions must agree pointwise outside the bad set. -/
structure IsCorrectUntilBad
    {I S : Type} (O : OracleSpec I)
    (bad : S → Bool)
    (initial₁ initial₂ : PMF S)
    (queries₁ queries₂ : QueryImpl O (RState S)) : Prop where
  bad_absorbing₁ : ∀ i s, bad s = true →
    ∀ p ∈ (queries₁ i s).support, bad p.2 = true
  bad_absorbing₂ : ∀ i s, bad s = true →
    ∀ p ∈ (queries₂ i s).support, bad p.2 = true
  initial_eq_of_not_bad : ∀ s, bad s = false → initial₁ s = initial₂ s
  queries_eq_of_not_bad : ∀ i s, bad s = false →
    ∀ (out : O i) s', bad s' = false →
      queries₁ i s (out, s') = queries₂ i s (out, s')

/-- A Bellman-style upper bound on reaching `bad` within a given (possibly infinite)
number of further queries. -/
structure IsValidBadEventBound
    {I S : Type} (O : OracleSpec I)
    (bad : S → Bool)
    (queries : QueryImpl O (RState S))
    (bound : S → ENat → NNReal) : Prop where
  le_one : ∀ s q_b, bound s q_b ≤ 1
  eq_one_of_bad : ∀ s q_b, bad s = true → bound s q_b = 1
  preserved : ∀ i s q_b,
    PMF.expectation (queries i s) (fun p => (bound p.2 q_b : ENNReal)) ≤
      (bound s (q_b + 1) : ENNReal)

/-- Average a statewise bad-event bound over an initial-state distribution. -/
noncomputable def initialBadEventBound
    {S : Type} (initial : PMF S) (bound : S → ENat → NNReal) (q_b : ENat) : NNReal :=
  ∑' s, getPMF initial s * bound s q_b

/-- Correct-until-bad oracle implementations are approximately equal, with error bounded
by the expected initial value of a valid bad-event valuation for the first implementation.
The good subdistributions agree, so bounding the bad probability in either implementation
is sufficient. -/
theorem correctUntilBad_approxEq
    {I S : Type} {O : OracleSpec I}
    (bad : S → Bool)
    (initial₁ initial₂ : PMF S)
    (queries₁ queries₂ : QueryImpl O (RState S))
    (bound : S → ENat → NNReal)
    (hCorrect : IsCorrectUntilBad O bad initial₁ initial₂ queries₁ queries₂)
    (hBound₁ : IsValidBadEventBound O bad queries₁ bound)
    (q_b : ENat) :
    ApproxEq q_b (initialBadEventBound initial₁ bound q_b)
      ({ stateType := S, initialState := initial₁, queries := queries₁ } : OracleImpl O)
      ({ stateType := S, initialState := initial₂, queries := queries₂ } : OracleImpl O) := by
  sorry
