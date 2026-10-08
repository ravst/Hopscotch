import Hopscotch.ApproxEq.CorrectUntilBad

/-!
# The absorbing failure process used by the Cramer--Shoup rejection bridge

The data state holds the information needed to answer queries. Only its Boolean
failure component enters the Bellman valuation. The secret key is reconstructed
by a probabilistic abstraction, rather than fixed in this valuation's state.

This is an instance of the existing correct-until-bad theorem, not a new
simulation rule. Connecting it to the concrete games is a separate obligation.
-/

namespace Hopscotch.CramerShoup

/-- Failure probability after `n` independent opportunities of rate `p`. -/
noncomputable def failureProbability (p : NNReal) : Nat → NNReal
  | 0 => 0
  | n + 1 => p + (1 - p) * failureProbability p n

lemma failureProbability_le_one (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    failureProbability p n ≤ 1 := by
  induction n with
  | zero => simp [failureProbability]
  | succ n ih =>
      calc
        failureProbability p (n + 1) = p + (1 - p) * failureProbability p n := rfl
        _ ≤ p + (1 - p) * 1 := by gcongr
        _ = 1 := by rw [mul_one, add_comm, tsub_add_cancel_of_le hp]

lemma failureProbability_add_survival (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    failureProbability p n + (1 - p) ^ n = 1 := by
  induction n with
  | zero => simp [failureProbability]
  | succ n ih =>
      calc
        failureProbability p (n + 1) + (1 - p) ^ (n + 1) =
            p + (1 - p) * (failureProbability p n + (1 - p) ^ n) := by
          rw [failureProbability, pow_succ]
          ring
        _ = p + (1 - p) * 1 := by rw [ih]
        _ = 1 := by rw [mul_one, add_comm, tsub_add_cancel_of_le hp]

/-- The usual geometric failure bound, expressed without a new probability rule. -/
lemma failureProbability_eq (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    failureProbability p n = 1 - (1 - p) ^ n := by
  have h := failureProbability_add_survival p hp n
  calc
    failureProbability p n = failureProbability p n + (1 - p) ^ n - (1 - p) ^ n :=
      (add_tsub_cancel_right _ _).symm
    _ = 1 - (1 - p) ^ n := by rw [h]

lemma failureProbability_le_linear (p : NNReal) (n : Nat) :
    failureProbability p n ≤ n * p := by
  induction n with
  | zero => simp [failureProbability]
  | succ n ih =>
      calc
        failureProbability p (n + 1) = p + (1 - p) * failureProbability p n := rfl
        _ ≤ p + failureProbability p n := by
          gcongr
          exact mul_le_of_le_one_left (zero_le _) (tsub_le_self : 1 - p ≤ 1)
        _ ≤ p + n * p := add_le_add le_rfl ih
        _ = ((n + 1 : Nat) : NNReal) * p := by push_cast; ring

/-- Error budget for the absorbing process, including an unlimited budget. -/
noncomputable def failureBudget (p : NNReal) : ENat → NNReal
  | none => 1
  | some n => failureProbability p n

/-- The failed state has value one. An unlimited query budget also has value one. -/
noncomputable def failureValuation (p : NNReal) {A : Type} (st : A × Bool) : ENat → NNReal
  | none => 1
  | some n => if st.2 then 1 else failureProbability p n

/-- While good, toss a failure coin and use the common good transition on
its good branch. Once failed, always use the failure continuation. Both
continuations still answer the oracle's queries. -/
noncomputable def failureQueries {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1)
    (good failed : QueryImpl O (RState A)) : QueryImpl O (RState (A × Bool)) :=
  fun i st => do
    let b ← if st.2 then PMF.pure true else PMF.bernoulli p hp
    let out ← (if b then failed else good) i st.1
    pure (out.1, (out.2, b))

noncomputable def failureOracle {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failed : QueryImpl O (RState A)) : OracleImpl O where
  stateType := A × Bool
  initialState := initial.map (fun a => (a, false))
  queries := failureQueries p hp good failed

/-- Failure is absorbing, independently of the failure continuation. -/
lemma failureQueries_absorbing {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (good failed : QueryImpl O (RState A))
    (i : I) (st : A × Bool) (h : st.2 = true) :
    ∀ out ∈ (failureQueries p hp good failed i st).support, out.2.2 = true := by
  intro out hout
  simp only [failureQueries, h, ↓reduceIte, sPMF] at hout
  change out ∈ ((failed i st.1).map (fun x => (x.1, (x.2, true)))).support at hout
  rw [PMF.support_map] at hout
  obtain ⟨x, hx, rfl⟩ := hout
  rfl

/-- Changing the failure continuation changes no good subdistribution. -/
lemma failureOracles_correctUntilBad {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failed₁ failed₂ : QueryImpl O (RState A)) :
    IsCorrectUntilBad O Prod.snd
      (failureOracle p hp initial good failed₁).initialState
      (failureOracle p hp initial good failed₂).initialState
      (failureOracle p hp initial good failed₁).queries
      (failureOracle p hp initial good failed₂).queries := by
  constructor
  · exact failureQueries_absorbing p hp good failed₁
  · exact failureQueries_absorbing p hp good failed₂
  · intro st hst
    rfl
  · intro i st hst out st' hst'
    rcases st with ⟨a, b⟩
    rcases st' with ⟨a', b'⟩
    dsimp at hst hst'
    subst b
    subst b'
    simp only [failureOracle, failureQueries, Bool.false_eq_true, ↓reduceIte, sPMF]
    simp [PMF.monad_bind_eq_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_bool,
      PMF.pure_apply, Prod.mk.injEq, eq_comm]

/-- The data transition does not affect expectations of the failure status. -/
lemma failureQueries_expectation {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (good failed : QueryImpl O (RState A))
    (i : I) (st : A × Bool) (f : Bool → ENNReal) :
    (failureQueries p hp good failed i st).expectation (fun out => f out.2.2) =
      (if st.2 then PMF.pure true else PMF.bernoulli p hp).expectation f := by
  cases h : st.2 <;>
    simp only [failureQueries, h, Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind]
  all_goals
    rw [PMF.expectation_bind]
    congr 1
    funext b
    rw [PMF.expectation_bind]
    simp [PMF.expectation_pure, PMF.expectation_const]

/-- Bellman reasoning is performed on the simple process, never on a
concrete state containing a fixed secret key. -/
lemma failureOracle_bound {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failed : QueryImpl O (RState A)) :
    IsValidBadEventBound O Prod.snd
      (failureOracle p hp initial good failed).queries (failureValuation p) := by
  constructor
  · intro st q
    cases q with
    | top => simp [failureValuation]
    | coe n =>
      cases h : st.2 <;> simp [failureValuation, h, failureProbability_le_one p hp n]
  · intro st q h
    cases q <;> simp [failureValuation, h]
  · intro i st q
    cases q with
    | top => simp [failureValuation, PMF.expectation_const]
    | coe n =>
      have hsucc : failureValuation p st ((n : ENat) + 1) =
          (if st.2 then 1 else failureProbability p (n + 1)) := by
        rw [← ENat.coe_one, ← ENat.coe_add]
        rfl
      rw [hsucc]
      simp only [failureOracle]
      have hfun : (fun out : O i × (A × Bool) =>
          (failureValuation p out.2 (n : ENat) : ENNReal)) =
          (fun out => if out.2.2 then 1 else (failureProbability p n : ENNReal)) := by
        funext out
        cases h : out.2.2 <;> simp [failureValuation, h]
      rw [hfun, failureQueries_expectation p hp good failed i st
        (fun b => if b then 1 else (failureProbability p n : ENNReal))]
      cases h : st.2 <;>
        simp [h, PMF.expectation, tsum_fintype, Fintype.sum_bool, PMF.bernoulli_apply,
          failureProbability, ENNReal.coe_add, ENNReal.coe_mul]

lemma failureOracle_initialBound {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failed : QueryImpl O (RState A)) (q : ENat) :
    initialBadEventBound (failureOracle p hp initial good failed).initialState
      (failureValuation p) q = failureBudget p q := by
  apply initialBadEventBound_constant_on_support
  intro st hst
  have hs := hst
  simp only [failureOracle, PMF.support_map] at hs
  obtain ⟨a, ha, rfl⟩ := hs
  cases q <;> rfl

/-- The existing error theorem gives the simple-oracle hop with its
explicit finite-budget error. -/
lemma failureOracles_approxEq {I A : Type} {O : OracleSpec I}
    (p : NNReal) (hp : p ≤ 1) (initial : PMF A)
    (good failed₁ failed₂ : QueryImpl O (RState A)) (q : ENat) :
    ApproxEq q (failureBudget p q)
      (failureOracle p hp initial good failed₁)
      (failureOracle p hp initial good failed₂) := by
  have h := correctUntilBad_approxEq Prod.snd _ _ _ _ (failureValuation p)
    (failureOracles_correctUntilBad p hp initial good failed₁ failed₂)
    (failureOracle_bound p hp initial good failed₁) q
  rwa [failureOracle_initialBound] at h

end Hopscotch.CramerShoup
