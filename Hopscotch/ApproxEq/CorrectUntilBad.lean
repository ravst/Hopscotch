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

namespace CorrectUntilBad

/-! ### Auxiliary material for `correctUntilBad_approxEq`

The lemmas in this section are proof-internal helpers for the fundamental
"correct until bad" lemma proved below. -/

/-- Split a sum over an index type into its bad and its good part. -/
private lemma tsum_split_bad {A : Type*} (g : A → Bool) (f : A → ENNReal) :
    ∑' a, f a = (∑' a, if g a then f a else 0) + ∑' a, if g a then 0 else f a := by
  rw [← ENNReal.tsum_add]
  exact tsum_congr (fun a => by by_cases h : g a <;> simp [h])

/-- Two probability measures that agree on all good points also give the same
mass to the bad points. -/
private lemma badmass_eq {A : Type*} (μ₁ μ₂ : PMF A) (g : A → Bool)
    (hagree : ∀ a, g a = false → μ₁ a = μ₂ a) :
    (∑' a, if g a then μ₁ a else 0) = ∑' a, if g a then μ₂ a else 0 := by
  have h1 := tsum_split_bad g (fun a => μ₁ a)
  have h2 := tsum_split_bad g (fun a => μ₂ a)
  rw [PMF.tsum_coe] at h1 h2
  have hgood : (∑' a, if g a then (0 : ENNReal) else μ₁ a) = ∑' a, if g a then 0 else μ₂ a :=
    tsum_congr (fun a => by
      by_cases h : g a = true
      · simp [h]
      · simp [h, hagree a (by simpa using h)])
  rw [hgood] at h1
  have hne : (∑' a, if g a then (0 : ENNReal) else μ₂ a) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤) ?_
    calc (∑' a, if g a then (0 : ENNReal) else μ₂ a) ≤ ∑' a, μ₂ a :=
          ENNReal.tsum_le_tsum (fun a => by by_cases h : g a <;> simp [h])
      _ = 1 := PMF.tsum_coe μ₂
  have key : (∑' a, if g a then (0 : ENNReal) else μ₂ a) + (∑' a, if g a then μ₁ a else 0) =
      (∑' a, if g a then (0 : ENNReal) else μ₂ a) + ∑' a, if g a then μ₂ a else 0 := by
    rw [add_comm _ (∑' a, if g a then μ₁ a else 0), add_comm _ (∑' a, if g a then μ₂ a else 0),
      ← h1, ← h2]
  exact (ENNReal.add_right_inj hne).mp key

/-- A valuation that is `1` on all bad points has the same expectation under two
probability measures agreeing on the good points. -/
private lemma badexp_eq {A : Type*} (μ₁ μ₂ : PMF A) (g : A → Bool)
    (hagree : ∀ a, g a = false → μ₁ a = μ₂ a)
    (β : A → ENNReal) (hβ : ∀ a, g a = true → β a = 1) :
    (∑' a, μ₁ a * β a) = ∑' a, μ₂ a * β a := by
  rw [tsum_split_bad g (fun a => μ₁ a * β a), tsum_split_bad g (fun a => μ₂ a * β a)]
  congr 1
  · rw [show (∑' a, if g a then μ₁ a * β a else 0) = ∑' a, if g a then μ₁ a else 0 from
      tsum_congr (fun a => by by_cases h : g a = true <;> simp [h, hβ a])]
    rw [show (∑' a, if g a then μ₂ a * β a else 0) = ∑' a, if g a then μ₂ a else 0 from
      tsum_congr (fun a => by by_cases h : g a = true <;> simp [h, hβ a])]
    exact badmass_eq μ₁ μ₂ g hagree
  · exact tsum_congr (fun a => by
      by_cases h : g a = true
      · simp [h]
      · simp [h, hagree a (by simpa using h)])

/-- The one-step estimate: if two probability measures agree outside the bad set,
then the expectation of `f₁` under the first is bounded by the expectation of `f₂`
under the second plus the expected value of a valuation `β` that dominates the
pointwise error and equals `1` on bad points. -/
private lemma exp_le_of_agree {A : Type*} (μ₁ μ₂ : PMF A) (g : A → Bool)
    (hagree : ∀ a, g a = false → μ₁ a = μ₂ a)
    (f₁ f₂ β : A → ENNReal)
    (hf₁ : ∀ a, f₁ a ≤ 1) (hβ : ∀ a, g a = true → β a = 1)
    (hstep : ∀ a, f₁ a ≤ f₂ a + β a) :
    (∑' a, μ₁ a * f₁ a) ≤ (∑' a, μ₂ a * f₂ a) + ∑' a, μ₁ a * β a := by
  have hbad : (∑' a, if g a then μ₁ a * f₁ a else 0) ≤ ∑' a, if g a then μ₁ a * β a else 0 := by
    refine ENNReal.tsum_le_tsum (fun a => ?_)
    by_cases h : g a = true
    · simp only [h, if_true, hβ a h, mul_one]
      exact mul_le_of_le_one_right' (hf₁ a)
    · simp [h]
  have hgood : (∑' a, if g a then (0 : ENNReal) else μ₁ a * f₁ a) ≤
      (∑' a, μ₂ a * f₂ a) + ∑' a, if g a then (0 : ENNReal) else μ₁ a * β a := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun a => ?_)
    by_cases h : g a = true
    · simp [h]
    · have hμ := hagree a (by simpa using h)
      simp only [h, if_false, Bool.false_eq_true]
      rw [hμ, ← mul_add]
      gcongr
      exact hstep a
  rw [tsum_split_bad g (fun a => μ₁ a * f₁ a), tsum_split_bad g (fun a => μ₁ a * β a)]
  calc (∑' a, if g a then μ₁ a * f₁ a else 0) + (∑' a, if g a then (0 : ENNReal) else μ₁ a * f₁ a)
      ≤ (∑' a, if g a then μ₁ a * β a else 0) +
        ((∑' a, μ₂ a * f₂ a) + ∑' a, if g a then (0 : ENNReal) else μ₁ a * β a) :=
        add_le_add hbad hgood
    _ = _ := by ring

/-- Averaging a uniform pointwise estimate over a probability measure. -/
private lemma exp_le_of_uniform {A : Type*} (μ : PMF A) (f₁ f₂ : A → ENNReal) (B : ENNReal)
    (h : ∀ a, f₁ a ≤ f₂ a + B) :
    (∑' a, μ a * f₁ a) ≤ (∑' a, μ a * f₂ a) + B := by
  calc (∑' a, μ a * f₁ a) ≤ ∑' a, (μ a * f₂ a + μ a * B) :=
        ENNReal.tsum_le_tsum (fun a => by rw [← mul_add]; gcongr; exact h a)
    _ = (∑' a, μ a * f₂ a) + (∑' a, μ a) * B := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = (∑' a, μ a * f₂ a) + B := by rw [PMF.tsum_coe, one_mul]

/-- Peel off one unit of query budget in `ℕ∞`. -/
private lemma enat_pred {a q : ℕ∞} (h : 1 + a ≤ q) : ∃ q', q = q' + 1 ∧ a ≤ q' := by
  induction q with
  | top => exact ⟨⊤, by simp, le_top⟩
  | coe n =>
    have ha : a ≠ ⊤ := by
      intro h'; rw [h'] at h; simp at h
    lift a to ℕ using ha
    rw [show ((1 : ℕ∞) + (a : ℕ∞)) = ((1 + a : ℕ) : ℕ∞) by push_cast; ring, Nat.cast_le] at h
    refine ⟨((n - 1 : ℕ) : ℕ∞), ?_, ?_⟩
    · rw [show ((n - 1 : ℕ) : ℕ∞) + 1 = ((n - 1 + 1 : ℕ) : ℕ∞) by push_cast; ring]
      congr 1
      omega
    · rw [Nat.cast_le]; omega

/-- Push `simulateQ` through a `FreeM.roll` node. -/
private lemma simulateQ_roll' {ι} {spec : OracleSpec ι} (t : spec.Domain) {m} {β}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (k : spec.Range t → OracleComp spec β) :
    simulateQ impl (PFunctor.FreeM.roll t k) = impl t >>= fun u => simulateQ impl (k u) := by
  unfold simulateQ
  rw [PFunctor.FreeM.mapM.eq_def]; rfl

/-- The core induction behind the fundamental lemma: the probability of any bounded-depth
computation returning `true` differs by at most the bad-event bound between the two
implementations. -/
private lemma run_le {I S : Type} {O : OracleSpec I}
    (bad : S → Bool)
    (queries₁ queries₂ : QueryImpl O (RState S))
    (bound : S → ENat → NNReal)
    (hq : ∀ i s, bad s = false → ∀ (out : O i) (s' : S), bad s' = false →
      queries₁ i s (out, s') = queries₂ i s (out, s'))
    (hone : ∀ s q, bad s = true → bound s q = 1)
    (hpres : ∀ i s q, PMF.expectation (queries₁ i s) (fun p => (bound p.2 q : ENNReal)) ≤
      (bound s (q + 1) : ENNReal)) :
    ∀ (c : OracleComp (withPMFSpec O) Bool) (q : ENat) (s : S), FreeM.depth c ≤ q →
      (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) c s) true ≤
          PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) c s) true + (bound s q : ENNReal)) ∧
      (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) c s) true ≤
          PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) c s) true + (bound s q : ENNReal)) := by
  intro c
  induction c with
  | pure val =>
    intro q s _
    constructor <;> exact le_add_right (le_of_eq rfl)
  | roll t cont Hind =>
    cases t with
    | oracle i =>
      intro q s hb
      rw [FreeM.depth] at hb
      -- the trivial estimate available once the state is already bad
      have htriv : bad s = true →
          (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁)
              (PFunctor.FreeM.roll (withPMFI.oracle i) cont) s) true ≤
            PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂)
              (PFunctor.FreeM.roll (withPMFI.oracle i) cont) s) true + (bound s q : ENNReal)) ∧
          (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂)
              (PFunctor.FreeM.roll (withPMFI.oracle i) cont) s) true ≤
            PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁)
              (PFunctor.FreeM.roll (withPMFI.oracle i) cont) s) true + (bound s q : ENNReal)) := by
        intro hs
        rw [hone s q hs]
        constructor <;>
          exact le_trans (PMF.coe_le_one _ _) (by simp)
      by_cases hs : bad s = true
      · exact htriv hs
      have hsf : bad s = false := by simpa using hs
      obtain ⟨q', hq'eq, hq'le⟩ := enat_pred hb
      -- expand both runs into an expectation over the first query
      have hexpand : ∀ (queries : QueryImpl O (RState S)),
          PMF.map Prod.fst (simulateQ (addPMFtoImpl queries)
              (PFunctor.FreeM.roll (withPMFI.oracle i) cont) s) true =
            ∑' p : O i × S, queries i s p *
              PMF.map Prod.fst (simulateQ (addPMFtoImpl queries) (cont p.1) p.2) true := by
        intro queries
        simp only [simulateQ_roll', addPMFtoImpl]
        simp only [bind, StateT.bind, StateT.run]
        rw [PMF.map_bind, PMF.bind_apply]
        rfl
      have hIH : ∀ p : O i × S,
          (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) (cont p.1) p.2) true ≤
            PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) (cont p.1) p.2) true +
              (bound p.2 q' : ENNReal)) ∧
          (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) (cont p.1) p.2) true ≤
            PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) (cont p.1) p.2) true +
              (bound p.2 q' : ENNReal)) := by
        intro p
        refine Hind p.1 q' p.2 (le_trans (le_iSup (fun u => FreeM.depth (cont u)) p.1) hq'le)
      have hagree : ∀ p : O i × S, (fun p : O i × S => bad p.2) p = false →
          queries₁ i s p = queries₂ i s p := by
        rintro ⟨out, s'⟩ hp
        exact hq i s hsf out s' hp
      have hβ : ∀ p : O i × S, (fun p : O i × S => bad p.2) p = true →
          ((bound p.2 q' : ENNReal)) = 1 := by
        intro p hp
        rw [hone p.2 q' hp]; simp
      have hpres' : (∑' p : O i × S, queries₁ i s p * (bound p.2 q' : ENNReal)) ≤
          (bound s q : ENNReal) := by
        have := hpres i s q'
        rw [PMF.expectation_eq_tsum] at this
        rw [hq'eq]
        exact this
      rw [hexpand queries₁, hexpand queries₂]
      constructor
      · refine le_trans (exp_le_of_agree (queries₁ i s) (queries₂ i s)
          (fun p => bad p.2) hagree _ _ (fun p => (bound p.2 q' : ENNReal))
          (fun p => PMF.coe_le_one _ _) hβ (fun p => (hIH p).1)) ?_
        exact add_le_add le_rfl hpres'
      · have hswap : (∑' p : O i × S, queries₂ i s p * (bound p.2 q' : ENNReal)) =
            ∑' p : O i × S, queries₁ i s p * (bound p.2 q' : ENNReal) :=
          badexp_eq _ _ (fun p => bad p.2) (fun p hp => (hagree p hp).symm) _ hβ
        refine le_trans (exp_le_of_agree (queries₂ i s) (queries₁ i s)
          (fun p => bad p.2) (fun p hp => (hagree p hp).symm) _ _
          (fun p => (bound p.2 q' : ENNReal))
          (fun p => PMF.coe_le_one _ _) hβ (fun p => (hIH p).2)) ?_
        rw [hswap]
        exact add_le_add le_rfl hpres'
    | sample p =>
      intro q s hb
      rw [FreeM.depth] at hb
      have hexpand : ∀ (queries : QueryImpl O (RState S)),
          PMF.map Prod.fst (simulateQ (addPMFtoImpl queries)
              (PFunctor.FreeM.roll (withPMFI.sample p) cont) s) true =
            ∑' a, p a *
              PMF.map Prod.fst (simulateQ (addPMFtoImpl queries) (cont a) s) true := by
        intro queries
        simp only [simulateQ_roll', addPMFtoImpl]
        simp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind,
          StateT.run]
        simp only [PMF.bind_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.map_bind]
        rw [PMF.bind_apply]
        rfl
      have hIH : ∀ a,
          (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) (cont a) s) true ≤
            PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) (cont a) s) true +
              (bound s q : ENNReal)) ∧
          (PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) (cont a) s) true ≤
            PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) (cont a) s) true +
              (bound s q : ENNReal)) := by
        intro a
        refine Hind a q s (le_trans ?_ hb)
        exact le_trans (le_iSup (fun u => FreeM.depth (cont u)) a) le_add_self
      rw [hexpand queries₁, hexpand queries₂]
      exact ⟨exp_le_of_uniform p _ _ _ (fun a => (hIH a).1),
        exp_le_of_uniform p _ _ _ (fun a => (hIH a).2)⟩

end CorrectUntilBad

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
  intro d hdepth
  -- probability that the distinguisher outputs `true`, starting from state `s`
  set F₁ : S → ENNReal :=
    fun s => PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₁) d s) true with hF₁
  set F₂ : S → ENNReal :=
    fun s => PMF.map Prod.fst (simulateQ (addPMFtoImpl queries₂) d s) true with hF₂
  have hstep := CorrectUntilBad.run_le bad queries₁ queries₂ bound
    hCorrect.queries_eq_of_not_bad hBound₁.eq_one_of_bad hBound₁.preserved d q_b
  -- the two runs, expanded as expectations over the initial state
  have hrun : ∀ (initial : PMF S) (queries : QueryImpl O (RState S)),
      runDistinguisher d ({ stateType := S, initialState := initial, queries := queries } :
          OracleImpl O) true =
        ∑' s, initial s *
          PMF.map Prod.fst (simulateQ (addPMFtoImpl queries) d s) true := by
    intro initial queries
    simp only [runDistinguisher, PMF.monad_bind_eq_bind]
    rw [PMF.bind_apply]
  have hβ : ∀ s, bad s = true → ((bound s q_b : ENNReal)) = 1 := by
    intro s hs
    rw [hBound₁.eq_one_of_bad s q_b hs]; simp
  have h1 : (∑' s, initial₁ s * F₁ s) ≤ (∑' s, initial₂ s * F₂ s) +
      ∑' s, initial₁ s * (bound s q_b : ENNReal) :=
    CorrectUntilBad.exp_le_of_agree initial₁ initial₂ bad hCorrect.initial_eq_of_not_bad
      F₁ F₂ (fun s => (bound s q_b : ENNReal)) (fun s => PMF.coe_le_one _ _) hβ
      (fun s => (hstep s hdepth).1)
  have h2 : (∑' s, initial₂ s * F₂ s) ≤ (∑' s, initial₁ s * F₁ s) +
      ∑' s, initial₁ s * (bound s q_b : ENNReal) := by
    have hswap : (∑' s, initial₂ s * (bound s q_b : ENNReal)) =
        ∑' s, initial₁ s * (bound s q_b : ENNReal) :=
      CorrectUntilBad.badexp_eq _ _ bad
        (fun s hs => (hCorrect.initial_eq_of_not_bad s hs).symm) _ hβ
    have := CorrectUntilBad.exp_le_of_agree initial₂ initial₁ bad
      (fun s hs => (hCorrect.initial_eq_of_not_bad s hs).symm)
      F₂ F₁ (fun s => (bound s q_b : ENNReal)) (fun s => PMF.coe_le_one _ _) hβ
      (fun s => (hstep s hdepth).2)
    rwa [hswap] at this
  -- the error term, as an `ENNReal`
  have hsummable : Summable (fun s => getPMF initial₁ s * bound s q_b) := by
    refine NNReal.summable_of_le (fun s => ?_) (f := fun s => getPMF initial₁ s) ?_
    · exact mul_le_of_le_one_right (zero_le _) (hBound₁.le_one s q_b)
    · rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      rw [show (∑' s, ((getPMF initial₁ s : NNReal) : ENNReal)) = ∑' s, initial₁ s from
        tsum_congr (fun s => pmf_non_inf initial₁ s)]
      rw [PMF.tsum_coe]
      simp
  have herror : ((initialBadEventBound initial₁ bound q_b : NNReal) : ENNReal) =
      ∑' s, initial₁ s * (bound s q_b : ENNReal) := by
    rw [initialBadEventBound, ENNReal.coe_tsum hsummable]
    exact tsum_congr (fun s => by rw [ENNReal.coe_mul, pmf_non_inf initial₁ s])
  -- transfer the two `ENNReal` estimates to the real-valued advantage
  have hne₁ : (∑' s, initial₁ s * F₁ s) ≠ ⊤ := by
    rw [← hrun initial₁ queries₁]
    exact PMF.apply_ne_top _ _
  have hne₂ : (∑' s, initial₂ s * F₂ s) ≠ ⊤ := by
    rw [← hrun initial₂ queries₂]
    exact PMF.apply_ne_top _ _
  have htoreal : ∀ (x y : ENNReal) (hx : x ≠ ⊤) (hy : y ≠ ⊤),
      x ≤ y + ((initialBadEventBound initial₁ bound q_b : NNReal) : ENNReal) →
      x.toReal ≤ y.toReal + (initialBadEventBound initial₁ bound q_b : Real) := by
    intro x y hx hy hxy
    have := ENNReal.toReal_mono (by simp [hy]) hxy
    rwa [ENNReal.toReal_add hy (by simp), ENNReal.coe_toReal] at this
  rw [herror] at htoreal
  have hR₁ := htoreal _ _ hne₁ hne₂ h1
  have hR₂ := htoreal _ _ hne₂ hne₁ h2
  rw [← hrun initial₁ queries₁, ← hrun initial₂ queries₂] at hR₁ hR₂
  change |(getPMF (runDistinguisher d _) True : Real) - (getPMF (runDistinguisher d _) True)| ≤ _
  simp only [getPMF, decide_true, ENNReal.coe_toNNReal_eq_toReal]
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩
