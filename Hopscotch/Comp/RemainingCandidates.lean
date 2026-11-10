import Hopscotch.Comp.PMFExpectation
import Hopscotch.Tactic.Normalization.PMF.Lemmas
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform sampling from remaining candidates

A nonempty candidate set represents values compatible with previous observations.
Observations restrict it to a fiber. The reconstruction lemmas preserve the joint
law of an observation and its hidden value; the budget lemmas bound adaptive
subset guesses and finite-valued observations.

This theory is independent of any encryption scheme.
-/

namespace Hopscotch.RemainingCandidates

abbrev Candidates (A : Type) := {s : Finset A // s.Nonempty}

noncomputable def budget (n m : Nat) : NNReal := min 1 ((n : NNReal) / m)

variable {A B : Type} [DecidableEq A] [DecidableEq B]

noncomputable def fiber (s : Candidates A) (f : A → B) (b : B) : Candidates A :=
  if h : (s.val.filter (fun a => f a = b)).Nonempty then
    ⟨s.val.filter (fun a => f a = b), h⟩ else s

end Hopscotch.RemainingCandidates

namespace Hopscotch.RemainingCandidates

/-! ## Finite-candidate probability lemmas -/

variable {A B : Type} [DecidableEq A] [DecidableEq B]

lemma card_pos {A : Type} (s : Candidates A) : 0 < s.val.card := s.property.card_pos

lemma budget_le_one (n m : Nat) : budget n m ≤ 1 := min_le_left _ _

lemma uniform_image_mass (s : Candidates A) (f : A → B) (b : B) :
    ((PMF.uniformOfFinset s.val s.property).map f) b =
      ((s.val.filter (fun a => f a = b)).card : ENNReal) / s.val.card := by
  classical
  have h : ((PMF.uniformOfFinset s.val s.property).map f) b =
      (PMF.uniformOfFinset s.val s.property).toOuterMeasure {a | f a = b} := by
    simp only [PMF.map_apply, PMF.toOuterMeasure_apply]
    apply tsum_congr
    intro a
    by_cases hb : b = f a <;> simp [Set.mem_setOf_eq, hb, eq_comm]
  rw [h]
  convert PMF.toOuterMeasure_uniformOfFinset_apply s.property {a | f a = b} using 1
  congr 2
  apply congrArg Finset.card
  ext a
  simp

lemma map_const_apply (p : PMF A) (b b' : B) (a : A) :
    (p.map (fun x => (b, x))) (b', a) = if b' = b then p a else 0 := by
  classical
  by_cases h : b' = b <;> simp [PMF.map_apply, Prod.mk.injEq, ite_and, h]

lemma map_second_apply (p : PMF A) (f : A → B) (b : B) (a : A) :
    (p.map (fun x => (f x, x))) (b, a) = if b = f a then p a else 0 := by
  classical
  simp [PMF.map_apply, Prod.mk.injEq, and_comm, ite_and]

/-- Observing an authentication value and reconstructing from its surviving
fiber preserves the joint law of the observation and the hidden share. -/
lemma fiber_reconstruct (s : Candidates A) (f : A → B) :
    (((PMF.uniformOfFinset s.val s.property).map f).bind fun b =>
      (PMF.uniformOfFinset (fiber s f b).val (fiber s f b).property).map
        (fun a => (b, a))) =
      (PMF.uniformOfFinset s.val s.property).map (fun a => (f a, a)) := by
  classical
  ext ⟨b, a⟩
  simp only [PMF.bind_apply, map_const_apply, map_second_apply, mul_ite, mul_zero,
    ]
  rw [tsum_eq_single b]
  swap
  · intro b' hb'
    simp [Ne.symm hb']
  simp only [ite_true]
  rw [uniform_image_mass]
  by_cases h : (s.val.filter (fun a => f a = b)).Nonempty
  · have hk0 : ((s.val.filter (fun a => f a = b)).card : ENNReal) ≠ 0 :=
      by exact_mod_cast (Nat.ne_of_gt h.card_pos)
    simp only [fiber, dif_pos h, PMF.uniformOfFinset_apply, Finset.mem_filter]
    by_cases ha : a ∈ s.val <;> by_cases hb : f a = b
    · simp only [ha, hb, and_self, ↓reduceIte]
      rw [div_eq_mul_inv, mul_right_comm,
        ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top _), one_mul]
    · simp [ha, hb, Ne.symm hb]
    · simp [ha, hb]
    · simp [ha, hb]
  · have hk : (s.val.filter (fun a => f a = b)).card = 0 :=
      by simpa [Finset.card_eq_zero] using h
    rw [hk]
    simp only [Nat.cast_zero]
    by_cases hb : b = f a
    · have ha : a ∉ s.val := fun ha =>
        h ⟨a, Finset.mem_filter.mpr ⟨ha, hb.symm⟩⟩
      simp [hb, PMF.uniformOfFinset_apply, ha]
    · simp [hb]


lemma weighted_budget_le (n m k : Nat) (hm : 0 < m) :
    ((k : NNReal) / m) * budget n k ≤ (n : NNReal) / m := by
  by_cases hk : k = 0
  · simp [hk]
  · have hm0 : (m : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    have hk0 : (k : NNReal) ≠ 0 := by exact_mod_cast hk
    calc
      ((k : NNReal) / m) * budget n k ≤ ((k : NNReal) / m) * ((n : NNReal) / k) :=
        mul_le_mul_right (min_le_right _ _) _
      _ = (n : NNReal) / m := by field_simp

/-- Revealing a value with at most |B| possible outcomes converts the expected
post-observation guessing budget to a pre-observation budget. Empty fibers have
zero probability, even though `fiber` uses a total default on them. -/
lemma observed_budget_le [Fintype B] (s : Candidates A) (f : A → B) (n : Nat) :
    ((PMF.uniformOfFinset s.val s.property).map f).expectation
      (fun b => (budget n (fiber s f b).val.card : ENNReal)) ≤
        (min 1 (((n : NNReal) * Fintype.card B) / s.val.card) : NNReal) := by
  classical
  let p := (PMF.uniformOfFinset s.val s.property).map f
  have hm0 : (s.val.card : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos s)
  have hone : p.expectation (fun b => (budget n (fiber s f b).val.card : ENNReal)) ≤ 1 := by
    calc
      _ ≤ p.expectation (fun _ => 1) := by
        apply ENNReal.tsum_le_tsum
        intro b
        exact mul_le_mul_right (ENNReal.coe_le_coe.mpr (budget_le_one _ _)) _
      _ = _ := PMF.expectation_const p 1
  have hlinear : p.expectation (fun b => (budget n (fiber s f b).val.card : ENNReal)) ≤
      (((n : NNReal) * Fintype.card B) / s.val.card : NNReal) := by
    calc
      p.expectation (fun b => (budget n (fiber s f b).val.card : ENNReal)) ≤
          ∑' _ : B, (((n : NNReal) / s.val.card : NNReal) : ENNReal) := by
        apply ENNReal.tsum_le_tsum
        intro b
        rw [show p b = _ from uniform_image_mass s f b]
        by_cases h : (s.val.filter (fun a => f a = b)).Nonempty
        · simp only [fiber, dif_pos h]
          have hn := ENNReal.coe_le_coe.mpr
            (weighted_budget_le n s.val.card (s.val.filter (fun a => f a = b)).card
              (card_pos s))
          simpa only [ENNReal.coe_mul, ENNReal.coe_div hm0, ENNReal.coe_natCast] using hn
        · have hz : (s.val.filter (fun a => f a = b)).card = 0 := by
            simpa [Finset.card_eq_zero] using h
          simp [hz]
      _ = (((n : NNReal) * Fintype.card B) / s.val.card : NNReal) := by
        simp [tsum_fintype, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  simpa only [ENNReal.coe_min, ENNReal.coe_one] using le_min hone hlinear

end Hopscotch.RemainingCandidates

namespace Hopscotch.RemainingCandidates

/-- A query may hit a whole subset of compatible keys. Its size is bounded
by `c`, and a miss removes precisely that subset. -/
lemma budget_subset_step (n m k c : Nat) (hm : 0 < m) (hkm : k ≤ m) (hkc : k ≤ c) :
    (k : NNReal) / m + ((m - k : Nat) : NNReal) / m * budget (n * c) (m - k) ≤
      budget ((n + 1) * c) m := by
  have hm0 : (m : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  apply le_min
  · calc
      _ ≤ (k : NNReal) / m + ((m - k : Nat) : NNReal) / m * 1 := by
        gcongr
        exact budget_le_one _ _
      _ = 1 := by
        have hs : (k : NNReal) + ((m - k : Nat) : NNReal) = m := by
          exact_mod_cast Nat.add_sub_of_le hkm
        rw [mul_one, ← add_div, hs, div_self hm0]
  · calc
      _ ≤ (k : NNReal) / m + ((n * c : Nat) : NNReal) / m :=
        add_le_add le_rfl (weighted_budget_le (n * c) m (m - k) hm)
      _ ≤ (c : NNReal) / m + ((n * c : Nat) : NNReal) / m := by
        gcongr
      _ = _ := by push_cast; rw [← add_div]; congr 1; ring

/-- Revealing one of `|B|` possible outcomes converts the pre-observation
candidate budget into the post-observation guessing budget. -/
lemma budget_challenge_step {A B : Type} [DecidableEq A] [DecidableEq B] [Fintype B]
    (s : Candidates A) (f : A → B) (n : Nat) :
    ((PMF.uniformOfFinset s.val s.property).map f).expectation
      (fun b => (budget n (fiber s f b).val.card : ENNReal)) ≤
        (budget ((n + 1) * Fintype.card B) s.val.card : ENNReal) := by
  calc
    _ ≤ (budget (n * Fintype.card B) s.val.card : ENNReal) := by
      simpa [budget] using observed_budget_le s f n
    _ ≤ _ := by
      apply ENNReal.coe_le_coe.mpr
      unfold budget
      gcongr
      exact_mod_cast Nat.le_succ n

lemma expectation_map {A B : Type} (p : PMF A) (f : A → B) (g : B → ENNReal) :
    (p.map f).expectation g = p.expectation (fun a => g (f a)) := by
  simp only [PMF.map_eq_bind_pure, PMF.expectation_bind, PMF.expectation_pure]

/-- Average the hit branch and the surviving-candidate branch of a subset test. -/
lemma subset_budget_expectation {A : Type} [DecidableEq A]
    (s : Candidates A) (hit : A → Bool) (n c : Nat)
    (hk : (s.val.filter (fun a => hit a = true)).card ≤ c) :
    (PMF.uniformOfFinset s.val s.property).expectation
      (fun a => if hit a then 1 else
        (budget (n * c) (s.val.filter (fun x => hit x = false)).card : ENNReal)) ≤
      (budget ((n + 1) * c) s.val.card : ENNReal) := by
  classical
  let k := (s.val.filter (fun a => hit a = true)).card
  let l := (s.val.filter (fun a => hit a = false)).card
  have hsum : k + l = s.val.card := by
    simpa [k, l, Bool.not_eq_true] using
      Finset.card_filter_add_card_filter_not (s := s.val) (fun a => hit a = true)
  have hk' : k ≤ s.val.card := Finset.card_filter_le _ _
  have hl : l = s.val.card - k := by omega
  have hm0 : (s.val.card : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos s)
  rw [← expectation_map (PMF.uniformOfFinset s.val s.property) hit
    (fun b => if b then 1 else (budget (n * c) l : ENNReal))]
  simp only [PMF.expectation, tsum_fintype, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte, mul_one, uniform_image_mass]
  change (k : ENNReal) / s.val.card +
    (l : ENNReal) / s.val.card * (budget (n * c) l : ENNReal) ≤ _
  have hnum := ENNReal.coe_le_coe.mpr
    (budget_subset_step n s.val.card k c (card_pos s) hk' hk)
  rw [← hl] at hnum
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_div hm0,
    ENNReal.coe_natCast, add_comm] using hnum

end Hopscotch.RemainingCandidates

namespace Hopscotch.RemainingCandidates

lemma expectation_le_on_support {A : Type} (p : PMF A) (f g : A → ENNReal)
    (h : ∀ a ∈ p.support, f a ≤ g a) : p.expectation f ≤ p.expectation g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_right (h a (by simpa only [PMF.mem_support_iff] using ha)) _

open scoped Classical in
lemma fiber_eq_of_partition {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (s : Candidates A) (f : A → B) (label : A → C)
    (h : ∀ a b, f a = f b ↔ label a = label b) (a : A) :
    fiber s f (f a) = fiber s label (label a) := by
  have hf : s.val.filter (fun b => f b = f a) =
      s.val.filter (fun b => label b = label a) := by
    ext b
    simp only [Finset.mem_filter, h]
  unfold fiber
  rw [hf]

open scoped Classical in
lemma fiber_val_of_mem {A B : Type} [DecidableEq A] [DecidableEq B]
    (s : Candidates A) (f : A → B) (a : A) (ha : a ∈ s.val) :
    (fiber s f (f a)).val = s.val.filter (fun b => f b = f a) := by
  have hf : (s.val.filter (fun b => f b = f a)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  simp only [fiber, dif_pos hf]

open scoped Classical in
lemma fiber_card_le_of_factor {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (s : Candidates A) (f : A → B) (label : A → C)
    (h : ∀ a b, label a = label b → f a = f b)
    (a : A) (ha : a ∈ s.val) :
    (fiber s label (label a)).val.card ≤ (fiber s f (f a)).val.card := by
  rw [fiber_val_of_mem s label a ha, fiber_val_of_mem s f a ha]
  apply Finset.card_le_card
  intro b hb
  rcases Finset.mem_filter.mp hb with ⟨hb, he⟩
  exact Finset.mem_filter.mpr ⟨hb, h b a he⟩

lemma budget_antitone (n m k : Nat) (hm : 0 < m) (h : m ≤ k) :
    budget n k ≤ budget n m := by
  unfold budget
  gcongr

open scoped Classical in
lemma fiber_const {A B : Type} [DecidableEq A] [DecidableEq B] (s : Candidates A) (f : A → B)
    (h : ∀ a b, f a = f b) (a : A) : fiber s f (f a) = s := by
  have hf : s.val.filter (fun b => f b = f a) = s.val := by
    ext b
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _
    exact h b a
  unfold fiber
  rw [hf]
  simp [s.property]

lemma budget_mono_n (n k m : Nat) (h : n ≤ k) : budget n m ≤ budget k m := by
  unfold budget
  gcongr

open scoped Classical in
/-- Conditioning on a good observation gives the same fiber for both kernels. -/
lemma fiber_lift_eq_of_good {A B S : Type} [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (s : Candidates A) (f g : A → B × S) (bad : S → Bool)
    (hbad : ∀ a, bad (f a).2 = bad (g a).2)
    (hagree : ∀ a, bad (f a).2 = false → f a = g a)
    (z : B × (S × Candidates A)) (hz : bad z.2.1 = false) :
    (((PMF.uniformOfFinset s.val s.property).map f).map
      (fun b => (b.1, (b.2, fiber s f b)))) z =
    (((PMF.uniformOfFinset s.val s.property).map g).map
      (fun b => (b.1, (b.2, fiber s g b)))) z := by
  have hpre (b : B × S) (hb : bad b.2 = false) (a : A) : f a = b ↔ g a = b := by
    constructor
    · intro ha
      have hf : bad (f a).2 = false := by rw [ha]; exact hb
      exact (hagree a hf).symm.trans ha
    · intro ha
      have hf : bad (f a).2 = false := (hbad a).trans (by rw [ha]; exact hb)
      exact (hagree a hf).trans ha
  have hfiber (b : B × S) (hb : bad b.2 = false) : fiber s f b = fiber s g b := by
    have hfilter : s.val.filter (fun a => f a = b) = s.val.filter (fun a => g a = b) := by
      ext a
      simp only [Finset.mem_filter, hpre b hb a]
    unfold fiber
    rw [hfilter]
  rw [PMF.map_comp, PMF.map_comp, PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  have hlift :
      (f a).1 = z.1 ∧ (f a).2 = z.2.1 ∧ fiber s f (f a) = z.2.2 ↔
      (g a).1 = z.1 ∧ (g a).2 = z.2.1 ∧ fiber s g (g a) = z.2.2 := by
    constructor
    · rintro ⟨ho, hs, hc⟩
      have hb : bad (f a).2 = false := hs ▸ hz
      rw [← hagree a hb, ← hfiber (f a) hb]
      exact ⟨ho, hs, hc⟩
    · rintro ⟨ho, hs, hc⟩
      have hb : bad (f a).2 = false := (hbad a).trans (hs ▸ hz)
      rw [hagree a hb, hfiber (g a) (hs ▸ hz)]
      exact ⟨ho, hs, hc⟩
  have heq : ((f a).1, ((f a).2, fiber s f (f a))) = z ↔
      ((g a).1, ((g a).2, fiber s g (g a))) = z := by
    simpa only [Prod.ext_iff] using hlift
  simp only [Function.comp_apply, eq_comm (a := z), heq]

end Hopscotch.RemainingCandidates
