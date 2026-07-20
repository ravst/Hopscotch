import Mathlib

-- set_option maxHeartbeats 400000

/-!
# PMF disintegration helpers and a generic oracle-reconstruction lemma

This file is deliberately **Mathlib-only** (no VCVio dependency).  It packages the
probability-theoretic core needed to prove `rState2Rstate_non_dist` in `ObsEqComp.lean`:

* `PMF.condOn` / `PMF.map_bind_condOn_fiber` : disintegration (law of total probability).
* `GTree` : a generic model of an adaptive oracle computation (oracle queries + sampling).
* `geval` : running a `GTree` against a generic stateful kernel.
* `geval_reconstruct` : if a "reconstructed" oracle `ostep` together with a conditional-state
  map `cs` satisfies the one-step compatibility `HSTEP`, then running any bounded-depth
  computation against the original kernel and against the reconstruction give the same
  output distribution.
-/

open PMF

open Classical in
/-- Total (defaulted) conditioning of a `PMF` on a set: condition on `s` when it has positive
mass, otherwise return the distribution unchanged. -/
noncomputable def PMF.condOn {α : Type _} (d : PMF α) (s : Set α) : PMF α :=
  if h : ∃ a ∈ s, a ∈ d.support then d.filter s h else d

/-- Disintegration / law of total probability: sampling `x ~ d` is the same as first sampling
the value `b = g x` from the pushforward `d.map g`, then resampling `x` from `d` conditioned on
the fibre `{a | g a = b}`. -/
lemma PMF.map_bind_condOn_fiber {α β : Type _} (d : PMF α) (g : α → β) :
    (d.map g).bind (fun b => d.condOn {a | g a = b}) = d := by
  classical
  ext a
  simp only [PMF.bind_apply, PMF.map_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite (g a)]
  have memfib : ∀ (a' : α) (b : β), a' ∈ {a_1 | g a_1 = b} ↔ g a' = b := by
    intro a' b; simp [Set.mem_setOf_eq]
  have hother : (∑' (b : β), if b = g a then 0 else
      (∑' (a' : α), if b = g a' then d a' else 0) * (d.condOn {a_1 | g a_1 = b}) a) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    split_ifs with hb
    · rfl
    · by_cases hsup : ∃ a' ∈ {a_1 | g a_1 = b}, a' ∈ d.support
      · have hc : (d.condOn {a_1 | g a_1 = b}) a = 0 := by
          unfold PMF.condOn
          rw [dif_pos hsup, PMF.filter_apply]
          have hanin : a ∉ {a_1 | g a_1 = b} := by rw [memfib]; intro h; exact hb h.symm
          rw [Set.indicator_of_notMem hanin]; ring
        rw [hc, mul_zero]
      · have hz : (∑' (a' : α), if b = g a' then d a' else 0) = 0 := by
          apply ENNReal.tsum_eq_zero.mpr
          intro a'
          split_ifs with hga'
          · by_contra hne
            exact hsup ⟨a', (memfib a' b).mpr hga'.symm, by simp [PMF.mem_support_iff, hne]⟩
          · rfl
        rw [hz, zero_mul]
  rw [hother, add_zero]
  by_cases hda : d a = 0
  · by_cases hsup : ∃ a' ∈ {a_1 | g a_1 = g a}, a' ∈ d.support
    · unfold PMF.condOn
      rw [dif_pos hsup, PMF.filter_apply]
      simp [Set.indicator, hda]
    · unfold PMF.condOn
      rw [dif_neg hsup, hda]
      simp
  · have hsup : ∃ a' ∈ {a_1 | g a_1 = g a}, a' ∈ d.support :=
      ⟨a, (memfib a (g a)).mpr rfl, by simp [PMF.mem_support_iff, hda]⟩
    unfold PMF.condOn
    rw [dif_pos hsup, PMF.filter_apply]
    have hain : a ∈ {a_1 | g a_1 = g a} := (memfib a (g a)).mpr rfl
    rw [Set.indicator_of_mem hain]
    have hind : ∀ a', Set.indicator {a_1 | g a_1 = g a} (⇑d) a' = if g a = g a' then d a' else 0 := by
      intro a'
      by_cases h : g a' = g a
      · rw [Set.indicator_of_mem ((memfib a' (g a)).mpr h)]; simp [h, eq_comm]
      · rw [Set.indicator_of_notMem (by rw [memfib]; exact h)]; simp [Ne.symm h, h]
    simp only [hind]
    set Z := ∑' (a' : α), if g a = g a' then d a' else 0 with hZ
    have hZne : Z ≠ 0 := by
      rw [hZ]; intro hc
      have := ENNReal.tsum_eq_zero.mp hc a
      simp at this; exact hda this
    have hZfin : Z ≠ ⊤ := by
      have hle : Z ≤ 1 := by
        rw [hZ, ← PMF.tsum_coe d]; apply ENNReal.tsum_le_tsum; intro a'; split_ifs <;> simp
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    rw [mul_comm (d a) Z⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hZne hZfin, one_mul]

/-- Conditioning on a set that contains the whole support is the identity. -/
lemma PMF.condOn_eq_self {α : Type _} (d : PMF α) (s : Set α) (hsub : ∀ a ∈ d.support, a ∈ s) :
    d.condOn s = d := by
  classical
  have hind : ∀ a, Set.indicator s (⇑d) a = d a := by
    intro a
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha]
      have : d a = 0 := by
        by_contra hne
        exact ha (hsub a ((PMF.mem_support_iff d a).mpr hne))
      rw [this]
  have hsum : (∑' a, Set.indicator s (⇑d) a) = 1 := by
    simp only [hind]; exact PMF.tsum_coe d
  have hex : ∃ a ∈ s, a ∈ d.support := by
    obtain ⟨a, ha⟩ := PMF.support_nonempty d
    exact ⟨a, hsub a ha, ha⟩
  unfold PMF.condOn
  rw [dif_pos hex]
  ext a
  rw [PMF.filter_apply, hind, hsum, inv_one, mul_one]

/-- Pointwise congruence for `PMF.bind` on the support of the first argument. -/
lemma PMF.bindCongrOnSupport {α β : Type _} (x : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ x.support, f a = g a) : x.bind f = x.bind g := by
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  ext1 a
  ext1 ha
  exact h a ha

/-
Iterated conditioning is conditioning on the intersection (when the intersection still has
positive mass).
-/
lemma PMF.condOn_condOn {α : Type _} (d : PMF α) (s t : Set α)
    (h : ∃ a, a ∈ s ∧ a ∈ t ∧ a ∈ d.support) :
    (d.condOn s).condOn t = d.condOn (s ∩ t) := by
      have h_filter_s : d.condOn s = d.filter s (by
      exact ⟨ h.choose, h.choose_spec.1, h.choose_spec.2.2 ⟩) := by
        unfold PMF.condOn; aesop;
      generalize_proofs at *;
      -- Similarly, show that `d.filter s` has positive `t`-mass, so `(d.filter s).condOn t = (d.filter s).filter t _`.
      have h_filter_st : (d.filter s ‹_›).condOn t = (d.filter s ‹_›).filter t (by
      obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := h; use a; aesop;) := by
        unfold PMF.condOn; aesop;
      generalize_proofs at *;
      rw [ h_filter_s, h_filter_st, show d.condOn ( s ∩ t ) = d.filter ( s ∩ t ) ( by
                                      grind ) from ?_ ]
      · generalize_proofs at *;
        ext a;
        have h_normalization : (∑' a', (s ∩ t).indicator d a') = (∑' a', t.indicator (d.filter s ‹_›) a') * (∑' a', s.indicator d a') := by
          rw [ ← ENNReal.tsum_mul_right ];
          congr with a' ; by_cases ha' : a' ∈ s <;> by_cases ha'' : a' ∈ t <;> simp +decide [ ha', ha'' ];
          by_cases h : ∑' a', s.indicator d a' = 0 <;> simp_all +decide [ mul_assoc ];
          rw [ ENNReal.inv_mul_cancel ] <;> aesop;
        by_cases h : ∑' a', t.indicator ( d.filter s ‹_› ) a' = 0 <;> by_cases h' : ∑' a', s.indicator d a' = 0 <;> simp_all +decide [ ENNReal.mul_inv, ENNReal.inv_mul_cancel ];
        · grind;
        · exact False.elim ( h.choose_spec.2.2 ( h_normalization _ h.choose_spec.1 h.choose_spec.2.1 ) );
        · by_cases ha : a ∈ s <;> by_cases hb : a ∈ t <;> simp_all +decide [ Set.indicator_apply ];
          ring;
      · unfold PMF.condOn; aesop;

/-
Conditioning a bind on a downstream event that is determined by the upstream sample: if for
every `a` and every `b` in the support of `g a`, membership `b ∈ s` is equivalent to `a ∈ ψ`,
then conditioning `d.bind g` on `s` is the same as conditioning `d` on `ψ` first.
-/
lemma PMF.condOn_bind_of_upstream {α β : Type _} (d : PMF α) (g : α → PMF β) (s : Set β)
    (ψ : Set α) (hcompat : ∀ a, ∀ b ∈ (g a).support, (b ∈ s ↔ a ∈ ψ)) :
    (d.bind g).condOn s = (d.condOn ψ).bind g := by
      unfold PMF.condOn;
      split_ifs <;> simp_all +decide [ Set.indicator_apply, PMF.filter_apply ];
      · -- By definition of bind, we can rewrite the right-hand side as the sum over y of (d.filter ψ h✝) y * g y b.
        ext b; simp [PMF.bind_apply, PMF.filter_apply];
        by_cases hb : b ∈ s <;> simp +decide [ hb, Set.indicator_apply ];
        · rw [ ← ENNReal.tsum_mul_right ];
          congr with a ; by_cases ha : a ∈ ψ <;> simp +decide [ ha, hb, Set.indicator_apply ];
          · rw [ show ( ∑' a', s.indicator ( ⇑ ( d.bind g ) ) a' ) = ( ∑' a', ψ.indicator ( ⇑d ) a' ) from ?_ ]
            · ring
            have h_sum_eq : ∑' a', s.indicator (⇑(d.bind g)) a' = ∑' a', ∑' a'', ψ.indicator (⇑d) a'' * (g a'') a' := by
              apply tsum_congr
              intro a'
              by_cases ha' : a' ∈ s <;> simp +decide [ ha', Set.indicator_apply ];
              · congr with a'' ; by_cases ha'' : a'' ∈ ψ <;> simp +decide [ ha'', Set.indicator_apply ];
                exact Or.inr ( Classical.not_not.1 fun h => ha'' <| hcompat a'' a' h |>.1 ha' );
              · rw [ tsum_eq_single a ] <;> simp_all +decide [ Set.indicator_apply ];
                · exact Or.inr ( Classical.not_not.1 fun h => ha' <| hcompat a a' h |>.2 ha );
                · grind;
            rw [ h_sum_eq, ENNReal.tsum_comm ];
            simp +decide [ ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, PMF.tsum_coe ];
          · exact Or.inl <| Or.inr <| Classical.not_not.1 fun h => ha <| hcompat a b h |>.1 hb;
        · rw [ tsum_eq_single ( Classical.choose ‹∃ a ∈ ψ, a ∈ d.support› ) ] <;> simp_all +decide [ Set.indicator_apply ]; all_goals grind;
      · next Z =>
        obtain ⟨ b, ha₁, ha₂ ⟩ := ‹∃ a ∈ s, a ∈ ( d.bind g ).support›; simp_all +decide [ PMF.mem_support_iff ] ;
        exfalso
        have ⟨i, ⟨Hi1, Hi2⟩⟩ := ha₂
        rw [hcompat i b Hi2] at ha₁
        apply Hi1
        apply Z
        assumption
        -- grind +ring;
      · obtain ⟨ a, ha, ha' ⟩ := ‹∃ a ∈ ψ, a ∈ d.support›; specialize hcompat a; simp_all +decide [ PMF.mem_support_iff ] ;
        rename_i h₁ h₂; specialize h₂
        have := PMF.support_nonempty ( g a )
        obtain ⟨ b, hb ⟩ := this
        specialize h₂ b ( hcompat b ( by
          exact (mem_support_iff (g a) b).mp hb
        ) ) a ha'
        exfalso
        have X : (g a) b ≠ 0 := by
          exact (mem_support_iff (g a) b).mp hb
        apply X
        assumption

/-- Conditioning a pushforward equals pushing forward the conditioning along the preimage. -/
lemma PMF.condOn_map {α β : Type _} (d : PMF α) (g : α → β) (s : Set β) :
    (d.map g).condOn s = (d.condOn (g ⁻¹' s)).map g := by
  have hmap : ∀ (e : PMF α), e.map g = e.bind (fun a => PMF.pure (g a)) := by
    intro e; rw [PMF.map]; rfl
  rw [hmap d, PMF.condOn_bind_of_upstream d (fun a => PMF.pure (g a)) s (g ⁻¹' s) ?compat, ← hmap]
  case compat =>
    intro a b hb
    rw [PMF.mem_support_iff] at hb
    have hbga : b = g a := by
      by_contra hne
      rw [PMF.pure_apply, if_neg hne] at hb
      exact hb rfl
    subst hbga
    simp [Set.mem_preimage]

/-- `PMF.map` only depends on the values of the function on the support. -/
lemma PMF.map_congr_on_support {α β : Type _} (d : PMF α) {f g : α → β}
    (h : ∀ a ∈ d.support, f a = g a) : d.map f = d.map g := by
  rw [show d.map f = d.bind (fun a => PMF.pure (f a)) from by rw [PMF.map]; rfl,
      show d.map g = d.bind (fun a => PMF.pure (g a)) from by rw [PMF.map]; rfl]
  exact PMF.bindCongrOnSupport d (fun a ha => by rw [h a ha])

/-- Conditioning only depends on the set's intersection with the support. -/
lemma PMF.condOn_congr_on_support {α : Type _} (d : PMF α) (s t : Set α)
    (h : ∀ a ∈ d.support, a ∈ s ↔ a ∈ t) : d.condOn s = d.condOn t := by
  classical
  have hind : Set.indicator s (⇑d) = Set.indicator t (⇑d) := by
    funext a
    by_cases ha : a ∈ d.support
    · by_cases hs : a ∈ s
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((h a ha).mp hs)]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun ht => hs ((h a ha).mpr ht))]
    · rw [PMF.mem_support_iff, not_not] at ha
      simp [Set.indicator_apply, ha]
  have hex : (∃ a ∈ s, a ∈ d.support) ↔ (∃ a ∈ t, a ∈ d.support) := by
    constructor
    · rintro ⟨a, ha, ha2⟩; exact ⟨a, (h a ha2).mp ha, ha2⟩
    · rintro ⟨a, ha, ha2⟩; exact ⟨a, (h a ha2).mpr ha, ha2⟩
  unfold PMF.condOn
  by_cases hh : ∃ a ∈ s, a ∈ d.support
  · rw [dif_pos hh, dif_pos (hex.mp hh)]
    ext a; rw [PMF.filter_apply, PMF.filter_apply, hind]
  · rw [dif_neg hh, dif_neg (fun h2 => hh (hex.mpr h2))]
