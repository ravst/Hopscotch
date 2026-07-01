import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finmap

/-!
# Core lemmas for lazy random-function caching

This file collects the purely probabilistic / `Finmap` content used to relate the eagerly
sampled random-function oracle to its lazy cached implementations.  It deliberately depends
only on `Mathlib` so that the heavy `PMF`/`Finmap` reasoning is isolated from the
oracle/observational-equivalence machinery in `RF_caching.lean`.
-/

namespace RFCache

/-
Pushing an equivalence through a uniform distribution over a finite type.
-/
theorem map_uniformOfFintype_equiv {X Y : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (e : X ≃ Y) :
    (PMF.uniformOfFintype X).map e = PMF.uniformOfFintype Y := by
  ext y; simp +decide [ *, PMF.map_apply, PMF.uniformOfFintype_apply ] ;
  rw [ Finset.sum_eq_single ( e.symm y ) ] <;> simp +decide [ e.symm_apply_apply ];
  · exact Fintype.card_congr e;
  · grind

end RFCache

/-- Complete a lazy random-function cache into a total function.

Cached inputs keep their stored outputs; every input absent from the cache is filled with
an independently uniform value. -/
noncomputable def completePRFCache (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (cache : Finmap (fun _x : X => Y)) : PMF (X → Y) := by
    classical
    exact do
    let missing ← PMF.uniformOfFintype ({x : X // x ∉ cache.keys} → Y)
    pure fun x =>
      if h : x ∈ cache.keys then
        (cache.lookup x).getD (Classical.choice inferInstance)
      else
        missing ⟨x, h⟩

lemma Finmap.lookup_eq_none_iff_not_mem_keys {X Y : Type} [DecidableEq X]
    {st : Finmap (fun _x : X => Y)} {x : X} :
    st.lookup x = none ↔ x ∉ st.keys := by
  rw [Finmap.lookup_eq_none, Finmap.mem_keys]

@[simp] lemma Finmap.keys_insert {X Y : Type} [DecidableEq X]
    (st : Finmap (fun _x : X => Y)) (query : X) (a : Y) :
    (st.insert query a).keys = ({query} : Finset X) ∪ st.keys := by
  ext x
  simp [Finmap.mem_keys, Finmap.mem_insert]

private noncomputable def emptyCacheMissingEquiv (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    ({x : X // x ∉ (∅ : Finmap (fun _x : X => Y)).keys} → Y) ≃ (X → Y) where
  toFun missing x := missing ⟨x, by simp [Finmap.keys_empty]⟩
  invFun f x := f x.1
  left_inv missing := by
    funext x
    simp
  right_inv f := by
    funext x
    rfl

lemma completePRFCache_empty (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    (completePRFCache X Y ∅ ) = PMF.uniformOfFintype (X → Y) := by
  convert RFCache.map_uniformOfFintype_equiv ( emptyCacheMissingEquiv X Y ) using 1

noncomputable def missingAfterInsertEquiv {X Y : Type} [DecidableEq X]
    (st : Finmap (fun _x : X => Y)) (query : X)
    (hquery : query ∉ st.keys) :
    ({x : X // x ∉ st.keys} → Y) ≃
      ({x : X // x ∉ ({query} : Finset X) ∪ st.keys} → Y) × Y where
  toFun f :=
    ⟨fun x => f ⟨x.1, by
      have hx := x.2
      simp at hx
      exact hx.2⟩ ,
    f ⟨query, hquery⟩⟩
  invFun p x :=
    if hx : x.1 = query then
      p.2
    else
      p.1 ⟨x.1, by
        simp
        constructor <;> try assumption
        exact x.2⟩
  left_inv missing := by
    funext x
    by_cases hx : x.1 = query <;> try simp [hx]
    subst hx
    simp
  right_inv p := by
    rcases p with ⟨missing, a'⟩
    apply Prod.ext
    · funext x
      by_cases hx : x.1 = query
      · exfalso
        exact x.2 (by
          simp
          exact Or.inl hx)
      · simp [hx]
    · simp

/-- It might be useful to have the caching function that triggers caching of more than one
element. -/
noncomputable def FinmapFromFun {X Y : Type} [DecidableEq X] (D : Finset X) (f : D → Y) :
    Finmap (fun _x : X => Y) :=
  D.attach.toList.foldl (fun c x => c.insert x.1 (f x)) ∅

noncomputable def FinmapFromOptionFun {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) : Finmap (fun _x : X => Y) :=
  FinmapFromFun (Finset.univ.filter fun x => (f x).isSome)
    (fun x => (f x.1).get (Finset.mem_filter.mp x.2).2)

private lemma Finmap.mem_keys_foldl_insert_list {X Y : Type} [DecidableEq X]
    {D : Finset X} (f : D → Y) (l : List D)
    (c : Finmap (fun _x : X => Y)) (x : X) :
    x ∈ (l.foldl (fun c x' => c.insert x'.1 (f x')) c).keys ↔
      x ∈ c.keys ∨ ∃ x' ∈ l, x'.1 = x := by
  induction l generalizing c with
  | nil =>
      simp
  | cons hd tl ih =>
      rw [List.foldl_cons, ih]
      simp [Finmap.keys_insert]
      tauto

private lemma Finmap.lookup_foldl_insert_list_of_not_mem {X Y : Type} [DecidableEq X]
    {D : Finset X} (f : D → Y) (l : List D)
    (c : Finmap (fun _x : X => Y)) (x : X)
    (hnot : ∀ x' ∈ l, x'.1 ≠ x) :
    (l.foldl (fun c x' => c.insert x'.1 (f x')) c).lookup x = c.lookup x := by
  induction l generalizing c with
  | nil =>
      simp
  | cons hd tl ih =>
      rw [List.foldl_cons, ih]
      · exact Finmap.lookup_insert_of_ne c (Ne.symm (hnot hd (by simp)))
      · intro x' hx'
        exact hnot x' (by simp [hx'])

private lemma Finmap.lookup_foldl_insert_list_of_mem {X Y : Type} [DecidableEq X]
    {D : Finset X} (f : D → Y) (l : List D)
    (c : Finmap (fun _x : X => Y)) (hnd : l.Nodup)
    {x : X} (hxD : x ∈ D) (hmem : (⟨x, hxD⟩ : D) ∈ l) :
    (l.foldl (fun c x' => c.insert x'.1 (f x')) c).lookup x = some (f ⟨x, hxD⟩) := by
  induction l generalizing c with
  | nil =>
      simp at hmem
  | cons hd tl ih =>
      rw [List.foldl_cons]
      by_cases hhd : hd = ⟨x, hxD⟩
      · subst hhd
        rw [Finmap.lookup_foldl_insert_list_of_not_mem]
        · simp
        · intro x' hx' hx
          apply (List.nodup_cons.mp hnd).1
          have hxEq : x' = ⟨x, hxD⟩ := Subtype.ext hx
          exact hxEq ▸ hx'
      · have hmemTl : (⟨x, hxD⟩ : D) ∈ tl := by
          simp at hmem
          rcases hmem with h | h
          · exact False.elim (hhd h.symm)
          · exact h
        exact ih (c.insert hd.1 (f hd)) (List.nodup_cons.mp hnd).2 hmemTl

@[simp] lemma FinmapFromFun_keys {X Y : Type} [DecidableEq X]
    (D : Finset X) (f : D → Y) :
    (FinmapFromFun D f).keys = D := by
  ext x
  simp [FinmapFromFun, Finmap.mem_keys_foldl_insert_list]

@[simp] lemma FinmapFromFun_lookup {X Y : Type} [DecidableEq X]
    (D : Finset X) (f : D → Y) {x : X} (hx : x ∈ D) :
    (FinmapFromFun D f).lookup x = some (f ⟨x, hx⟩) := by
  simpa [FinmapFromFun] using
    (Finmap.lookup_foldl_insert_list_of_mem f D.attach.toList
      (∅ : Finmap (fun _x : X => Y)) (Finset.nodup_toList D.attach) hx (by simp))

@[simp] theorem FinmapFromOptionFun_keys {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) :
    (FinmapFromOptionFun f).keys = Finset.univ.filter (fun x => (f x).isSome) := by
  simp [FinmapFromOptionFun]

@[simp] theorem FinmapFromOptionFun_lookup_some {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) {x : X} {y : Y} (h : f x = some y) :
    (FinmapFromOptionFun f).lookup x = some y := by
  have hx : x ∈ Finset.univ.filter (fun x => (f x).isSome) := by
    simp [h]
  rw [FinmapFromOptionFun,
    FinmapFromFun_lookup (Finset.univ.filter fun x => (f x).isSome)
      (fun x => (f x.1).get (Finset.mem_filter.mp x.2).2) hx]
  simp [h]

@[simp] theorem FinmapFromOptionFun_lookup_none {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) {x : X} (h : f x = none) :
    (FinmapFromOptionFun f).lookup x = none := by
  rw [Finmap.lookup_eq_none]
  rw [← Finmap.mem_keys]
  simp [FinmapFromOptionFun_keys, h]

@[simp] theorem FinmapFromOptionFun_lookup {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) (x : X) :
    (FinmapFromOptionFun f).lookup x = f x := by
  cases h : f x with
  | none =>
      exact FinmapFromOptionFun_lookup_none f h
  | some y =>
      exact FinmapFromOptionFun_lookup_some f h

@[simp] theorem FinmapFromOptionFun_none {X Y : Type} [Fintype X] [DecidableEq X] :
    FinmapFromOptionFun (fun _x : X => (none : Option Y)) = ∅ := by
  apply Finmap.ext_lookup
  intro x
  simp

@[simp] theorem FinmapFromOptionFun_union_insert {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) (m : Finmap (fun _x : X => Y)) (key : X) (elem : Y) :
    FinmapFromOptionFun f ∪ Finmap.insert key elem m =
      FinmapFromOptionFun (fun x =>
        match f x with
        | some y => some y
        | none => if x = key then some elem else m.lookup x) := by
  apply Finmap.ext_lookup
  intro x
  cases hfx : f x with
  | some y =>
      have hx : x ∈ FinmapFromOptionFun f := by
        rw [← Finmap.mem_keys]
        simp [FinmapFromOptionFun_keys, hfx]
      rw [Finmap.lookup_union_left hx]
      simp [FinmapFromOptionFun_lookup_some, hfx]
  | none =>
      have hx : x ∉ FinmapFromOptionFun f := by
        rw [← Finmap.mem_keys]
        simp [FinmapFromOptionFun_keys, hfx]
      rw [Finmap.lookup_union_right hx]
      by_cases hkey : x = key
      · subst x
        rw [Finmap.lookup_insert]
        symm
        apply FinmapFromOptionFun_lookup_some
        simp [hfx]
      · rw [Finmap.lookup_insert_of_ne m hkey]
        cases hm : m.lookup x with
        | some y =>
            simp [hfx, hkey, FinmapFromOptionFun_lookup_some, hm]
        | none =>
            simp [hfx, hkey, FinmapFromOptionFun_lookup_none, hm]

noncomputable def missingBatchEquiv {X Y : Type} [DecidableEq X]
    (st : Finmap (fun _x : X => Y)) (D : Finset X)
    (hD : ∀ x, x ∈ D → x ∉ st.keys) :
    ({x : X // x ∉ st.keys} → Y) ≃
      (D → Y) × ({x : X // x ∉ st.keys ∧ x ∉ D} → Y) where
  toFun missing :=
    ⟨fun x => missing ⟨x.1, hD x.1 x.2⟩,
     fun x => missing ⟨x.1, x.2.1⟩⟩
  invFun p x :=
    if hxD : x.1 ∈ D then
      p.1 ⟨x.1, hxD⟩
    else
      p.2 ⟨x.1, ⟨x.2, hxD⟩⟩
  left_inv missing := by
    funext x
    by_cases hxD : x.1 ∈ D <;> simp [hxD]
  right_inv p := by
    rcases p with ⟨batch, missing⟩
    apply Prod.ext
    · funext x
      simp
    · funext x
      simp [x.2.2]

/-- A uniform distribution over a product is the same as sampling each coordinate
independently and uniformly. -/
theorem uniform_prod_bind {A B C : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (k : A → B → PMF C) :
    ((PMF.uniformOfFintype (A × B)).bind fun p => k p.1 p.2)
      = (PMF.uniformOfFintype A).bind fun a => (PMF.uniformOfFintype B).bind fun b => k a b := by
  ext c;
  simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ENNReal.mul_inv ];
  exact congr_arg _ ( by rw [ ← Finset.sum_product' ] ; rfl )

/-- Recursion for `completePRFCache` at a single fresh key: completing a cache is the same
as first sampling the value at `query` uniformly, inserting it, and completing the larger
cache. -/
theorem completePRFCache_insert_eq (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (st : Finmap (fun _x : X => Y)) (query : X) (hq : query ∉ st.keys) :
    completePRFCache X Y st
      = (PMF.uniformOfFintype Y).bind fun a => completePRFCache X Y (st.insert query a) := by
  -- By definition of `completePRFCache`, we can write it as a bind of the uniform distribution over the missing keys.
  have h_completePRFCache_def : ∀ (s : Finmap (fun _x : X => Y)), completePRFCache X Y s = (PMF.uniformOfFintype ({x : X // x ∉ s.keys} → Y)).map (fun missing x => if h : x ∈ s.keys then (s.lookup x).getD (Classical.choice inferInstance) else missing ⟨x, h⟩) := by
    unfold completePRFCache; aesop;
  -- Let `e := missingAfterInsertEquiv st query hq : F_st ≃ F_K × Y` where `F_st = {x // x ∉ st.keys} → Y` and `F_K = {x // x ∉ {query} ∪ st.keys} → Y`.
  set e := missingAfterInsertEquiv st query hq with he;
  -- From `RFCache.map_uniformOfFintype_equiv e` we get `uniformOfFintype F_st = (uniformOfFintype (F_K × Y)).map e.symm`.
  have h_uniform_equiv : PMF.uniformOfFintype ({x : X // x ∉ st.keys} → Y) = (PMF.uniformOfFintype ({x : X // x ∉ {query} ∪ st.keys} → Y)).bind (fun g => (PMF.uniformOfFintype Y).bind (fun a => PMF.pure (e.symm (g, a)))) := by
    have h_uniform_equiv : PMF.uniformOfFintype ({x : X // x ∉ st.keys} → Y) = (PMF.uniformOfFintype ({x : X // x ∉ {query} ∪ st.keys} → Y)).bind (fun g => (PMF.uniformOfFintype Y).bind (fun a => PMF.pure (e.symm (g, a)))) := by
      have h_uniform_equiv : PMF.uniformOfFintype ({x : X // x ∉ st.keys} → Y) = (PMF.uniformOfFintype ({x : X // x ∉ {query} ∪ st.keys} → Y) |>.bind (fun g => PMF.uniformOfFintype Y |>.bind (fun a => PMF.pure (e.symm (g, a))))) := by
        have := RFCache.map_uniformOfFintype_equiv e.symm
        rw [ ← this, PMF.map ];
        convert uniform_prod_bind _ using 1;
        rfl
      exact h_uniform_equiv;
    exact h_uniform_equiv;
  -- By `uniform_prod_bind`, `= (uniformOfFintype F_K).bind fun g => (uniformOfFintype Y).bind fun a => pure (build st (e.symm (g,a)))`.
  have h_uniform_prod_bind : PMF.map (fun missing x => if h : x ∈ st.keys then (st.lookup x).getD (Classical.choice inferInstance) else missing ⟨x, h⟩) (PMF.uniformOfFintype ({x : X // x ∉ st.keys} → Y)) = (PMF.uniformOfFintype ({x : X // x ∉ {query} ∪ st.keys} → Y)).bind (fun g => (PMF.uniformOfFintype Y).bind (fun a => PMF.pure (fun x => if h : x ∈ st.keys then (st.lookup x).getD (Classical.choice inferInstance) else e.symm (g, a) ⟨x, h⟩))) := by
    convert congr_arg ( fun p => PMF.map ( fun missing x => if h : x ∈ st.keys then ( Finmap.lookup x st ).getD ( Classical.choice inferInstance ) else missing ⟨ x, h ⟩ ) p ) h_uniform_equiv using 1;
    ext; simp [PMF.map];
  rw [ h_completePRFCache_def, h_uniform_prod_bind, PMF.bind_comm ];
  congr! 2;
  rw [ h_completePRFCache_def ];
  rw [ Finmap.keys_insert ];
  ext; simp +decide [ Finmap.lookup_insert, Finmap.lookup_insert_of_ne, hq ] ;
  congr! 2;
  congr! 2;
  split_ifs <;> simp_all +decide [ Finmap.lookup_insert, Finmap.lookup_insert_of_ne ];
  · rw [ Finmap.lookup_insert_of_ne ] ; aesop;
  · grind;
  · unfold missingAfterInsertEquiv; aesop;
  · simp +decide [ missingAfterInsertEquiv ];
    grobner

/-- Recursion for `completePRFCache` at a batch of fresh keys: completing a cache is the
same as first sampling values for all of `D` uniformly, inserting them, and completing the
larger cache. -/
theorem completePRFCache_union_eq (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (st : Finmap (fun _x : X => Y)) (D : Finset X)
    (hD : ∀ x, x ∈ D → x ∉ st.keys) :
    completePRFCache X Y st
      = (PMF.uniformOfFintype (D → Y)).bind fun vals =>
          completePRFCache X Y (st ∪ FinmapFromFun D vals) := by
  have h_uniform_prod_bind : PMF.uniformOfFintype ({x : X // x ∉ st.keys} → Y) = (PMF.uniformOfFintype (D → Y)).bind (fun vals => PMF.uniformOfFintype ({x : X // x ∉ st.keys ∧ x ∉ D} → Y) |>.bind (fun g => PMF.pure (missingBatchEquiv st D hD |>.symm (vals, g)))) := by
    have h_uniform_equiv : PMF.uniformOfFintype ({x : X // x ∉ st.keys} → Y) = (PMF.uniformOfFintype ((D → Y) × ({x : X // x ∉ st.keys ∧ x ∉ D} → Y))).map (missingBatchEquiv st D hD).symm :=
      Eq.symm (RFCache.map_uniformOfFintype_equiv (missingBatchEquiv st D hD).symm)
    rw [ h_uniform_equiv, PMF.map ];
    convert uniform_prod_bind _ using 1;
    rfl;
  convert congr_arg ( fun p => PMF.map ( fun missing x => if h : x ∈ st.keys then ( Finmap.lookup x st ).getD ( Classical.choice inferInstance ) else missing ⟨ x, h ⟩ ) p ) h_uniform_prod_bind using 1;
  ext; simp [PMF.map];
  congr! 2;
  convert PMF.map_apply _ _ _ using 2;
  rw [ tsum_fintype ];
  refine Finset.sum_bij ( fun g _ => fun x => g ⟨ x, by
    grind +suggestions ⟩ ) ?_ ?_ ?_ ?_ <;> simp +decide [ missingBatchEquiv ];
  · simp +decide [ funext_iff ];
    intro a₁ a₂ h a ha₁ ha₂; specialize h a; simp_all +decide [ Finmap.keys_union, FinmapFromFun_keys ] ;
  · exact fun b => ⟨ fun x => b ⟨ x, by
      simp +decide [ Finmap.keys_union, FinmapFromFun_keys, x.2 ] ⟩, rfl ⟩;
  · congr! 2;
    · all_goals generalize_proofs at *;
      grind +suggestions;
    · rw [ Fintype.card_subtype ];
      rw [ show ( Finset.filter ( fun x => x ∉ st.keys ∧ x ∉ D ) Finset.univ : Finset X ) = Finset.univ \ ( st.keys ∪ D ) by ext; aesop ] ; rw [ Finset.card_sdiff ] ; norm_num;
      rw [ Finmap.keys_union, FinmapFromFun_keys ]

/-! ### Crux diagram lemmas

These express the commutation of the caching abstraction `completePRFCache` with a single
query step of the lazy oracles, purely in terms of `PMF`/`Finmap`. -/

/-- Fresh-query step: sampling a value for a not-yet-cached `query`, inserting it, and then
completing the cache is the same as completing the cache directly and reading off `query`. -/
theorem completePRFCache_diagram_fresh (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (st : Finmap (fun _x : X => Y)) (query : X) (hq : query ∉ st.keys) :
    ((PMF.uniformOfFintype Y).bind fun a =>
        (completePRFCache X Y (st.insert query a)).bind fun c => PMF.pure (a, c))
      = (completePRFCache X Y st).bind fun c => PMF.pure (c query, c) := by
  rw [ completePRFCache_insert_eq X Y st query hq ];
  -- By definition of `completePRFCache`, we know that for any `a` and `c` in the support of `completePRFCache X Y (st.insert query a)`, we have `c query = a`.
  have h_support : ∀ a : Y, ∀ c ∈ (completePRFCache X Y (st.insert query a)).support, c query = a := by
    intro a c hc; unfold completePRFCache at hc; simp_all +decide [ Finmap.lookup_insert, Finmap.lookup_insert_of_ne ] ;
    contrapose! hc;
    convert PMF.map_apply _ _ _ |> Eq.trans <| _ using 1;
    convert tsum_zero with x ; aesop;
  ext c; simp [PMF.bind_apply];
  grind +suggestions

/-- Cached-query step: when `query` is already cached with value `v`, reading the cache and
completing it agrees with completing the cache and reading off `query`. -/
theorem completePRFCache_diagram_cached (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (st : Finmap (fun _x : X => Y)) (query : X) (v : Y)
    (hv : st.lookup query = some v) :
    ((completePRFCache X Y st).bind fun c => PMF.pure (v, c))
      = (completePRFCache X Y st).bind fun c => PMF.pure (c query, c) := by
  have h_eq : ∀ c ∈ (completePRFCache X Y st).support, c query = v := by
    intro c hc
    have hc' : ∃ missing : {x : X // x ∉ st.keys} → Y,
        c = fun x => if h : x ∈ st.keys then (st.lookup x).getD (Classical.choice inferInstance)
          else missing ⟨x, h⟩ := by
      contrapose! hc
      unfold completePRFCache
      simp +decide [hc]
      exact (PMF.map_apply _ _ _).trans (by aesop)
    obtain ⟨missing, hmissing⟩ := hc'
    grind +suggestions
  simp +zetaDelta at *
  ext c
  simp [PMF.bind_apply]
  grind

/-- Batched fresh-query step: sampling a batch of values for a set `D` of not-yet-cached
inputs (with `query ∈ D`), inserting them, and completing the cache agrees with completing
the cache directly and reading off `query`. -/
theorem completePRFCache_diagram_batch (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (st : Finmap (fun _x : X => Y)) (query : X) (D : Finset X)
    (hqD : query ∈ D) (hD : ∀ x, x ∈ D → x ∉ st.keys) :
    ((PMF.uniformOfFintype (D → Y)).bind fun vals =>
        (completePRFCache X Y (st ∪ FinmapFromFun D vals)).bind fun c =>
          PMF.pure (vals ⟨query, hqD⟩, c))
      = (completePRFCache X Y st).bind fun c => PMF.pure (c query, c) := by
  have h_eq : ∀ vals : D → Y, ∀ c ∈ (completePRFCache X Y (st ∪ FinmapFromFun D vals)).support, c query = vals ⟨query, hqD⟩ := by
    intro vals c hc;
    have hc' : ∃ missing : {x : X // x ∉ (st ∪ FinmapFromFun D vals).keys} → Y,
        c = fun x => if h : x ∈ (st ∪ FinmapFromFun D vals).keys then
          ((st ∪ FinmapFromFun D vals).lookup x).getD (Classical.choice inferInstance)
          else missing ⟨x, h⟩ := by
      contrapose! hc
      unfold completePRFCache
      simp +decide [hc]
      exact (PMF.map_apply _ _ _).trans (by aesop)
    obtain ⟨missing, hmissing⟩ := hc'
    grind +suggestions
  rw [completePRFCache_union_eq X Y st D hD]
  simp +decide [PMF.bind_bind, h_eq]
  congr! 2
  ext c
  simp [PMF.bind_apply]
  grind +suggestions
