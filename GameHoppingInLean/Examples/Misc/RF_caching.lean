import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.PRF
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF

import Mathlib.Data.Finmap


/-- Ideal random-function oracle.
It samples a uniformly random function `X → Y` once during initialization and answers
each query by applying that sampled function. -/
noncomputable def PRF_ideal2 (X Y : Type) [DecidableEq X] [Fintype Y] [Nonempty Y] :
    RStateOracle (SecurePRFSpec X Y) where
  stateType := Finmap (fun _x : X => Y)
  initialState := pure ∅
  queries x := do
      let c <- get
      match c.lookup x with
      | Option.some y => return y
      | Option.none =>
          let newVal ← PMF.uniformOfFintype Y
          StateT.set (c.insert x newVal)
          pure newVal


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

private lemma Finmap.lookup_eq_none_iff_not_mem_keys {X Y : Type} [DecidableEq X]
    {st : Finmap (fun _x : X => Y)} {x : X} :
    st.lookup x = none ↔ x ∉ st.keys := by
  rw [Finmap.lookup_eq_none, Finmap.mem_keys]

@[simp] private lemma Finmap.keys_insert {X Y : Type} [DecidableEq X]
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

private lemma completePRFCache_empty (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    (completePRFCache X Y ∅ ) = PMF.uniformOfFintype (X → Y) := by
  classical
  simp [completePRFCache]
  -- simp only [GameHoppingSimplifyPMF]
  rw [← PMF.map_uniformOfFintype_equiv  (emptyCacheMissingEquiv X Y)]
  simp only [GameHoppingSimplifyPMF, emptyCacheMissingEquiv]
  simp

private noncomputable def missingAfterInsertEquiv {X Y : Type} [DecidableEq X]
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

/-- The eagerly sampled random-function oracle and its lazy cached implementation are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal2 (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  apply ObsEq.symm
  refine correctAbstractionBindImpliesObsEq  (PRF_ideal2 X Y) (PRF_ideal X Y) (completePRFCache X Y) ?_
  constructor
  · simp [PRF_ideal2, PRF_ideal, completePRFCache_empty]
    apply PMF.ext
    intro f
    simp [PMF.uniformOfFintype_apply]
  · simp [PRF_ideal, PRF_ideal2, OracleSpec.Domain, SecurePRFSpec]
    intro query
    ext1 st
    simp [bindInputState, bindOutputState, PRF_ideal, PRF_ideal2, completePRFCache,
              StateT.run, bindSecond, Functor.map, StateT.map, StateT.set, liftM, bindSecond, completePRFCache, monadLift, MonadLift.monadLift, StateT.lift, StateT.map]
    -- simp only [GameHoppingSimplifyPMF]
    cases hgm : Finmap.lookup query st with
    | none =>
      simp [bindSecond, completePRFCache, StateT.map, StateT.lift, StateT.set, StateT.run]
      simp only [GameHoppingSimplifyPMF]
      have hqNotIn : query ∉ st.keys := Finmap.lookup_eq_none_iff_not_mem_keys.mp hgm
      rw [← PMF.map_uniformOfFintype_equiv (missingAfterInsertEquiv st query hqNotIn).symm]
      simp [missingAfterInsertEquiv]
      rw [PMF.bind_comm]
      simp only [GameHoppingSimplifyPMF]
      congr 1
      ext1 a
      let tmp_isoD : { x // x ∉ (Finmap.insert query a st).keys } ≃ { x // x ∉ {query} ∪ st.keys } :=
        Equiv.subtypeEquivRight fun x => by simp [Finmap.keys_insert]
      let tmp_iso :  ({ x // x ∉ (Finmap.insert query a st).keys } → Y) ≃ ({ x // x ∉ {query} ∪ st.keys } → Y) :=
        Equiv.arrowCongr tmp_isoD (Equiv.refl Y)
      rw [← PMF.map_uniformOfFintype_equiv tmp_iso]
      simp [tmp_iso, tmp_isoD, Equiv.subtypeEquivRight, Equiv.subtypeEquiv, Equiv.arrowCongr]
      congr 1; ext1 f
      simp
      congr 1
      rw [ite_cond_eq_false] <;> try (simp; assumption)
      congr 1; ext1 x
      by_cases hx : x ∈ st.keys
      · rw [dite_cond_eq_true] <;> try (simp; right; assumption)
        rw [dite_cond_eq_true] <;> try (simp; assumption)
        rw [Finmap.lookup_insert_of_ne]
        intro contra; subst contra; contradiction
      · by_cases hxq : x = query
        · subst hxq
          rw [dite_cond_eq_true] <;> try simp
          rw [ite_cond_eq_false]
          simp
          assumption
        · rw [dite_cond_eq_false] <;> try (simp; constructor <;> assumption)
          rw [dite_cond_eq_false] <;> try simp ; assumption
          rw [dite_cond_eq_false]
          simp
          assumption
    | some v =>
        simp [bindSecond, completePRFCache]
        simp only [GameHoppingSimplifyPMF]
        congr 1; ext1 a
        simp
        congr 2
        rw [dite_cond_eq_true]
        simp
        by_contra hnot
        have hnone : Finmap.lookup query st = none :=
          Finmap.lookup_eq_none_iff_not_mem_keys.mpr hnot
        rw [hnone] at hgm
        contradiction

/-- Lift the cached random-function equivalence to indistinguishability. -/
noncomputable def indistinguishable_PRF_ideal_PRF_ideal2
    {Reductions : IndistinguishabilityReductions} (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    Indistinguishable IndistinguishabilityAssumptions.empty Reductions
      (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  intro κ
  exact Indistinguishable.of_ObsEq (obsEq_PRF_ideal_PRF_ideal2 X Y)


/-- It might be useful to have the caching function that triggers caching of more than one element --/

noncomputable def FinmapFromFun {X Y : Type} [DecidableEq X] (D : Finset X) (f : D → Y) :
    Finmap (fun _x : X => Y) :=
  D.attach.toList.foldl (fun c x => c.insert x.1 (f x)) ∅

noncomputable def FinmapFromOptionFun {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Option Y) : Finmap (fun _x : X => Y) :=
  FinmapFromFun (Finset.univ.filter fun x => (f x).isSome)
    (fun x => (f x.1).get (Finset.mem_filter.mp x.2).2)

noncomputable def PRF_ideal_cache_batch (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (f : X → Finset X) (hf : ∀ x, x ∈ f x) :
    RStateOracle (SecurePRFSpec X Y) where
  stateType := Finmap (fun _x : X => Y)
  initialState := pure ∅
  queries := {
    impl := fun _ x => by
      classical
      exact do
      let c <- get
      if hx : x ∈ c.keys then
        return (c.lookup x).getD (Classical.choice inferInstance)
      else
        let batch := (f x).filter (fun x' => x' ∉ c.keys)
        let newVals ← PMF.uniformOfFintype (batch → Y)
        StateT.set (c ∪ FinmapFromFun batch newVals)
        return newVals ⟨x, by simp [batch, hf x, hx]⟩
  }

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
        · intro x' hx'
          intro hx
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
  simpa [FinmapFromOptionFun, h] using
    (FinmapFromFun_lookup (Finset.univ.filter fun x => (f x).isSome)
      (fun x => (f x.1).get (Finset.mem_filter.mp x.2).2) hx)

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


private noncomputable def missingAfterBatchEquiv {X Y : Type} [DecidableEq X]
    (st : Finmap (fun _x : X => Y)) (D : Finset X)
    (hD : ∀ x, x ∈ D → x ∉ st.keys) (vals : D → Y) :
    ({x : X // x ∉ st.keys} → Y) ≃
      (D → Y) × ({x : X // x ∉ (st ∪ FinmapFromFun D vals).keys} → Y) where
  toFun missing :=
    ⟨fun x => missing ⟨x.1, hD x.1 x.2⟩,
     fun x => missing ⟨x.1, by
       have hx := x.2
       have hx' : x.1 ∉ st.keys ∧ x.1 ∉ (FinmapFromFun D vals).keys := by
         simpa [Finmap.keys_union] using hx
       exact hx'.1⟩⟩
  invFun p x :=
    if hxD : x.1 ∈ D then
      p.1 ⟨x.1, hxD⟩
    else
      p.2 ⟨x.1, by
        have hxNotMap : x.1 ∉ (FinmapFromFun D vals).keys := by
          simpa [FinmapFromFun_keys] using hxD
        simpa [Finmap.keys_union] using And.intro x.2 hxNotMap⟩
  left_inv missing := by
    funext x
    by_cases hxD : x.1 ∈ D <;> simp [hxD]
  right_inv p := by
    rcases p with ⟨batch, missing⟩
    apply Prod.ext
    · funext x
      simp
    · funext x
      have hxNotD : x.1 ∉ D := by
        intro hxD
        have hxKeys : x.1 ∈ (st ∪ FinmapFromFun D vals).keys := by
          simp [Finmap.keys_union, FinmapFromFun_keys, hxD]
        exact x.2 hxKeys
      simp [hxNotD]

private noncomputable def missingBatchEquiv {X Y : Type} [DecidableEq X]
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



/-- The eagerly sampled random-function oracle and the batched lazy cache are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal_cache_pair (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (f : X → Finset X) (hf : ∀ x, x ∈ f x) :
    ObsEq (PRF_ideal X Y) (PRF_ideal_cache_batch X Y f hf) := by
  apply ObsEq.symm
  refine correctAbstractionBindImpliesObsEq
    (PRF_ideal_cache_batch X Y f hf) (PRF_ideal X Y) (completePRFCache X Y) ?_
  constructor
  · simp [PRF_ideal_cache_batch, PRF_ideal, completePRFCache_empty]
    apply PMF.ext
    intro g
    simp [PMF.uniformOfFintype_apply]
  · simp [PRF_ideal, PRF_ideal_cache_batch, OracleSpec.domain, SecurePRFSpec]
    intro i query
    ext1 st
    simp [bindInputState, bindOutputState, PRF_ideal, PRF_ideal_cache_batch, completePRFCache,
              StateT.run, bindSecond, Functor.map, StateT.map, StateT.set, liftM,
              monadLift, MonadLift.monadLift, StateT.lift, StateT.map]
    simp only [GameHoppingSimplifyPMF]
    by_cases hq : query ∈ st.keys
    · simp [hq, bindSecond, completePRFCache]
    ·
      simp [hq, bindSecond, completePRFCache, StateT.map, StateT.lift, StateT.set, StateT.run]
      simp only [GameHoppingSimplifyPMF]
      simp [Finmap.keys_union, FinmapFromFun_keys]
      let D := {x' ∈ f query | x' ∉ st.keys}
      have hD : ∀ x, x ∈ D → x ∉ st.keys := by
        intro x hx
        have hx' : x ∈ {x' ∈ f query | x' ∉ st.keys} := by
          simpa [D] using hx
        exact (Finset.mem_filter.mp hx').2
      rw [← PMF.map_uniformOfFintype_equiv (missingBatchEquiv st D hD).symm]
      simp [missingBatchEquiv, D]
      congr 1
      ext1 a
      let tmp_isoD :
          {x : X // x ∉ (st ∪ FinmapFromFun ({x' ∈ f query | x' ∉ st.keys}) a).keys} ≃
            {x : X // x ∉ st.keys ∧ x ∉ {x' ∈ f query | x' ∉ st.keys}} :=
        Equiv.subtypeEquivRight fun x => by
          simp [Finmap.keys_union, FinmapFromFun_keys]
      let tmp_iso :
          ({x : X // x ∉ (st ∪ FinmapFromFun ({x' ∈ f query | x' ∉ st.keys}) a).keys} → Y) ≃
            ({x : X // x ∉ st.keys ∧ x ∉ {x' ∈ f query | x' ∉ st.keys}} → Y) :=
        Equiv.arrowCongr tmp_isoD (Equiv.refl Y)
      rw [← PMF.map_uniformOfFintype_equiv tmp_iso]
      simp [tmp_iso, tmp_isoD, Equiv.subtypeEquivRight, Equiv.subtypeEquiv, Equiv.arrowCongr,
        Finmap.keys_union, FinmapFromFun_keys]
      congr 1
      ext1 b
      simp [Function.comp]
      congr 1
      apply Prod.ext
      · simp [hf query, hq]
      · funext x
        simp only [Prod.snd]
        by_cases hxst : x ∈ st.keys
        · have hxmem : x ∈ st := by
            simpa [Finmap.mem_keys] using hxst
          simp [hxst, Finmap.lookup_union_left hxmem]
        · by_cases hxf : x ∈ f query
          · have hxD : x ∈ {x' ∈ f query | x' ∉ st.keys} := by
              simp [hxf, hxst]
            have hxnotmem : x ∉ st := by
              simpa [Finmap.mem_keys] using hxst
            simp [hxst, hxf, Finmap.lookup_union_right hxnotmem, FinmapFromFun_lookup, hxD]
          · have hxnot : ¬(x ∈ f query ∧ x ∉ st.keys) := by
              intro h
              exact hxf h.1
            simp [hxst, hxf, hxnot]
