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
  queries := {
    impl := fun _ x => do
      let c <- get
      match c.lookup x with
      | Option.some y => return y
      | Option.none =>
          let newVal ← PMF.uniformOfFintype Y
          StateT.set (c.insert x newVal)
          pure newVal
  }

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
  simp only [GameHoppingSimplifyPMF]
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
  · simp [PRF_ideal, PRF_ideal2, OracleSpec.domain, SecurePRFSpec]
    intro i query
    ext1 st
    simp [bindInputState, bindOutputState, PRF_ideal, PRF_ideal2, completePRFCache,
              StateT.run, bindSecond, Functor.map, StateT.map, StateT.set, liftM, bindSecond, completePRFCache, monadLift, MonadLift.monadLift, StateT.lift, StateT.map]
    simp only [GameHoppingSimplifyPMF]
    generalize hgm : Finmap.lookup query st = gm
    cases gm with
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
      congr 1
      ext1 f
      simp
      congr 1
      rw [ite_cond_eq_false] <;> try (simp; assumption)
      congr 1
      ext1 x
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
        congr 1
        ext1 a
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
