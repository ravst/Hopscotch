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

private def optionGetWithProof {Y : Type} (o : Option Y) (F : o = none → Y) : Y :=
  match o with
  | some y => y
  | none => F rfl

@[simp] private lemma optionGetWithProof_eq_some {Y : Type} {o : Option Y} {a : Y}
    (ho : o = some a) (F : o = none → Y) :
    optionGetWithProof o F = a := by
  subst o
  rfl

@[simp] private lemma optionGetWithProof_eq_none {Y : Type} {o : Option Y}
    (ho : o = none) (F : o = none → Y) :
    optionGetWithProof o F = F ho := by
  subst o
  rfl

private lemma optionGetWithProof_congr {Y : Type} {o₁ o₂ : Option Y}
    (ho : o₁ = o₂) (F₁ : o₁ = none → Y) (F₂ : o₂ = none → Y)
    (hF : ∀ h₁ h₂, F₁ h₁ = F₂ h₂) :
    optionGetWithProof o₁ F₁ = optionGetWithProof o₂ F₂ := by
  subst o₂
  by_cases hn : o₁ = none
  · simpa [optionGetWithProof_eq_none hn] using hF hn hn
  · rcases o₁ with _ | y
    · contradiction
    · simp [optionGetWithProof_eq_some rfl]

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
      optionGetWithProof (cache.lookup x) fun h =>
        missing ⟨x, by
          rw [Finmap.mem_keys]
          exact Finmap.lookup_eq_none.mp h⟩

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
  toFun missing :=
    (fun x =>
        missing ⟨x.1, by
          exact fun hxkeys =>
            x.2 (by
              simp
              exact Or.inr hxkeys)⟩,
      missing ⟨query, hquery⟩)
  invFun p x :=
    if hx : x.1 = query then
      p.2
    else
      p.1 ⟨x.1, by
        intro hxkeys
        simp at hxkeys
        cases hxkeys with
        | inl hsame => exact hx hsame
        | inr hmem => exact x.2 hmem⟩
  left_inv missing := by
    funext x
    by_cases hx : x.1 = query
    · subst hx
      simp
    · simp [hx]
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

private noncomputable def missingAfterInsertEquiv2 {X Y : Type} [DecidableEq X]
    (st : Finmap (fun _x : X => Y)) (query : X) (a : Y)
    (hquery : query ∉ st.keys) :
    ({x : X // x ∉ st.keys} → Y) ≃
      ({x : X // x ∉ (st.insert query a).keys} → Y) × Y where
  toFun missing :=
    (fun x =>
        missing ⟨x.1, by
          intro hxkeys
          exact x.2 (by
            simpa [Finmap.keys_insert] using
              (Or.inr hxkeys : x.1 = query ∨ x.1 ∈ st.keys))⟩,
      missing ⟨query, hquery⟩)
  invFun p x :=
    if hx : x.1 = query then
      p.2
    else
      p.1 ⟨x.1, by
        have hnot : x.1 ∉ ({query} : Finset X) ∪ st.keys := by
          simp [hx, x.2]
        simpa [Finmap.keys_insert] using hnot⟩
  left_inv missing := by
    funext x
    by_cases hx : x.1 = query
    · subst hx
      simp
    · simp [hx]
  right_inv p := by
    rcases p with ⟨missing, a'⟩
    apply Prod.ext
    · funext x
      by_cases hx : x.1 = query
      · exfalso
        exact x.2 (by
          simp [Finmap.keys_insert, hx])
      · simp [hx]
    · simp



/-- The eagerly sampled random-function oracle and its lazy cached implementation are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal2 (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  apply ObsEq.symm
  exact correctAbstractionBindImpliesObsEq
    (PRF_ideal2 X Y) (PRF_ideal X Y) (completePRFCache X Y) (by
      constructor
      · simp [PRF_ideal2, PRF_ideal, completePRFCache_empty]
        apply PMF.ext
        intro f
        simp [PMF.uniformOfFintype_apply]
      · simp [PRF_ideal, PRF_ideal2, OracleSpec.domain, SecurePRFSpec]
        intro i query
        ext1 st
        simp [bindInputState, bindOutputState, PRF_ideal, PRF_ideal2, completePRFCache,
              StateT.run, bindSecond]
        simp only [GameHoppingSimplifyPMF, Functor.map, StateT.map, StateT.set, liftM]

        by_cases heq : Finmap.lookup query st = none
        ·
          simp [heq, bindSecond, completePRFCache]
          simp only [GameHoppingSimplifyPMF, StateT.run, StateT.map, StateT.set]
          simp
          simp only [GameHoppingSimplifyPMF]
          let iso := missingAfterInsertEquiv st query
            (Finmap.lookup_eq_none_iff_not_mem_keys.mp heq)
          rw [← PMF.map_uniformOfFintype_equiv  iso.symm]
          simp [iso, missingAfterInsertEquiv]
          simp only [GameHoppingSimplifyPMF]
          let iso2 (a : Y) :
              {x : X // x ∉ (Finmap.insert query a st).keys} ≃
                {x : X // x ∉ ({query} : Finset X) ∪ st.keys} := {
            toFun := fun x => ⟨x.1, by
              simpa [Finmap.keys_insert] using x.2⟩
            invFun := fun x => ⟨x.1, by
              simpa [Finmap.keys_insert] using x.2⟩
            left_inv := fun x => by
              ext
              rfl
            right_inv := fun x => by
              ext
              rfl
          }
          have hinner (a : Y) :
              (do
                let a_1 ← PMF.uniformOfFintype
                  ({x : X // x ∉ (Finmap.insert query a st).keys} → Y)
                pure
                  (a, fun x => optionGetWithProof
                    (Finmap.lookup x (Finmap.insert query a st)) fun h =>
                      a_1 ⟨x, by
                        rw [Finmap.mem_keys]
                        exact Finmap.lookup_eq_none.mp h⟩)) =
              (do
                let a_1 ← PMF.uniformOfFintype
                  ({x : X // x ∉ ({query} : Finset X) ∪ st.keys} → Y)
                pure
                  (a, fun x => optionGetWithProof
                    (Finmap.lookup x (Finmap.insert query a st)) fun h =>
                        (Equiv.arrowCongr (iso2 a).symm (Equiv.refl Y) a_1) ⟨x, by
                          rw [Finmap.mem_keys]
                          exact Finmap.lookup_eq_none.mp h⟩)) := by
            change (PMF.uniformOfFintype
                ({x : X // x ∉ (Finmap.insert query a st).keys} → Y)).bind _ = _
            rw [PMF.bind_uniformOfFintype_equiv
              (e := Equiv.arrowCongr (iso2 a).symm (Equiv.refl Y))]
            rfl
          conv_lhs =>
            enter [2, a]
            rw [hinner a]
          simp
          rw [PMF.bind_comm]
          congr 1
          ext1 f
          congr 1
          ext1 a
          congr
          ext x
          simp[iso2]

          by_cases hxq : x = query
          · subst hxq
            simp [Finmap.lookup_insert, heq]

          · simp only [dif_neg hxq]
            refine optionGetWithProof_congr (Finmap.lookup_insert_of_ne st hxq) _ _ ?_
            intro h₁ h₂
            congr 1
        ·
          let cached : Y := (Finmap.lookup query st).getD (Classical.choice ‹Nonempty Y›)
          have hcached : Finmap.lookup query st = some cached := by
            dsimp [cached]
            cases hlookup : Finmap.lookup query st with
            | none => contradiction
            | some y => simp [hlookup]
          simp [hcached, bindSecond, completePRFCache]

      )


/-- Lift the cached random-function equivalence to indistinguishability. -/
noncomputable def indistinguishable_PRF_ideal_PRF_ideal2
    {Reductions : IndistinguishabilityReductions} (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    Indistinguishable IndistinguishabilityAssumptions.empty Reductions
      (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  intro κ
  exact Indistinguishable.of_ObsEq (obsEq_PRF_ideal_PRF_ideal2 X Y)
