import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finmap
import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.Examples.Schemes.PRF
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF
import GameHoppingInLean.Examples.Misc.RF_cachingCore

/-!
# Lazy random-function caching

The eagerly sampled random-function oracle `PRF_ideal` samples an entire function `X → Y`
up front.  This file introduces two lazy cached implementations and shows each is
observationally equivalent to `PRF_ideal`, via the state abstraction `completePRFCache`
(defined in `RF_cachingCore.lean`).  The heavy `PMF`/`Finmap` reasoning is isolated in the
crux lemmas `completePRFCache_diagram_fresh`, `completePRFCache_diagram_cached` and
`completePRFCache_diagram_batch`; here we only normalize the oracle/state plumbing and apply
them.
-/

/-- Ideal random-function oracle, lazy single-entry cache.
It answers a query `x` by returning the cached value if present, or sampling a fresh uniform
value, caching it, and returning it. -/
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

/-- The eagerly sampled random-function oracle and its lazy cached implementation are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal2 (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  obs_eq_by_rand_abstraction ← (completePRFCache X Y)
  case left =>
    -- initialization: the completed empty cache is the uniform random function
    simp only [PRF_ideal, PRF_ideal2, PMF.pure_bind]
    convert completePRFCache_empty X Y using 2
    exact PMF.pure_bind _ _
  case right =>
    -- per-query diagram
    simp only [PRF_ideal, PRF_ideal2, OracleSpec.Domain, SecurePRFSpec]
    intro query
    ext1 st
    simp only [correctAbstractionDiagSimps, StateTSimps, RStateSimplifier,
      GameHoppingSimplifyPMF, PRF_ideal, PRF_ideal2]
    cases hgm : Finmap.lookup query st with
    | none =>
      simp only [GameHoppingSimplifyPMF, StateTSimps, RStateSimplifier, StateT.set, bindSecond]
      exact completePRFCache_diagram_fresh X Y st query
        (Finmap.lookup_eq_none_iff_not_mem_keys.mp hgm)
    | some v =>
      simp only [GameHoppingSimplifyPMF, StateTSimps, RStateSimplifier, bindSecond]
      exact completePRFCache_diagram_cached X Y st query v hgm

/-- Lift the cached random-function equivalence to indistinguishability. -/
noncomputable def indistinguishable_PRF_ideal_PRF_ideal2 (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    IndistinguishableSingle IndAssumptions.empty
      (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  exact Indistinguishable.of_ObsEq (obsEq_PRF_ideal_PRF_ideal2 X Y)


/-- Ideal random-function oracle, lazy batched cache.
On a query `x` not in the cache, it samples fresh uniform values for every element of the
batch `f x` still missing from the cache, stores them, and returns the value at `x`. -/
noncomputable def PRF_ideal_cache_batch (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (f : X → Finset X) (hf : ∀ x, x ∈ f x) :
    RStateOracle (SecurePRFSpec X Y) where
  stateType := Finmap (fun _x : X => Y)
  initialState := pure ∅
  queries x := by
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

/-- The eagerly sampled random-function oracle and the batched lazy cache are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal_cache_pair (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (f : X → Finset X) (hf : ∀ x, x ∈ f x) :
    ObsEq (PRF_ideal X Y) (PRF_ideal_cache_batch X Y f hf) := by
  obs_eq_by_rand_abstraction ← (completePRFCache X Y)
  case left =>
    -- initialization: the completed empty cache is the uniform random function
    simp only [PRF_ideal, PRF_ideal_cache_batch, PMF.pure_bind]
    convert completePRFCache_empty X Y using 2
    exact PMF.pure_bind _ _
  case right =>
    -- per-query diagram
    simp only [PRF_ideal, PRF_ideal_cache_batch, OracleSpec.Domain, SecurePRFSpec]
    intro query
    ext1 st
    simp only [correctAbstractionDiagSimps, StateTSimps, RStateSimplifier,
      GameHoppingSimplifyPMF, PRF_ideal, PRF_ideal_cache_batch]
    by_cases hq : query ∈ st.keys
    · -- cached branch
      obtain ⟨v, hv⟩ : ∃ v, Finmap.lookup query st = some v :=
        Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr (Finmap.mem_keys.mp hq))
      simp only [hq, dif_pos, hv, Option.getD_some, GameHoppingSimplifyPMF, StateTSimps,
        RStateSimplifier, bindSecond]
      exact completePRFCache_diagram_cached X Y st query v hv
    · -- fresh batched branch
      simp only [hq, dif_neg, not_false_eq_true, GameHoppingSimplifyPMF, StateTSimps,
        RStateSimplifier, StateT.set, bindSecond, liftM, monadLift, MonadLift.monadLift,
        StateT.lift]
      exact completePRFCache_diagram_batch X Y st query ({x' ∈ f query | x' ∉ st.keys})
        (Finset.mem_filter.mpr ⟨hf query, hq⟩) (fun x hx => (Finset.mem_filter.mp hx).2)



def choosePair (b : Bool) (pair : (X × X)) :=
  if b then pair.1 else pair.2

noncomputable def PRF_ideal_cache_batch_pairs (i : ℕ) (Y : Type) [Fintype Y] [Nonempty Y] :
    RStateOracle (SecurePRFSpec (BitVec i.succ) Y) where
  stateType := Finmap (fun _x : (BitVec i) => (Y × Y))
  initialState := pure ∅
  queries x := by
      simp[SecurePRFSpec, OracleSpec.Domain] at x
      exact do
      let c <- get
      let x' := x.extractLsb' 0 i
      if hx : x' ∈ c.keys then
        let value := (c.lookup x').getD (Classical.choice inferInstance)
        return choosePair x[i] value
      else
        let v1 <- PMF.uniformOfFintype Y
        let v2 <- PMF.uniformOfFintype Y
        if x[i] then
          StateT.set (c.insert x' (v1, v2))
        else
          StateT.set (c.insert x' (v2, v1))
        return v1



/-- The eagerly sampled random-function oracle and the batched lazy cache are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal_cache_pairs {i : ℕ} (Y : Type)
     [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal2 (BitVec i.succ) Y) (PRF_ideal_cache_batch_pairs i Y) :=
      by sorry
