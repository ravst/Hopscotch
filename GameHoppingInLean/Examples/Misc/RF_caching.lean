import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finmap
import GameHoppingInLean.Indistinguishability.Def
import GameHoppingInLean.Tactic.Defs
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
    OracleImpl (SecurePRFSpec X Y) where
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
    simp only [correctAbstractionDiagSimps, sStateT, sRState,
      sPMF, PRF_ideal, PRF_ideal2]
    cases hgm : Finmap.lookup query st with
    | none =>
      simp only [sPMF, sStateT, sRState, StateT.set, bindSecond]
      exact completePRFCache_diagram_fresh X Y st query
        (Finmap.lookup_eq_none_iff_not_mem_keys.mp hgm)
    | some v =>
      simp only [sPMF, sStateT, sRState, bindSecond]
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
    OracleImpl (SecurePRFSpec X Y) where
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
    simp only [correctAbstractionDiagSimps, sStateT, sRState,
      sPMF, PRF_ideal, PRF_ideal_cache_batch]
    by_cases hq : query ∈ st.keys
    · -- cached branch
      obtain ⟨v, hv⟩ : ∃ v, Finmap.lookup query st = some v :=
        Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr (Finmap.mem_keys.mp hq))
      simp only [hq, dif_pos, hv, Option.getD_some, sPMF, sStateT,
        sRState, bindSecond]
      exact completePRFCache_diagram_cached X Y st query v hv
    · -- fresh batched branch
      simp only [hq, dif_neg, not_false_eq_true, sPMF, sStateT,
        sRState, StateT.set, bindSecond, liftM, monadLift, MonadLift.monadLift,
        StateT.lift]
      exact completePRFCache_diagram_batch X Y st query ({x' ∈ f query | x' ∉ st.keys})
        (Finset.mem_filter.mpr ⟨hf query, hq⟩) (fun x hx => (Finset.mem_filter.mp hx).2)

def choosePair (b : Bool) (pair : (X × X)) :=
  if b then pair.1 else pair.2

noncomputable def PRF_ideal_cache_batch_pairs (i : ℕ) (Y : Type) [Fintype Y] [Nonempty Y] :
    OracleImpl (SecurePRFSpec (BitVec i.succ) Y) where
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


/-- Reconstruct a `BitVec (i+1)` from its top bit and its low `i` bits. -/
theorem BitVec.cons_getElem_extractLsb'_self (i : ℕ) (x : BitVec (i + 1)) :
    BitVec.cons (x[i]) (x.extractLsb' 0 i) = x := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_cons]
  split
  · next h => subst h; rfl
  · next h =>
    rw [BitVec.getElem_extractLsb' (by omega)]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    simp

/-- Expand a paired cache into an equivalent single-key cache over `BitVec (i+1)`.
A low-bit key `x'` present in the paired cache with pair `(a, b)` becomes the two entries
`cons true x' ↦ a` and `cons false x' ↦ b`; equivalently, the full key `k` is present iff its
low `i` bits are cached, and its value is read off the pair with the top bit `k[i]`. -/
noncomputable def expandPairs {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y]
    (c : Finmap (fun _x : BitVec i => Y × Y)) : Finmap (fun _x : BitVec i.succ => Y) :=
  FinmapFromOptionFun (fun k =>
    if _h : (k.extractLsb' 0 i) ∈ c.keys then
      some (choosePair k[i]
        ((c.lookup (k.extractLsb' 0 i)).getD (Classical.choice inferInstance)))
    else none)

/-- Random abstraction taking a paired-cache state to the uniform completion of the
equivalent single-key cache. -/
noncomputable def completePairsToFun {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y]
    (c : Finmap (fun _x : BitVec i => Y × Y)) : PMF (BitVec i.succ → Y) :=
  completePRFCache (BitVec i.succ) Y (expandPairs Y c)

@[simp] lemma expandPairs_lookup {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y]
    (c : Finmap (fun _x : BitVec i => Y × Y)) (k : BitVec i.succ) :
    (expandPairs Y c).lookup k =
      if _h : (k.extractLsb' 0 i) ∈ c.keys then
        some (choosePair k[i]
          ((c.lookup (k.extractLsb' 0 i)).getD (Classical.choice inferInstance)))
      else none := by
  unfold expandPairs
  rw [FinmapFromOptionFun_lookup]

lemma expandPairs_mem_keys {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y]
    (c : Finmap (fun _x : BitVec i => Y × Y)) (k : BitVec i.succ) :
    k ∈ (expandPairs Y c).keys ↔ (k.extractLsb' 0 i) ∈ c.keys := by
  rw [Finmap.mem_keys, ← Finmap.lookup_isSome, expandPairs_lookup]
  split <;> simp_all

@[simp] lemma expandPairs_empty {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y] :
    expandPairs Y (∅ : Finmap (fun _x : BitVec i => Y × Y)) = ∅ := by
  unfold expandPairs
  simp

lemma completePairsToFun_empty {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y] :
    completePairsToFun Y (∅ : Finmap (fun _x : BitVec i => Y × Y))
      = PMF.uniformOfFintype (BitVec i.succ → Y) := by
  unfold completePairsToFun
  rw [expandPairs_empty, completePRFCache_empty]

@[simp] theorem BitVec.getElem_cons_top (i : ℕ) (b : Bool) (y : BitVec i) :
    (BitVec.cons b y)[i] = b := by
  simp [BitVec.getElem_cons]

@[simp] theorem BitVec.extractLsb'_cons_self (i : ℕ) (b : Bool) (y : BitVec i) :
    (BitVec.cons b y).extractLsb' 0 i = y := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_extractLsb' (by omega), BitVec.getLsbD_eq_getElem (by omega),
    BitVec.getElem_cons, dif_neg (by omega)]
  simp

theorem BitVec.cons_inj_iff (i : ℕ) (b1 b2 : Bool) (y1 y2 : BitVec i) :
    BitVec.cons b1 y1 = BitVec.cons b2 y2 ↔ b1 = b2 ∧ y1 = y2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg (fun v => v[i]) h
      simpa using this
    · have := congrArg (fun v => BitVec.extractLsb' 0 i v) h
      simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

/-- Inserting a pair into the paired cache corresponds, under `expandPairs`, to inserting the
two sibling full keys with the two components of the pair. -/
lemma expandPairs_insert {i : ℕ} (Y : Type) [Fintype Y] [Nonempty Y]
    (st : Finmap (fun _x : BitVec i => Y × Y)) (x' : BitVec i) (p : Y × Y) :
    expandPairs Y (st.insert x' p) =
      ((expandPairs Y st).insert (BitVec.cons true x') p.1).insert (BitVec.cons false x') p.2 := by
  apply Finmap.ext_lookup
  intro k
  have hk : BitVec.cons k[i] (k.extractLsb' 0 i) = k :=
    BitVec.cons_getElem_extractLsb'_self i k
  have hne_tf : (BitVec.cons true x' : BitVec i.succ) ≠ BitVec.cons false x' := by
    intro h; rw [BitVec.cons_inj_iff] at h; exact absurd h.1 (by decide)
  rw [expandPairs_lookup]
  by_cases hyx : k.extractLsb' 0 i = x'
  · -- `k` is one of the two sibling keys `cons k[i] x'`
    rw [dif_pos (by rw [hyx, Finmap.keys_insert]; simp), hyx, Finmap.lookup_insert,
      Option.getD_some]
    rw [hyx] at hk
    cases hbk : k[i] with
    | false =>
      rw [hbk] at hk
      rw [← hk, Finmap.lookup_insert]; rfl
    | true =>
      rw [hbk] at hk
      rw [← hk, Finmap.lookup_insert_of_ne _ hne_tf, Finmap.lookup_insert]; rfl
  · -- `k`'s low bits are not `x'`; it equals neither sibling key
    have hne1 : k ≠ BitVec.cons true x' := by
      intro h; rw [← hk, BitVec.cons_inj_iff] at h; exact hyx h.2
    have hne2 : k ≠ BitVec.cons false x' := by
      intro h; rw [← hk, BitVec.cons_inj_iff] at h; exact hyx h.2
    rw [Finmap.lookup_insert_of_ne _ hne2, Finmap.lookup_insert_of_ne _ hne1,
      expandPairs_lookup]
    by_cases hst : k.extractLsb' 0 i ∈ st.keys
    · rw [dif_pos (by rw [Finmap.keys_insert]; simp [hst]), dif_pos hst,
        Finmap.lookup_insert_of_ne _ hyx]
    · rw [dif_neg (by rw [Finmap.keys_insert]; simp [hyx, hst]), dif_neg hst]

/-- The eagerly sampled random-function oracle and the batched paired lazy cache are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal_cache_pairs' {i : ℕ} (Y : Type)
     [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal (BitVec i.succ) Y) (PRF_ideal_cache_batch_pairs i Y) := by
  symm
  refine correctAbstractionBindImpliesObsEq _ _ (completePairsToFun Y) ?_
  constructor
  · -- initialization
    simp only [PRF_ideal, PRF_ideal_cache_batch_pairs, PMF.pure_bind]
    convert completePairsToFun_empty Y using 2
    exact PMF.pure_bind _ _
  · -- per-query diagram
    intro query
    ext1 st
    simp only [correctAbstractionDiagSimps, sStateT, sRState,
      sPMF, PRF_ideal, PRF_ideal_cache_batch_pairs]
    by_cases hq : query.extractLsb' 0 i ∈ st.keys
    · -- cached branch
      have hv : (expandPairs Y st).lookup query =
          some (choosePair query[i]
            ((st.lookup (query.extractLsb' 0 i)).getD (Classical.choice inferInstance))) := by
        rw [expandPairs_lookup, dif_pos hq]
      simp only [hq, dif_pos, sPMF, sStateT, sRState, bindSecond]
      unfold completePairsToFun
      exact completePRFCache_diagram_cached (BitVec i.succ) Y (expandPairs Y st) query _ hv
    · -- fresh branch
      have hkq : BitVec.cons query[i] (query.extractLsb' 0 i) = query :=
        BitVec.cons_getElem_extractLsb'_self i query
      have h1 : query ∉ (expandPairs Y st).keys := fun h =>
        hq ((expandPairs_mem_keys Y st query).mp h)
      cases hbit : query[i] with
      | true =>
        simp only [hbit, hq, sPMF, sStateT, sRState,
          StateT.set, StateT.bind, bind, StateT.pure, pure, bindSecond, PMF.pure_bind,
          liftM, monadLift, MonadLift.monadLift, StateT.lift, reduceDIte, reduceIte,
          reduceCtorEq, completePairsToFun, expandPairs_insert]
        have hqcons : BitVec.cons true (query.extractLsb' 0 i) = query := by
          rw [← hbit]; exact hkq
        have hne : query ≠ BitVec.cons false (query.extractLsb' 0 i) := by
          rw [← hqcons]; intro h; rw [BitVec.cons_inj_iff] at h; exact absurd h.1 (by decide)
        have h2 : BitVec.cons false (query.extractLsb' 0 i) ∉ (expandPairs Y st).keys := by
          intro h
          have hh := (expandPairs_mem_keys Y st _).mp h
          rw [BitVec.extractLsb'_cons_self] at hh
          exact hq hh
        simp only [hqcons]
        exact completePRFCache_diagram_fresh2' (BitVec i.succ) Y (expandPairs Y st) query
          (BitVec.cons false (query.extractLsb' 0 i)) hne h1 h2
      | false =>
        simp only [hbit, hq, sPMF, sStateT, sRState,
          StateT.set, StateT.bind, bind, StateT.pure, pure, bindSecond, PMF.pure_bind,
          liftM, monadLift, MonadLift.monadLift, StateT.lift, reduceDIte, reduceIte,
          reduceCtorEq, completePairsToFun, expandPairs_insert]
        have hqcons : BitVec.cons false (query.extractLsb' 0 i) = query := by
          rw [← hbit]; exact hkq
        have hct : BitVec.cons true (query.extractLsb' 0 i) ≠ query := by
          rw [← hqcons]; intro h; rw [BitVec.cons_inj_iff] at h; exact absurd h.1 (by decide)
        have h2 : BitVec.cons true (query.extractLsb' 0 i) ∉ (expandPairs Y st).keys := by
          intro h
          have hh := (expandPairs_mem_keys Y st _).mp h
          rw [BitVec.extractLsb'_cons_self] at hh
          exact hq hh
        have hcomm : ∀ a a_1 : Y,
            ((expandPairs Y st).insert (BitVec.cons true (query.extractLsb' 0 i)) a_1).insert query a
              = ((expandPairs Y st).insert query a).insert
                  (BitVec.cons true (query.extractLsb' 0 i)) a_1 :=
          fun _ _ => Finmap.insert_insert_of_ne _ hct
        simp only [hqcons, hcomm]
        exact completePRFCache_diagram_fresh2 (BitVec i.succ) Y (expandPairs Y st) query
          (BitVec.cons true (query.extractLsb' 0 i)) (Ne.symm hct) h1 h2

/-- The eagerly sampled random-function oracle and the batched lazy cache are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal_cache_pairs {i : ℕ} (Y : Type)
     [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal2 (BitVec i.succ) Y) (PRF_ideal_cache_batch_pairs i Y) :=
  obsEq_trans (ObsEq.symm (obsEq_PRF_ideal_PRF_ideal2 (BitVec i.succ) Y))
    (obsEq_PRF_ideal_PRF_ideal_cache_pairs' Y)
