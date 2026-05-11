import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRG
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF
import GameHoppingInLean.Examples.Constructions.GGM
import GameHoppingInLean.Examples.Misc.RF_caching
import GameHoppingInLean.Misc.PMFLemmas

section
attribute [-simp] bind_pure_comp
open scoped IndistinguishableI

/-- The `i`-th hybrid for the GGM proof.

The oracle samples a uniformly random label for every depth-`i` node in the GGM tree.
On input `x`, it reads the first `i` bits in the same LSB-first order used by `applyPRGs`,
looks up the corresponding random label, and then evaluates the remaining suffix with `prg`. -/
noncomputable def GGMHybrid {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := BitVec i.1 → BitVec k
  initialState := PMF.uniformOfFintype (BitVec i.1 → BitVec k)
  queries := {
    impl := fun _ x => do
      let labels ← get
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg (labels nodeBits) remainingBits)
  }

/-- The real GGM oracle is the first hybrid. -/
theorem obsEq_real_GGMHybrid_zero {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (PRF_real (GGM prg n)) (GGMHybrid prg 0) := by
  apply ObsEq.symm
  let e : (BitVec 0 → BitVec k) ≃ BitVec k :=
    {
      toFun := fun labels => labels 0
      invFun := fun seed _ => seed
      left_inv := by
        intro labels
        funext x
        have hx : x = 0 := Subsingleton.elim x 0
        rw [hx]
      right_inv := by
        intro seed
        rfl
    }
  refine mapStateBijImpliesObsEq (GGMHybrid prg 0) (PRF_real (GGM prg n)) e ?_ ?_
  · simp [GGMHybrid, PRF_real, GGM]
    simp only [PMF.map_uniformOfFintype_equiv]
  · intro i query
    ext seed
    simp [RState.mapStateBij, PRF_real, GGMHybrid, GGM, e]

/-- The final GGM hybrid is the ideal random-function oracle. -/
theorem obsEq_GGMHybrid_last_ideal {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (GGMHybrid prg (Fin.last n)) (PRF_ideal (BitVec n) (BitVec k)) := by
  apply obsEqReflexive
  simp [GGMHybrid, PRF_ideal]
  constructor
  · ext f
    simp [PMF.uniformOfFintype_apply]
  · funext i query labels
    simp
    have : n - n = 0 := by omega
    rw [this]
    simp [applyPRGs]

noncomputable def GGMHybrid2 {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec k)
  initialState := pure ∅
  queries := {
    impl := fun _ x => do
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let labels ← (do
        let state <- get
        match state.lookup nodeBits with
        | some x => return x
        | none =>
          let out <- PMF.uniformOfFintype (BitVec k)
          let state' := state.insert nodeBits out
          set state'
          return out
        )
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg labels remainingBits)

  }

noncomputable def GGMHybrid3 {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec (k + k))
  initialState := pure ∅
  queries := {
    impl := fun _ x => do
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let labels ← (do
        let state <- get
        match state.lookup nodeBits with
        | some x => return x
        | none =>
          let out <- PMF.uniformOfFintype (BitVec (k+k))
          let state' := state.insert nodeBits out
          set state'
          return out
        )
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      let choosenLabel := PRG.chooseHalfI labels (remainingBits.getLsbD 0)
      pure (applyPRGs prg choosenLabel (BitVec.extractLsb' 1 (n-i.1-1) remainingBits))
  }


/-- Skeleton reduction for one adjacent hybrid step in the GGM proof.

The intended implementation should:
1. maintain a cache of labels for depth-`i+1` nodes,
2. query the underlying PRG challenger once per unseen depth-`i` prefix, and
3. interpret the challenge output as the two child labels for that prefix. -/
noncomputable def GGMHybridStepReduction2PRG {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    SRReduction (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec (k+k))
  initialState := pure ∅
  queries := { impl := fun _ x => do
    let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
    let labels : BitVec (k+k) ← (
      do
        let state <- srGet!
        match state.lookup nodeBits with
        | some x => return x
        | none =>
          let out : BitVec (k+k) <- srQuery((), ())
          let state' := state.insert nodeBits out
          srSet(state')
          return out
      )
    let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
    let choosenHalf := PRG.chooseHalfI labels (remainingBits.getLsbD 0)
    let output : BitVec k := applyPRGs prg choosenHalf (BitVec.extractLsb' 1 (n-i.1-1) remainingBits)
    return output
  }


noncomputable def GGMHybridStepReduction2RF {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    SRReduction (SecurePRFSpec (BitVec i.1) (BitVec k)) (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun _ x => do
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let fNodeBits <- srQuery((), nodeBits)
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg fNodeBits remainingBits)
  }

/-- Consecutive GGM hybrids differ by one use of the underlying PRG. -/
-- easy
theorem obsEq_GGMHybrid_reduction_rf {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    ObsEq (GGMHybrid prg i)
      (applySRReduction (GGMHybridStepReduction2RF prg i) (PRF_ideal (BitVec i.1) (BitVec k))) := by
  apply ObsEq.symm
  let e :
      (applySRReduction (GGMHybridStepReduction2RF prg i)
        (PRF_ideal (BitVec i.1) (BitVec k))).stateType ≃
        (GGMHybrid prg i).stateType :=
    {
      toFun := fun st => st.2
      invFun := fun labels => ((), labels)
      left_inv := by
        intro st
        cases st.1
        rfl
      right_inv := by
        intro labels
        rfl
    }
  refine mapStateBijImpliesObsEq
    (applySRReduction (GGMHybridStepReduction2RF prg i)
      (PRF_ideal (BitVec i.1) (BitVec k)))
    (GGMHybrid prg i)
    e ?_ ?_
  · ext labels
    simp [applySRReduction, GGMHybridStepReduction2RF, GGMHybrid, PRF_ideal, e,
      PMF.map_bind, PMF.uniformOfFintype_apply]
  · intro _ query
    ext1 st
    simp [RState.mapStateBij, applySRReduction, GGMHybridStepReduction2RF,
      GGMHybrid, PRF_ideal, e, query_impl_convert, OracleComp.simulateQ]
    unfold RState.mapStateBij
    simp [StateT.run]

-- easy/medium
theorem obsEq_GGMHybrid2_reduction_rf {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    ObsEq (GGMHybrid2 prg i)
      (applySRReduction (GGMHybridStepReduction2RF prg i) (PRF_ideal2 (BitVec i.1) (BitVec k))) := by
  apply ObsEq.symm
  let e :
      (applySRReduction (GGMHybridStepReduction2RF prg i)
        (PRF_ideal2 (BitVec i.1) (BitVec k))).stateType ≃
        (GGMHybrid2 prg i).stateType :=
    {
      toFun := fun st => st.2
      invFun := fun labels => ((), labels)
      left_inv := by
        intro st
        cases st.1
        rfl
      right_inv := by
        intro labels
        rfl
    }
  refine mapStateBijImpliesObsEq _ _ e ?_ ?_
  · ext labels
    simp [applySRReduction, GGMHybridStepReduction2RF, GGMHybrid2, PRF_ideal2, e,
      PMF.map_bind, PMF.uniformOfFintype_apply]
  · intro _ query
    ext1 st
    simp [RState.mapStateBij, applySRReduction, GGMHybridStepReduction2RF,
      GGMHybrid2, PRF_ideal2, e, query_impl_convert, OracleComp.simulateQ]
    unfold RState.mapStateBij
    simp [StateT.run, StateT.set]
    generalize hm : Finmap.lookup (BitVec.extractLsb' 0 (↑i) query) st = m
    cases m with
    | none =>
      simp
      simp [StateT.run, StateT.set]
    | some m => simp

/-- Replacing the embedded PRG call with uniform randomness advances the hybrid by one level. -/
noncomputable def obsEq_rand_GGMHybrid_1_2 {Reductions : IndistinguishabilityReductions} {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n+1)) :
    (GGMHybridStepReduction2RF prg i ∈ Reductions.reductions _ _) ->
    Indistinguishable IndistinguishabilityAssumptions.empty Reductions
      (GGMHybrid prg i)
      (GGMHybrid2 prg i) := by
  intro hRed κ
  let hLeft :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid prg i)
        (applySRReduction (GGMHybridStepReduction2RF prg i)
          (PRF_ideal (BitVec i.1) (BitVec k))) :=
    Indistinguishable.of_ObsEq (obsEq_GGMHybrid_reduction_rf prg i)
  let hRF :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec i.1) (BitVec k))
        (PRF_ideal (BitVec i.1) (BitVec k))
        (PRF_ideal2 (BitVec i.1) (BitVec k)) :=
    indistinguishable_PRF_ideal_PRF_ideal2
      (Reductions := Reductions) (BitVec i.1) (BitVec k) κ
  let hMiddle :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2RF prg i)
          (PRF_ideal (BitVec i.1) (BitVec k)))
        (applySRReduction (GGMHybridStepReduction2RF prg i)
          (PRF_ideal2 (BitVec i.1) (BitVec k))) :=
    IndistinguishableI.reduction (r := GGMHybridStepReduction2RF prg i) none hRF hRed
  let hRight :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2RF prg i)
          (PRF_ideal2 (BitVec i.1) (BitVec k)))
        (GGMHybrid2 prg i) :=
    Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_reduction_rf prg i))
  calc
    GGMHybrid prg i
        ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2RF prg i)
        (PRF_ideal (BitVec i.1) (BitVec k)) := hLeft
    _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2RF prg i)
        (PRF_ideal2 (BitVec i.1) (BitVec k)) := hMiddle
    _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid2 prg i := hRight


noncomputable def Finmap.getWithProof {α : Type u} {β : α → Type v} [DecidableEq α]
    (m : Finmap β) (x : α) (hx : x ∈ m.keys) : β x :=
  Classical.choose (Finmap.mem_iff.mp (Finmap.mem_keys.mp hx))

noncomputable def Finmap.funToFinMap {X : Type u} {Y : Type v} [DecidableEq X]
    {S : Finset X} (f : S → Y) : Finmap (fun _ : X => Y) :=
  Finmap.keysLookupEquiv.symm
    ⟨(S, fun x => if h : x ∈ S then some (f ⟨x, h⟩) else none),
      by
        intro x
        by_cases h : x ∈ S <;> simp [h]⟩

@[simp] theorem Finmap.lookup_funToFinMap {X : Type u} {Y : Type v} [DecidableEq X]
    {S : Finset X} (f : S → Y) (x : X) :
    (Finmap.funToFinMap f).lookup x =
      if h : x ∈ S then some (f ⟨x, h⟩) else none := by
  simp [Finmap.funToFinMap]

@[simp] theorem Finmap.funToFinMap_empty {X : Type u} {Y : Type v} [DecidableEq X]
    (f : (∅ : Finset X) → Y) :
    Finmap.funToFinMap f = (∅ : Finmap (fun _ : X => Y)) := by
  apply Finmap.ext_lookup
  intro x
  simp

@[simp] theorem Finmap.keys_insert_union {X : Type u} {Y : Type v} [DecidableEq X]
    (st : Finmap (fun _ : X => Y)) (query : X) (a : Y) :
    (st.insert query a).keys = st.keys ∪ ({query} : Finset X) := by
  ext x
  simp [Finmap.mem_keys, Finmap.mem_insert, eq_comm, or_comm]

def BitVec.flipLsb {i : ℕ} (x : BitVec i.succ) : BitVec i.succ :=
  (BitVec.extractLsb' 1 i x).concat (!x.getLsbD 0)

@[simp] private lemma BitVec.extractLsb'_one_concat {i : ℕ} (x : BitVec i) (b : Bool) :
    BitVec.extractLsb' 1 i (x.concat b) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_concat, hn]

@[simp] private lemma BitVec.extractLsb'_one_extractLsb'_zero_succ
    {n i : ℕ} (x : BitVec n) :
    BitVec.extractLsb' 1 i (BitVec.extractLsb' 0 (i + 1) x) =
      BitVec.extractLsb' 0 i x := by
  sorry

@[simp] private lemma BitVec.flipLsb_concat_false {i : ℕ} (x : BitVec i) :
    BitVec.flipLsb (x.concat false) = x.concat true := by
  simp [BitVec.flipLsb]

@[simp] private lemma BitVec.flipLsb_concat_true {i : ℕ} (x : BitVec i) :
    BitVec.flipLsb (x.concat true) = x.concat false := by
  simp [BitVec.flipLsb]

@[simp] private lemma BitVec.flipLsb_flipLsb {i : ℕ} (x : BitVec i.succ) :
    x.flipLsb.flipLsb = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [BitVec.flipLsb, BitVec.getLsbD_concat]
  · have hn' : n - 1 < i := by omega
    have hnidx : 1 + (n - 1) = n := by omega
    simp [BitVec.flipLsb, BitVec.getLsbD_concat, BitVec.getLsbD_extractLsb',
      hn0, hn', hnidx]

private noncomputable def missingAfterInsertKeysEquiv {i k : ℕ}
    (st : Finmap (fun _ : BitVec i.succ => BitVec k))
    (query : BitVec i.succ) (a : BitVec k) :
    ({ x : BitVec i.succ //
        x ∉ (st.insert query a).keys ∧ x.flipLsb ∈ (st.insert query a).keys } →
        BitVec k) ≃
      ({ x : BitVec i.succ //
        x ∉ st.keys ∪ ({query} : Finset (BitVec i.succ)) ∧
          x.flipLsb ∈ st.keys ∪ ({query} : Finset (BitVec i.succ)) } → BitVec k) :=
  Equiv.arrowCongr
    (Equiv.subtypeEquivRight fun x => by
      simp [Finmap.keys_insert_union, and_comm, and_left_comm, and_assoc,
        or_comm, or_left_comm, or_assoc])
    (Equiv.refl (BitVec k))

private lemma uniform_missingAfterInsertKeys {i k : ℕ}
    (st : Finmap (fun _ : BitVec i.succ => BitVec k))
    (query : BitVec i.succ) (a : BitVec k) :
    PMF.uniformOfFintype
        ({ x : BitVec i.succ //
          x ∉ (st.insert query a).keys ∧ x.flipLsb ∈ (st.insert query a).keys } →
          BitVec k)
      =
    (PMF.uniformOfFintype
        ({ x : BitVec i.succ //
          x ∉ st.keys ∪ ({query} : Finset (BitVec i.succ)) ∧
            x.flipLsb ∈ st.keys ∪ ({query} : Finset (BitVec i.succ)) } →
          BitVec k)).map
      (missingAfterInsertKeysEquiv st query a).symm := by
  exact (PMF.map_uniformOfFintype_equiv
    (missingAfterInsertKeysEquiv st query a).symm).symm

private noncomputable def missingBeforeInsertSplitEquiv {i k : ℕ}
    (st : Finmap (fun _ : BitVec i.succ => BitVec k))
    (query : BitVec i.succ)
    (hquery : query ∉ st.keys)
    (hsibling : query.flipLsb ∈ st.keys) :
    ({ x : BitVec i.succ // x ∉ st.keys ∧ x.flipLsb ∈ st.keys } → BitVec k) ≃
      BitVec k ×
        ({ x : BitVec i.succ //
          x ∉ st.keys ∪ ({query} : Finset (BitVec i.succ)) ∧
            x.flipLsb ∈ st.keys ∪ ({query} : Finset (BitVec i.succ)) } → BitVec k) where
  toFun f :=
    ⟨f ⟨query, hquery, hsibling⟩,
      fun x => f ⟨x.1, by
        exact (Finset.not_mem_union.mp x.2.1).1,
        by
          rcases Finset.mem_union.mp x.2.2 with hflip | hflip
          · exact hflip
          · exfalso
            have hxflip : x.1.flipLsb = query := by simpa using hflip
            have hx : x.1 = query.flipLsb := by
              calc
                x.1 = x.1.flipLsb.flipLsb := by simp
                _ = query.flipLsb := by rw [hxflip]
            exact (Finset.not_mem_union.mp x.2.1).1 (by simpa [hx] using hsibling)⟩⟩
  invFun p x :=
    if hx : x.1 = query then
      p.1
    else
      p.2 ⟨x.1, by
        constructor
        · exact Finset.not_mem_union.mpr ⟨x.2.1, by simpa using hx⟩
        · exact Finset.mem_union.mpr (Or.inl x.2.2)⟩
  left_inv f := by
    funext x
    by_cases hx : x.1 = query
    · subst hx
      simp
    · simp [hx]
  right_inv p := by
    rcases p with ⟨v, g⟩
    apply Prod.ext
    · simp
    · funext x
      have hx : x.1 ≠ query := by
        intro hx
        exact (Finset.not_mem_union.mp x.2.1).2 (by simpa [hx])
      simp [hx]

private lemma uniform_missingBeforeInsertSplit {i k : ℕ}
    (st : Finmap (fun _ : BitVec i.succ => BitVec k))
    (query : BitVec i.succ)
    (hquery : query ∉ st.keys)
    (hsibling : query.flipLsb ∈ st.keys) :
    (PMF.uniformOfFintype
        ({ x : BitVec i.succ // x ∉ st.keys ∧ x.flipLsb ∈ st.keys } → BitVec k)).map
      (missingBeforeInsertSplitEquiv st query hquery hsibling)
      =
    PMF.uniformOfFintype
      (BitVec k ×
        ({ x : BitVec i.succ //
          x ∉ st.keys ∪ ({query} : Finset (BitVec i.succ)) ∧
            x.flipLsb ∈ st.keys ∪ ({query} : Finset (BitVec i.succ)) } → BitVec k)) := by
  exact PMF.map_uniformOfFintype_equiv
    (missingBeforeInsertSplitEquiv st query hquery hsibling)

noncomputable
def abstractionGGMHybird_2_to_3 {i k : ℕ} (f : Finmap (fun _ : BitVec (i.succ) ↦ BitVec k)) : PMF (Finmap (fun _ : BitVec i ↦ BitVec (k+k))) := by
  classical
  exact do
    let missing :=  { x : (BitVec i.succ) // x ∉ f.keys ∧ x.flipLsb ∈ f.keys}
    let missingVals <- PMF.uniformOfFintype (missing → BitVec k)
    let definedKeys : Finset (BitVec i) := f.keys.image (fun y => BitVec.extractLsb' 1 i y)
    -- let defined := { x : BitVec i // x ∈ definedKeys }
    let definedVals (d : definedKeys) : BitVec (k + k) :=
      let x := d.1
      let x0 : BitVec i.succ := x.concat false
      let x1 : BitVec i.succ := x.concat true
      if h0 : x0 ∈ f.keys then
        if h1 : x1 ∈ f.keys then
          (Finmap.getWithProof f x0 h0).append (Finmap.getWithProof f x1 h1)
        else
          (Finmap.getWithProof f x0 h0).append
            (missingVals ⟨x1, h1, by simpa [BitVec.flipLsb, x0, x1] using h0⟩)
      else
        if h1 : x1 ∈ f.keys then
          (missingVals ⟨x0, h0, by simpa [BitVec.flipLsb, x0, x1] using h1⟩).append
            (Finmap.getWithProof f x1 h1)
        else
          BitVec.ofNat (k + k) 0
    pure (Finmap.funToFinMap definedVals)

-- hard, notrvial randomization shifts.
theorem obsEq_GGMHybrid2_Vs_3 {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (GGMHybrid2 prg (i.succ)) (GGMHybrid3 prg i) := by
  refine correctAbstractionBindImpliesObsEq _ _
    abstractionGGMHybird_2_to_3 ?_
  constructor
  · simp [GGMHybrid2, GGMHybrid3, abstractionGGMHybird_2_to_3, GGMHybrid2]
  · intro idx query
    ext1 st
    --simp [GGMHybrid2] at st
    simp [SecurePRFSpec, abstractionGGMHybird_2_to_3, bindInputState, bindOutputState, StateT.run, GGMHybrid2, GGMHybrid3, bindSecond]
    simp [OracleSpec.domain, SecurePRFSpec] at query
    simp only [GameHoppingSimplifyPMF]
    generalize hm : Finmap.lookup (BitVec.extractLsb' 0 (↑(i.succ)) query) st = m
    cases m with
    | none =>
      simp at hm
      simp [hm]
      simp only [GameHoppingSimplifyPMF]
      have hUniform (a : BitVec k) := by
        exact uniform_missingAfterInsertKeys st
          (BitVec.extractLsb' 0 (↑(i.succ)) query) a
      simp at hUniform
      conv_lhs =>
        enter [2, a, 1]
        rw [hUniform a]
      clear hUniform
      simp only [GameHoppingSimplifyPMF]
      let q : BitVec (↑(i.succ)) := BitVec.extractLsb' 0 (↑(i.succ)) query
      have hqNotMem : q ∉ st.keys := by
        intro hq
        exact (Finmap.lookup_eq_none.mp hm) (Finmap.mem_keys.mp hq)
      by_cases hParent :
          ∃ a ∈ Finmap.keys st,
            BitVec.extractLsb' 1 (↑i) a = BitVec.extractLsb' 0 (↑i) query
      · have hsibling : q.flipLsb ∈ st.keys := by
          rcases hParent with ⟨a, haMem, haPrefix⟩
          have ha_ne_q : a ≠ q := by
            intro ha
            exact hqNotMem (by simpa [q, ha] using haMem)
          have ha_eq_flip : a = q.flipLsb := by
            -- `a` has the same parent prefix as `q`; since `q ∉ st.keys` but
            -- `a ∈ st.keys`, the low bit must be the opposite one.
            sorry
          simpa [ha_eq_flip] using haMem
        conv_rhs =>
          change (PMF.uniformOfFintype
            ({ x : BitVec (↑(i.succ)) //
              x ∉ st.keys ∧ x.flipLsb ∈ st.keys } → BitVec k)).bind _
          erw [PMF.bind_uniformOfFintype_equiv
            (e := (missingBeforeInsertSplitEquiv st q hqNotMem hsibling).symm)]
          rw [PMF.uniformOfFintype_prod_bind]
        simp only [GameHoppingSimplifyPMF]
        congr 1
        ext1 a
        congr 1
        ext1 f
        simp





        sorry
      ·
        sorry
    | some x => sorry

    -- generalize hm : Finmap.lookup (BitVec.extractLsb' 0 (↑(i.succ)) query) st = m








-- easy, just definition
-- swap PMF.uniform (BitVec k k) into ideal prg randomness
theorem obsEq_GGMHybrid2_applyStepReduction_real {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (GGMHybrid3 prg i)
      (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k)) := by
  let e :
      (GGMHybrid3 prg i).stateType ≃
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k)).stateType :=
    {
      toFun := fun labels => (labels, ())
      invFun := fun st => st.1
      left_inv := by
        intro labels
        rfl
      right_inv := by
        intro st
        cases st.2
        rfl
    }
  refine mapStateBijImpliesObsEq
    (GGMHybrid3 prg i)
    (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k))
    e ?_ ?_
  · simp [applySRReduction, GGMHybridStepReduction2PRG, GGMHybrid3, PRG_rand, e]
  · intro _ query
    ext1 st
    rcases st with ⟨cache, u⟩
    cases u
    simp [RState.mapStateBij, applySRReduction, GGMHybridStepReduction2PRG,
      GGMHybrid3, PRG_rand, e, query_impl_convert, OracleComp.simulateQ]
    unfold RState.mapStateBij
    simp [StateT.run, StateT.set]
    generalize hm : Finmap.lookup (BitVec.extractLsb' 0 (↑i) query) cache = m
    cases m with
    | none =>
        simp [hm, StateT.run, StateT.set]
        simp only [GameHoppingSimplifyPMF]
        simp [StateT.run, StateT.set, set]
        rfl
    | some m =>
        simp

def Finmap.mapKeys (s : Finmap (fun _ : α => β)) (f : β → γ) : Finmap (fun _ : α => γ) where
  entries := s.entries.map (fun x => ⟨x.1, f x.2⟩)
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    simpa [Multiset.keys] using s.nodupKeys.nodup_keys

@[simp]
theorem Finmap.mapKeys_empty (f : β → γ) :
    Finmap.mapKeys (∅ : Finmap (fun _ : α => β)) f = ∅ := by
  rfl

@[simp]
theorem Finmap.lookup_mapKeys [DecidableEq α]
    (m : Finmap (fun _ : α => β)) (f : β → γ) (x : α) :
    (Finmap.mapKeys m f).lookup x = (m.lookup x).map f := by
  rcases m with ⟨⟨l⟩, hl⟩
  exact List.dlookup_map₂ (γ := fun _ : α => β) (δ := fun _ : α => γ) (f := fun _ => f) x

@[simp]
theorem Finmap.mapKeys_insert [DecidableEq α]
    (m : Finmap (fun _ : α => β)) (f : β → γ) (x : α) (v : β) :
    Finmap.mapKeys (m.insert x v) f = (Finmap.mapKeys m f).insert x (f v) := by
  apply Finmap.ext_lookup
  intro y
  by_cases h : y = x
  · subst y
    simp
  · simp [h]

-- by correct abstraction, we map each seed in cache to its prgs.
theorem obsEq_applyStepReduction_rand_GGMHybrid2 {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg))
      (GGMHybrid2 prg i.castSucc) := by
  apply ObsEq.symm
  refine correctAbstractionImpliesObsEq _ _ (?_) (?_)
  · simp[applySRReduction, GGMHybridStepReduction2PRG, GGMHybrid2, PRG_real]
    intro f
    exact ⟨(Finmap.mapKeys f prg.draw), ()⟩
  · constructor
    · simp [GGMHybrid2, applySRReduction, GGMHybridStepReduction2PRG, PRG_real]
    · intro i_1 query
      cases i_1
      simp [OracleSpec.domain, SecurePRFSpec] at query
      simp [GGMHybrid2, applySRReduction, GGMHybridStepReduction2PRG, PRG_real,
            mapOutputState, mapInputState]
      ext1 st
      simp [mapOutputState, mapInputState, mapSecond, StateT.run, OracleComp.simulateQ, FreeMonad.roll, FreeMonad.mapM]
      generalize hm : Finmap.lookup (BitVec.extractLsb' 0 (↑i) query) st = m
      cases m with
      | none =>
        simp
        simp only [GameHoppingSimplifyPMF]
        simp
        simp only [GameHoppingSimplifyPMF]
        congr 1
        ext1 a
        congr 2
        rw [applyPRGs.eq_def]
        generalize hk : n - i = k
        cases k with
        | zero => omega
        | succ k'=> simp
      | some x =>
        simp
        congr 2
        rw [applyPRGs.eq_def]
        generalize hk : n - i = k
        cases k with
        | zero => omega
        | succ k'=> simp

/-- One hybrid step is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def GGMHybrid2_step_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    (hRi : GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    -- (hRi2 : GGMHybridStepReduction2RF prg i.castSucc ∈ Reductions.reductions _ _)
    :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid2 prg i.castSucc)
      (GGMHybrid2 prg i.succ) := by
  intro κ
  let hLeft :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid2 prg i.castSucc)
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg)) :=
    Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_applyStepReduction_rand_GGMHybrid2 prg i))
  let hPRG :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRGSpec k k) (PRG_real prg) (PRG_rand k k) := by
    simpa [SecurePRGAssumption', SecurePRGAssumptionFull, SecurePRGAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := SecurePRGAssumption' prg)
        (Reductions := Reductions) (κ := κ) (q_b := none) ())
  let hMiddle :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg))
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k)) :=
    IndistinguishableI.reduction (r := GGMHybridStepReduction2PRG prg i) none hPRG hRi
  let hRight₁ :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k))
        (GGMHybrid3 prg i) :=
    Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_applyStepReduction_real prg i))
  let hRight₂ :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid3 prg i)
        (GGMHybrid2 prg i.succ) :=
    Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_Vs_3 prg i))
  calc
    GGMHybrid2 prg i.castSucc
        ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_real prg) := hLeft
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2PRG prg i) (PRG_rand k k) := hMiddle
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid3 prg i := hRight₁
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid2 prg i.succ := hRight₂

noncomputable def GGMHybrid_step_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    (hRi : GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    (hStep2 : ∀ i : Fin (n+1),
      GGMHybridStepReduction2RF prg i ∈ Reductions.reductions _ _) :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid prg i.castSucc)
      (GGMHybrid prg i.succ) := by
  intro κ
  let liftEmpty :
      {q_b : ENat} → {I : Type} → {O : OracleSpec I} →
      {ro₁ ro₂ : RStateOracle O} →
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ q_b O ro₁ ro₂ →
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ q_b O ro₁ ro₂ := by
    intro q_b I O ro₁ ro₂ h
    induction h with
    | assumption i =>
        cases i
    | obsEqB q_b hObs =>
        exact IndistinguishableI.obsEqB q_b hObs
    | simpleReduction r q_b h hRed ih =>
        exact IndistinguishableI.simpleReduction r q_b ih hRed
    | reduction r q_b h hRed ih =>
        exact IndistinguishableI.reduction r q_b ih hRed
    | complexInitReduction r q_b h hRed ih =>
        exact IndistinguishableI.complexInitReduction r q_b ih hRed
    | randReduction r q_b h hRed ih =>
        exact IndistinguishableI.randReduction r q_b ih hRed
    | symm q_b h ih =>
        exact IndistinguishableI.symm q_b ih
    | trans ro₂ q_b h₁ h₂ ih₁ ih₂ =>
        exact IndistinguishableI.trans ro₂ q_b ih₁ ih₂
    | longSequence l q_b ro hStep ih =>
        exact IndistinguishableI.longSequence l q_b ro (fun i hi => ih i hi)
  let hLeft :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid prg i.castSucc)
        (GGMHybrid2 prg i.castSucc) :=
    liftEmpty (obsEq_rand_GGMHybrid_1_2 prg i.castSucc (hStep2 i.castSucc) κ)
  let hMiddle :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid2 prg i.castSucc)
        (GGMHybrid2 prg i.succ) :=
    GGMHybrid2_step_indistinguishable_of_securePRG
      (Reductions := Reductions) prg i hRi κ
  let hRight :
      IndistinguishableI (SecurePRGAssumption' prg) Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid2 prg i.succ)
        (GGMHybrid prg i.succ) :=
    Indistinguishable.symmetric
      (liftEmpty (obsEq_rand_GGMHybrid_1_2 prg i.succ (hStep2 i.succ) κ))
  calc
    GGMHybrid prg i.castSucc
        ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid2 prg i.castSucc := hLeft
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid2 prg i.succ := hMiddle
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid prg i.succ := hRight

noncomputable def GGMHybrids_indistinguishable_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k)
    (hStep : ∀ i : Fin n,
      GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    (hStep2 : ∀ i : Fin (n+1),
      GGMHybridStepReduction2RF prg i ∈ Reductions.reductions _ _) :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid prg 0)
      (GGMHybrid prg (Fin.last n)) := by
  intro κ
  refine Indistinguishable.long_step n
    (fun j => GGMHybrid prg ⟨j.1, ?_⟩)
    (GGMHybrid prg 0)
    (GGMHybrid prg (Fin.last n))
    (by rfl)
    (by rfl)
    ?_
  · exact Finset.mem_range.mp j.2
  · intro i hi
    simp [ro_seq_fixed]
    exact GGMHybrid_step_indistinguishable_of_securePRG
      (Reductions := Reductions) prg ⟨i, hi⟩ (hStep ⟨i, hi⟩) hStep2 κ

/-- GGM is secure assuming the underlying length-doubling PRG is secure, given the
reduction memberships used by the hybrid argument. -/
noncomputable def secureGGM_of_securePRG
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k)
    (hStep : ∀ i : Fin n,
      GGMHybridStepReduction2PRG prg i ∈ Reductions.reductions _ _)
    (hStep2 : ∀ i : Fin (n+1),
      GGMHybridStepReduction2RF prg i ∈ Reductions.reductions _ _) :
    SecurePRFDef (SecurePRGAssumption' prg) Reductions (GGM prg n) := by
  intro κ
  calc
    PRF_real (GGM prg n)
        ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid prg 0 :=
        Indistinguishable.of_ObsEq (obsEq_real_GGMHybrid_zero prg)
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid prg (Fin.last n) :=
        (GGMHybrids_indistinguishable_of_securePRG
          (Reductions := Reductions) prg hStep hStep2) κ
    _ ≈ᵢ[SecurePRGAssumption' prg, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      PRF_ideal (BitVec n) (BitVec k) :=
        Indistinguishable.of_ObsEq (obsEq_GGMHybrid_last_ideal prg)

-- end
