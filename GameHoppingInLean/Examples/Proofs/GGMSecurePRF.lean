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


def BitVec.flipMsb {k : ℕ} (v : BitVec k.succ) : BitVec k.succ :=
  v ^^^ BitVec.ofNat k.succ (2 ^ k)

@[simp] theorem BitVec.flipMsb_ne_self {k : ℕ} (v : BitVec k.succ) :
    v.flipMsb ≠ v := by
  intro h
  have hbit := congrArg (fun z : BitVec k.succ => z.getLsbD k) h
  have hmask : (BitVec.ofNat k.succ (2 ^ k)).getLsbD k = true := by
    simp [BitVec.getLsbD_ofNat]
  change (v ^^^ BitVec.ofNat k.succ (2 ^ k)).getLsbD k = v.getLsbD k at hbit
  rw [BitVec.getLsbD_xor, hmask, Bool.xor_true] at hbit
  cases v.getLsbD k <;> simp at hbit

@[simp] theorem BitVec.flipMsb_flipMsb {k : ℕ} (v : BitVec k.succ) :
    v.flipMsb.flipMsb = v := by
  simp [BitVec.flipMsb, BitVec.xor_assoc]

@[simp] theorem BitVec.extractLsb'_zero_flipMsb {k : ℕ} (v : BitVec k.succ) :
    BitVec.extractLsb' 0 k v.flipMsb = BitVec.extractLsb' 0 k v := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_extractLsb']
  rw [BitVec.getElem_extractLsb']
  unfold BitVec.flipMsb
  rw [BitVec.getLsbD_xor]
  have hmask : (BitVec.ofNat k.succ (2 ^ k)).getLsbD j = false := by
    have hne : k ≠ j := by omega
    simp [BitVec.getLsbD_ofNat, Nat.testBit_two_pow, hne]
  simp [hmask]

@[simp] theorem BitVec.getLsbD_flipMsb_msb {k : ℕ} (v : BitVec k.succ) :
    v.flipMsb.getLsbD k = !v.getLsbD k := by
  change (v ^^^ BitVec.ofNat k.succ (2 ^ k)).getLsbD k = !v.getLsbD k
  rw [BitVec.getLsbD_xor]
  have hmask : (BitVec.ofNat k.succ (2 ^ k))[k] = true := by
    simp [BitVec.getLsbD_ofNat]
  simp [hmask]

@[simp] theorem BitVec.getElem_flipMsb_msb {k : ℕ} (v : BitVec k.succ) :
    v.flipMsb[k] = !v[k] := by
  simpa [BitVec.getLsbD_eq_getElem (x := v.flipMsb) (i := k) (h := by omega),
    BitVec.getLsbD_eq_getElem (x := v) (i := k) (h := by omega)] using
    BitVec.getLsbD_flipMsb_msb v

theorem BitVec.eq_or_eq_flipMsb_of_extractLsb'_eq {k : ℕ} {x q : BitVec k.succ}
    (h : BitVec.extractLsb' 0 k x = BitVec.extractLsb' 0 k q) :
    x = q ∨ x = q.flipMsb := by
  by_cases htop : x[k] = q[k]
  · left
    apply BitVec.eq_of_getElem_eq
    intro j hj
    by_cases hjk : j = k
    · subst j
      exact htop
    · have hjlt : j < k := by omega
      have hbits := congrArg (fun v : BitVec k => v[j]) h
      simpa [BitVec.getElem_extractLsb'] using hbits
  · right
    apply BitVec.eq_of_getElem_eq
    intro j hj
    by_cases hjk : j = k
    · subst j
      cases hx : x[k] <;> cases hq : q[k] <;> simp [hx, hq] at htop ⊢
    · have hjlt : j < k := by omega
      have hbits := congrArg (fun v : BitVec k => v[j]) h
      have hbits' : x.getLsbD j = q.getLsbD j := by
        simpa [BitVec.getElem_extractLsb'] using hbits
      have hflip' : q.flipMsb.getLsbD j = q.getLsbD j := by
        change (q ^^^ BitVec.ofNat k.succ (2 ^ k)).getLsbD j = q.getLsbD j
        rw [BitVec.getLsbD_xor]
        have hmask : (BitVec.ofNat k.succ (2 ^ k)).getLsbD j = false := by
          have hne : k ≠ j := by omega
          simp [BitVec.getLsbD_ofNat, Nat.testBit_two_pow, hne]
        simp [hmask]
      rw [← BitVec.getLsbD_eq_getElem (x := x) (i := j) (h := hj),
        ← BitVec.getLsbD_eq_getElem (x := q.flipMsb) (i := j) (h := hj)]
      exact hbits'.trans hflip'.symm

@[simp] theorem BitVec.extractLsb'_zero_extractLsb'_zero {n m l : ℕ} (hml : m ≤ l)
    (v : BitVec n) :
    BitVec.extractLsb' 0 m (BitVec.extractLsb' 0 l v) =
      BitVec.extractLsb' 0 m v := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_eq_getElem (h := by omega)]
  rw [BitVec.getElem_extractLsb']
  rw [BitVec.getElem_extractLsb']
  simp

@[simp] theorem BitVec.extractLsb'_extractLsb' {n : ℕ}
    {start len innerStart innerLen : ℕ} (h : start + len ≤ innerLen)
    (v : BitVec n) :
    BitVec.extractLsb' start len (BitVec.extractLsb' innerStart innerLen v) =
      BitVec.extractLsb' (innerStart + start) len v := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_eq_getElem (h := by omega)]
  rw [BitVec.getElem_extractLsb']
  rw [BitVec.getElem_extractLsb']
  congr 1
  omega

/-- The sibling pair that should be sampled together when moving from depth `i`
to depth `i + 1`. -/
noncomputable def GGMHybrid2_Vs_3_batch {n : ℕ} (i : Fin n) :
    BitVec i.succ.1 → Finset (BitVec i.succ.1) :=
  fun x => {x, x.flipMsb}

@[simp] theorem GGMHybrid2_Vs_3_batch_self {n : ℕ} (i : Fin n)
    (x : BitVec i.succ.1) : x ∈ GGMHybrid2_Vs_3_batch i x := by
  simp [GGMHybrid2_Vs_3_batch]

@[simp] theorem GGMHybrid2_Vs_3_batch_flip {n : ℕ} (i : Fin n)
    (x : BitVec i.succ.1) : x.flipMsb ∈ GGMHybrid2_Vs_3_batch i x := by
  simp [GGMHybrid2_Vs_3_batch]

theorem PMF.bind_uniformOfFintype_bitVec_swap_append_do
    {k : ℕ} {α : Type} (f : BitVec (k + k) → PMF α) :
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec k)
      let x₂ ← PMF.uniformOfFintype (BitVec k)
      f (x₂ ++ x₁)) =
    (do
      let x ← PMF.uniformOfFintype (BitVec (k + k))
      f x) := by
  change (PMF.uniformOfFintype (BitVec k)).bind
      (fun x₁ => (PMF.uniformOfFintype (BitVec k)).bind
        (fun x₂ => f (x₂ ++ x₁))) =
    (PMF.uniformOfFintype (BitVec (k + k))).bind f
  rw [← PMF.uniformOfFintype_prod_bind
    (f := fun p : BitVec k × BitVec k => f (p.2 ++ p.1))]
  exact (PMF.bind_uniformOfFintype_equiv
    (e := (Equiv.prodComm (BitVec k) (BitVec k)).trans (RState.bitVecAppendEquiv k k))
    (g := f)).symm

noncomputable def PRF_ideal_cache_batch_flipMsb (i : ℕ) (Y : Type) [Fintype Y] [Nonempty Y] :
    RStateOracle (SecurePRFSpec (BitVec i.succ) Y) where
  stateType := Finmap (fun _x : (BitVec i.succ) => Y)
  initialState := pure ∅
  queries := {
    impl := fun u x =>
      letI : DecidableEq ((SecurePRFSpec (BitVec i.succ) Y).domain u) := by
        simp [SecurePRFSpec, OracleSpec.domain]
        exact inferInstance
      do
      let c <- get
      if x ∈ c.keys then
        return (c.lookup x).getD (Classical.choice inferInstance)
      else
        let v1 <- PMF.uniformOfFintype Y
        let v2 <- PMF.uniformOfFintype Y
        let newVals := (Finmap.insert x v1 ∅).insert x.flipMsb v2
        StateT.set (c ∪ newVals)
        return v1
  }

noncomputable def PRF_ideal_cache_batch_flipMsb2 (i : ℕ) (k : ℕ)  :
    RStateOracle (SecurePRFSpec (BitVec i.succ) (BitVec k)) where
  stateType := Finmap (fun _x : (BitVec i) => BitVec (k + k))
  initialState := pure ∅
  queries := {
    impl := fun _ x => by
      simp[SecurePRFSpec, OracleSpec.domain] at x
      exact do
      let c <- get
      let x' := x.extractLsb' 0 i
      if hx : x' ∈ c.keys then
        let value := (c.lookup x').getD (Classical.choice inferInstance)
        return PRG.chooseHalfI value (x[i])
      else
        let v1 <- PMF.uniformOfFintype (BitVec k)
        let v2 <- PMF.uniformOfFintype (BitVec k)
        if x[i] then
          StateT.set (c.insert x' (v1 ++ v2))
        else
          StateT.set (c.insert x' (v2 ++ v1))
        return v1
  }

theorem obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb (i k : ℕ) :
    ObsEq
      (PRF_ideal_cache_batch_flipMsb2 i k)
      (PRF_ideal_cache_batch_flipMsb i (BitVec k)) := by
  refine correctAbstractionImpliesObsEq _ _ ?_ ?_
  · simp [PRF_ideal_cache_batch_flipMsb2, PRF_ideal_cache_batch_flipMsb]
    intro fmap
    exact FinmapFromOptionFun fun x : BitVec i.succ =>
      (fmap.lookup (BitVec.extractLsb' 0 i x)).map fun label =>
        PRG.chooseHalfI label x[i]
  · constructor <;> simp [PRF_ideal_cache_batch_flipMsb2, PRF_ideal_cache_batch_flipMsb]
    simp [OracleSpec.domain, SecurePRFSpec]
    intro _ q
    ext1 st
    simp [StateT.run, StateT.get, StateT.set, mapOutputState, mapInputState]
    simp only [GameHoppingSimplifyPMF]
    generalize hm : Finmap.lookup (BitVec.extractLsb' 0 i q) st = m
    cases m with
    | none =>
      rw [ite_cond_eq_false]
      · simp
        simp only [GameHoppingSimplifyPMF]
        split_ifs with hqi
        · simp [StateT.set, StateT.run]
          simp only [GameHoppingSimplifyPMF]
          congr 1
          ext1 a
          congr 1
          ext1 b
          congr 3
          ext1 x
          by_cases hqx : x = q
          · subst hqx
            simp [hm]
            rw [ite_cond_eq_false]
            · simp [hqi, PRG.chooseHalfI]
            · simp
              intro h
              exact BitVec.flipMsb_ne_self x h.symm
          · by_cases hfqx : x = q.flipMsb
            · rw [hfqx]
              rw [BitVec.extractLsb'_zero_flipMsb]
              simp [hm, hqi, PRG.chooseHalfI]
            · have hparent_ne :
                  BitVec.extractLsb' 0 i x ≠ BitVec.extractLsb' 0 i q := by
                intro hparent
                rcases BitVec.eq_or_eq_flipMsb_of_extractLsb'_eq hparent with h | h
                · exact hqx h
                · exact hfqx h
              rw [Finmap.lookup_insert_of_ne st hparent_ne]
              cases hlook : Finmap.lookup (BitVec.extractLsb' 0 i x) st with
              | none =>
                  simp [hlook]
                  symm
                  simpa [hfqx] using
                    (Finmap.lookup_insert_of_ne
                      (s := (∅ : Finmap (fun _x : BitVec (i + 1) => BitVec k)))
                      (a := q) (a' := x) (b := a) hqx)
              | some label =>
                  simp [hlook]
        · simp [StateT.set, StateT.run]
          simp only [GameHoppingSimplifyPMF]
          simp at hqi
          congr 1
          ext1 a
          congr 1
          ext1 b
          congr 3
          ext1 x
          by_cases hqx : x = q
          · subst hqx
            simp [hm]
            rw [ite_cond_eq_false]
            · simp [hqi, PRG.chooseHalfI]
            · simp
              intro h
              exact BitVec.flipMsb_ne_self x h.symm
          · by_cases hfqx : x = q.flipMsb
            · rw [hfqx]
              rw [BitVec.extractLsb'_zero_flipMsb]
              simp [hm, hqi, PRG.chooseHalfI]
            · have hparent_ne :
                  BitVec.extractLsb' 0 i x ≠ BitVec.extractLsb' 0 i q := by
                intro hparent
                rcases BitVec.eq_or_eq_flipMsb_of_extractLsb'_eq hparent with h | h
                · exact hqx h
                · exact hfqx h
              rw [Finmap.lookup_insert_of_ne st hparent_ne]
              cases hlook : Finmap.lookup (BitVec.extractLsb' 0 i x) st with
              | none =>
                  simp [hlook]
                  symm
                  simpa [hfqx] using
                    (Finmap.lookup_insert_of_ne
                      (s := (∅ : Finmap (fun _x : BitVec (i + 1) => BitVec k)))
                      (a := q) (a' := x) (b := a) hqx)
              | some label =>
                  simp [hlook]
      · have hnot : BitVec.extractLsb' 0 i q ∉ st.keys := by
          rw [Finmap.mem_keys]
          exact Finmap.lookup_eq_none.mp hm
        simp [hnot]
    | some x =>
      rw [ite_cond_eq_true]
      · simp[hm]
      · simp
        apply Finmap.mem_of_lookup_eq_some
        assumption

lemma Finmap.union_insert_mem {X : Type} [DecidableEq X] {f : X → Type} (m1 m2 : Finmap f) (x : X) (v : f x)
  (hx : x ∈ m1.keys):
  m1 ∪ (m2.insert x v) = m1 ∪ m2 := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y ∈ m1
  · rw [Finmap.lookup_union_left hy, Finmap.lookup_union_left hy]
  · rw [Finmap.lookup_union_right hy, Finmap.lookup_union_right hy]
    by_cases hyx : y = x
    · subst y
      exfalso
      exact hy (by simpa [Finmap.mem_keys] using hx)
    · rw [Finmap.lookup_insert_of_ne m2 hyx]

lemma Finmap.union_insert_not_mem {X : Type} [DecidableEq X] {f : X → Type} (m1 m2 : Finmap f) (x : X) (v : f x)
  (hx : x ∉  m1.keys) :
  m1 ∪ (m2.insert x v) = (m1.insert x v) ∪ m2 := by
  apply Finmap.ext_lookup
  intro y
  by_cases hyx : y = x
  · subst y
    have hnot : x ∉ m1 := by
      rwa [← Finmap.mem_keys]
    rw [Finmap.lookup_union_right hnot]
    rw [Finmap.lookup_union_left]
    · simp
    · rw [Finmap.mem_insert]
      exact Or.inl rfl
  · by_cases hy : y ∈ m1
    · have hyInsert : y ∈ m1.insert x v := by
        rw [Finmap.mem_insert]
        exact Or.inr hy
      rw [Finmap.lookup_union_left hy, Finmap.lookup_union_left hyInsert]
      rw [Finmap.lookup_insert_of_ne m1 hyx]
    · have hyInsert : y ∉ m1.insert x v := by
        rw [Finmap.mem_insert]
        exact fun h => h.elim hyx hy
      rw [Finmap.lookup_union_right hy, Finmap.lookup_union_right hyInsert]
      rw [Finmap.lookup_insert_of_ne m2 hyx]

def batch_new_vals_bij_mem {l k : ℕ } (c : Finmap (fun _ : BitVec l.succ => BitVec k)) (x : BitVec l.succ ) (h_non_mem : x ∉ c.keys) (hf_mem: x.flipMsb ∈ c.keys) :
({ x_1 // x_1 ∈ ({x' ∈ {x, x.flipMsb} | x' ∉ c.keys} : Finset (BitVec l.succ)) } → BitVec k) ≃ BitVec k where
  toFun f := f ⟨x, by simp; assumption⟩
  invFun e := fun _ => e
  left_inv := by
    simp [Function.LeftInverse]
    intro f
    ext1 ⟨x₁, hx₁⟩
    simp at hx₁
    cases hx₁.1
    next h => simp [h]
    next h => subst h; exfalso; apply hx₁.2; assumption
  right_inv := by
     simp [Function.LeftInverse, Function.RightInverse]

def batch_new_vals_bij_not_mem {l k : ℕ } (c : Finmap (fun _ : BitVec l.succ => BitVec k)) (x : BitVec l.succ ) (h_non_mem : x ∉ c.keys) (hf_not_mem: x.flipMsb ∉ c.keys) :
({ x_1 // x_1 ∈ ({x' ∈ {x, x.flipMsb} | x' ∉ c.keys} : Finset (BitVec l.succ)) } → BitVec k) ≃ BitVec k × BitVec k where
  toFun f := ⟨f ⟨x, by simp; assumption⟩, f ⟨x.flipMsb, by simp; assumption⟩⟩
  invFun e := fun a =>
    if a = x then e.1 else e.2
  left_inv := by
    intro f
    funext a
    rcases a with ⟨y, hy⟩
    simp at hy
    rcases hy.1 with hyx | hyflip
    · subst y
      simp
    · subst y
      simp
  right_inv := by
    intro e
    rcases e with ⟨a, b⟩
    simp [BitVec.flipMsb_ne_self]

@[simp]
lemma Finmap.from_fun_lookup (X' : Finset X) (f : X' → Y) (elem : X) [DecidableEq X]:
  (FinmapFromFun X' f).lookup elem =
    if he : elem ∈ X' then
      Option.some (f ⟨elem, he⟩)
    else
      Option.none := by
  by_cases he : elem ∈ X'
  · simp [he, FinmapFromFun_lookup]
  · rw [dif_neg he]
    exact Finmap.lookup_eq_none.mpr (by
      rw [← Finmap.mem_keys]
      simp [he])

@[simp]
lemma Finmap.from_fun_in (X' : Finset X) (f : X' → Y) (elem : X) [DecidableEq X]:
  (elem ∈ (FinmapFromFun X' f)) ↔ elem ∈ X' := by
  rw [← Finmap.mem_keys]
  simp

theorem obsEq_PRF_ideal_cache_batch_flipMsb_GGMHybrid2_Vs_3_batch {k n : ℕ}
    (i : Fin n) :
    ObsEq
      (PRF_ideal_cache_batch_flipMsb i.1 (BitVec k))
      (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
        (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)) := by
  apply obsEqReflexive
  simp [PRF_ideal_cache_batch_flipMsb, PRF_ideal_cache_batch]
  ext1 _
  ext1 x
  congr
  ext1 c
  ext1 st
  split_ifs with hif <;> try rfl
  simp [GGMHybrid2_Vs_3_batch, StateT.run, Function.comp]
  simp only [GameHoppingSimplifyPMF]
  by_cases hflip : x.flipMsb ∈ c.keys
  · conv_lhs =>
      simp [StateT.set]
      enter [2, a, 2, b, 1]
      rw [Finmap.union_insert_mem, Finmap.union_insert_not_mem]
      · rfl
      · tactic => assumption
      · tactic => assumption
    simp
    rw [← PMF.map_uniformOfFintype_equiv (batch_new_vals_bij_mem c x hif hflip).symm ]
    simp [StateT.set]
    simp only [GameHoppingSimplifyPMF, StateT.set]
    congr 1
    ext1 a
    simp [batch_new_vals_bij_mem]
    congr 2
    apply Finmap.ext_lookup
    intro x1
    by_cases hx1 : x = x1
    · subst hx1
      simp
      rw[Finmap.lookup_union_right]
      · simp
        assumption
      · exact hif
    · rw [Finmap.lookup_insert_of_ne]
      · rw [Finmap.lookup_union_left_of_not_in]
        simp
        intro h
        cases h
        next h' =>
          exfalso
          apply hx1
          symm
          assumption
        next h' =>
          subst h'
          assumption
      · symm
        assumption
  · conv_lhs =>
      simp [StateT.set]
      enter [2, a, 2, b, 1]
      rw [Finmap.union_insert_not_mem, Finmap.union_insert_not_mem]
      · rfl
      · tactic =>
          simp
          constructor <;> try assumption
          intro h
          exact BitVec.flipMsb_ne_self x h.symm
      · tactic => assumption
    simp only [GameHoppingSimplifyPMF]
    rw [← PMF.map_uniformOfFintype_equiv (batch_new_vals_bij_not_mem c x hif hflip).symm ]
    simp [StateT.set, batch_new_vals_bij_not_mem]
    simp only [GameHoppingSimplifyPMF, StateT.set]
    congr
    ext1 a
    congr
    ext1 b
    congr 2
    apply Finmap.ext_lookup
    intro e
    by_cases hex : e = x
    · subst hex
      simp
      rw [Finmap.lookup_union_right]
      simp
      assumption
      apply hif
    · rw [Finmap.lookup_insert_of_ne] <;> try assumption
      by_cases hex2 : e = x.flipMsb
      · subst hex2
        simp
        rw [Finmap.lookup_union_right] <;> try exact hflip
        simp
        assumption
      · rw [Finmap.lookup_insert_of_ne] <;> try assumption
        rw [Finmap.lookup_union_left_of_not_in]
        simp
        intro h
        exfalso
        cases h <;> contradiction

/-- Final bridge from the batch-cached random function view to the paired-label
`GGMHybrid3` view. This is the remaining randomization-shift lemma: the batch relation
will eventually cache both children of a depth-`i` node, and this lemma will identify
that cache with the `BitVec (k + k)` parent-label cache. -/
theorem obsEq_GGMHybrid2_Vs_3_batch_bridge {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq
      (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
        (PRF_ideal_cache_batch_flipMsb2 i.1 k))
      (GGMHybrid3 prg i) := by
  simp [applySRReduction, GGMHybridStepReduction2RF, GGMHybrid3, PRF_ideal_cache_batch_flipMsb2]
  refine correctAbstractionImpliesObsEq _ _ (fun (a,b) => b) ?_
  constructor
  · simp
  · simp [OracleComp.simulateQ, OracleSpec.domain, SecurePRFSpec]
    intro _ query
    ext1 st
    simp [mapOutputState, mapInputState, StateT.get, StateT.set, StateT.run, PMF.map]
    generalize Hm : Finmap.lookup (BitVec.extractLsb' 0 (↑i) query) st.2 = m
    cases m with
    | none =>
      simp []
      rw [ite_cond_eq_false]
      · simp
        simp only [GameHoppingSimplifyPMF]
        by_cases hqi : query[i.val]
        · simp only [GameHoppingSimplifyPMF, hqi, PRG.chooseHalfI]
          simp
          simp only [GameHoppingSimplifyPMF]
          conv_rhs =>
            rw [← PMF.bind_uniformOfFintype_bitVec_append_do]
          simp
          simp only [GameHoppingSimplifyPMF]
          congr
          ext1 a
          congr
          ext1 b
          congr 3
          rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
          congr 1
        · simp at hqi
          simp only [GameHoppingSimplifyPMF, hqi, PRG.chooseHalfI]
          conv_rhs =>
            rw [← PMF.bind_uniformOfFintype_bitVec_swap_append_do]
          simp
          simp only [GameHoppingSimplifyPMF]
          congr
          ext1 a
          congr
          ext1 b
          congr 3
          rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
          congr 1
      ·
        have hnot : BitVec.extractLsb' 0 i.1 query ∉ st.2.keys := by
          rw [Finmap.mem_keys]
          exact Finmap.lookup_eq_none.mp Hm
        simp [hnot]

    | some x =>
      simp
      rw [ite_cond_eq_true]
      · simp
        simp only [GameHoppingSimplifyPMF]
        congr 1
        rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
        simp [Hm]
        rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
        congr
      ·
        have hin : BitVec.extractLsb' 0 i.1 query ∈ st.2.keys := by
          rw [Finmap.mem_keys]
          exact Finmap.mem_of_lookup_eq_some Hm
        simp [hin]

/-- The `GGMHybrid2`/`GGMHybrid3` bridge as a symbolic indistinguishability object.

This is intentionally phrased as an `IndistinguishableI` chain rather than a direct
`ObsEq`, so the step can be assembled from the cached-random-function equivalences and
the stateful reduction that embeds the depth-`i+1` random function into the outer PRF
game. -/
noncomputable def indistinguishableI_GGMHybrid2_Vs_3
    {Reductions : IndistinguishabilityReductions}
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    (κ : ℕ)
    (hRi2 : GGMHybridStepReduction2RF prg i.succ ∈ Reductions.reductions _ _) :
    IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
      (SecurePRFSpec (BitVec n) (BitVec k))
      (GGMHybrid2 prg i.succ)
      (GGMHybrid3 prg i) := by
  let hLeft :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (GGMHybrid2 prg i.succ)
        (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal2 (BitVec i.succ.1) (BitVec k))) :=
    Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_reduction_rf prg i.succ)
  let hRF₁ :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec i.succ.1) (BitVec k))
        (PRF_ideal2 (BitVec i.succ.1) (BitVec k))
        (PRF_ideal (BitVec i.succ.1) (BitVec k)) :=
    Indistinguishable.symmetric
      (indistinguishable_PRF_ideal_PRF_ideal2
        (Reductions := Reductions) (BitVec i.succ.1) (BitVec k) κ)
  let hRF₂ :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec i.succ.1) (BitVec k))
        (PRF_ideal (BitVec i.succ.1) (BitVec k))
        (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
          (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)) :=
    Indistinguishable.of_ObsEq
      (obsEq_PRF_ideal_PRF_ideal_cache_pair
        (BitVec i.succ.1) (BitVec k)
        (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i))
  let hRF :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec i.succ.1) (BitVec k))
        (PRF_ideal2 (BitVec i.succ.1) (BitVec k))
        (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
          (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)) :=
    calc
      PRF_ideal2 (BitVec i.succ.1) (BitVec k)
          ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
              SecurePRFSpec (BitVec i.succ.1) (BitVec k)]
        PRF_ideal (BitVec i.succ.1) (BitVec k) := hRF₁
      _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
              SecurePRFSpec (BitVec i.succ.1) (BitVec k)]
        PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
          (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i) := hRF₂
  let hMiddle :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal2 (BitVec i.succ.1) (BitVec k)))
        (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
            (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i))) :=
    IndistinguishableI.reduction (r := GGMHybridStepReduction2RF prg i.succ) none hRF hRi2
  let hRight :
      IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
        (SecurePRFSpec (BitVec n) (BitVec k))
        (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
            (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)))
        (GGMHybrid3 prg i) :=
    let hBatchFlip :
        IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
          (SecurePRFSpec (BitVec n) (BitVec k))
          (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
            (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
              (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)))
          (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
            (PRF_ideal_cache_batch_flipMsb i.1 (BitVec k))) :=
      IndistinguishableI.reduction (r := GGMHybridStepReduction2RF prg i.succ) none
        (Indistinguishable.symmetric
          (Indistinguishable.of_ObsEq
            (obsEq_PRF_ideal_cache_batch_flipMsb_GGMHybrid2_Vs_3_batch (k := k) i)))
        hRi2
    let hFlipFlip2 :
        IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
          (SecurePRFSpec (BitVec n) (BitVec k))
          (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
            (PRF_ideal_cache_batch_flipMsb i.1 (BitVec k)))
          (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
            (PRF_ideal_cache_batch_flipMsb2 i.1 k)) :=
      IndistinguishableI.reduction (r := GGMHybridStepReduction2RF prg i.succ) none
        (Indistinguishable.symmetric
          (Indistinguishable.of_ObsEq
            (obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb i.1 k)))
        hRi2
    let hFlip2GGM :
        IndistinguishableI IndistinguishabilityAssumptions.empty Reductions κ none
          (SecurePRFSpec (BitVec n) (BitVec k))
          (applySRReduction (GGMHybridStepReduction2RF prg i.succ)
            (PRF_ideal_cache_batch_flipMsb2 i.1 k))
          (GGMHybrid3 prg i) :=
      Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_Vs_3_batch_bridge prg i)
    calc
      applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
            (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i))
          ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
              SecurePRFSpec (BitVec n) (BitVec k)]
        applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal_cache_batch_flipMsb i.1 (BitVec k)) := hBatchFlip
      _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
              SecurePRFSpec (BitVec n) (BitVec k)]
        applySRReduction (GGMHybridStepReduction2RF prg i.succ)
          (PRF_ideal_cache_batch_flipMsb2 i.1 k) := hFlipFlip2
      _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
              SecurePRFSpec (BitVec n) (BitVec k)]
        GGMHybrid3 prg i := hFlip2GGM
  calc
    GGMHybrid2 prg i.succ
        ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2RF prg i.succ)
        (PRF_ideal2 (BitVec i.succ.1) (BitVec k)) := hLeft
    _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      applySRReduction (GGMHybridStepReduction2RF prg i.succ)
        (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
          (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)) := hMiddle
    _ ≈ᵢ[IndistinguishabilityAssumptions.empty, Reductions, κ, none,
            SecurePRFSpec (BitVec n) (BitVec k)]
      GGMHybrid3 prg i := hRight


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
    (hRi2 : GGMHybridStepReduction2RF prg i.succ ∈ Reductions.reductions _ _)
    :
    Indistinguishable (SecurePRGAssumption' prg) Reductions
      (GGMHybrid2 prg i.castSucc)
      (GGMHybrid2 prg i.succ) := by
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
      (liftEmpty (indistinguishableI_GGMHybrid2_Vs_3
        (Reductions := Reductions) prg i κ hRi2))
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
      (Reductions := Reductions) prg i hRi (hStep2 i.succ) κ
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
