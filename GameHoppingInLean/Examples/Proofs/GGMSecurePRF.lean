import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRG
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF
import GameHoppingInLean.Examples.Constructions.GGM
import GameHoppingInLean.Examples.Misc.RF_caching
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.BitVec.Simprocs


section
attribute [-simp] bind_pure_comp
open scoped IndistinguishableI
open scoped OracleReduction


/-- Any indistinguishability that holds under the empty assumption set holds under
any assumption set. -/
noncomputable def liftEmptyAssumptions
    {Assumptions : IndistinguishabilityAssumptions}
    {q_b : ENat} {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (h : IndistinguishableI IndistinguishabilityAssumptions.empty q_b O ro₁ ro₂) :
    IndistinguishableI Assumptions q_b O ro₁ ro₂ := by
  induction h with
  | assumption i => exact i.elim
  | obsEqB q hObs => exact IndistinguishableI.obsEqB q hObs
  | complexInitReduction r q h ih => exact IndistinguishableI.complexInitReduction r q ih
  | symm q h ih => exact IndistinguishableI.symm q ih
  | trans ro₂ q h₁ h₂ ih₁ ih₂ => exact IndistinguishableI.trans ro₂ q ih₁ ih₂
  | longSequence l q ro hStep ih =>
      exact IndistinguishableI.longSequence l q ro (fun j hj => ih j hj)

/-- The `i`-th hybrid for the GGM proof.

The oracle samples a uniformly random label for every depth-`i` node in the GGM tree.
On input `x`, it reads the first `i` bits in the same LSB-first order used by `applyPRGs`,
looks up the corresponding random label, and then evaluates the remaining suffix with `prg`. -/
noncomputable def GGMHybrid {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := BitVec i.1 → BitVec k
  initialState := PMF.uniformOfFintype (BitVec i.1 → BitVec k)
  queries x := do
      let labels ← get
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg (labels nodeBits) remainingBits)



attribute [local game_hopping_unfold]
  GGMHybrid PRF_real GGM PRF_ideal applyPRGs

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
  obs_eq_by_abstraction e

/-- The final GGM hybrid is the ideal random-function oracle. -/
theorem obsEq_GGMHybrid_last_ideal {k n : ℕ} (prg : lengthDoublingPRG k) :
    ObsEq (GGMHybrid prg (Fin.last n)) (PRF_ideal (BitVec n) (BitVec k)) := by
  apply obsEqReflexive
  simp [OracleReductionSimps, StateTSimps, RStateSimplifier,
    GameHoppingSimplifyPMF, game_hopping_unfold]
  constructor
  · ext f
    simp [PMF.uniformOfFintype_apply]
  · funext query labels
    have : n - n = 0 := by omega
    rw [this]
    simp [applyPRGs]


noncomputable def GGMHybrid2 {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec k)
  initialState := pure ∅
  queries x := do
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


noncomputable def GGMHybrid3 {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    RStateOracle (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec (k + k))
  initialState := pure ∅
  queries x := do
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


/-- Skeleton reduction for one adjacent hybrid step in the GGM proof.

The intended implementation should:
1. maintain a cache of labels for depth-`i+1` nodes,
2. query the underlying PRG challenger once per unseen depth-`i` prefix, and
3. interpret the challenge output as the two child labels for that prefix. -/
noncomputable def GGMHybridStepReduction2PRG {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    OracleReduction (SecurePRGSpec k k) (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Finmap (fun _x : BitVec i.1 => BitVec (k+k))
  initialState := pure ∅
  queries x := do
    let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
    let labels : BitVec (k+k) ← (
      do
        let state <- orGet!
        match state.lookup nodeBits with
        | some x => return x
        | none =>
          let out : BitVec (k+k) <- orQuery(())
          let state' := state.insert nodeBits out
          orSet(state')
          return out
      )
    let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
    let choosenHalf := PRG.chooseHalfI labels (remainingBits.getLsbD 0)
    let output : BitVec k := applyPRGs prg choosenHalf (BitVec.extractLsb' 1 (n-i.1-1) remainingBits)
    return output


noncomputable def GGMHybridStepReduction2RF {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    OracleReduction (SecurePRFSpec (BitVec i.1) (BitVec k)) (SecurePRFSpec (BitVec n) (BitVec k)) where
  stateType := Unit
  initialState := pure ()
  queries x := do
      let nodeBits : BitVec (i.1) := BitVec.extractLsb' 0 i.1 x
      let fNodeBits <- orQuery(nodeBits)
      let remainingBits : BitVec (n - i.1) := BitVec.extractLsb' i.1 (n - i.1) x
      pure (applyPRGs prg fNodeBits remainingBits)


attribute [local game_hopping_unfold]
  GGMHybrid2 GGMHybrid3 GGMHybridStepReduction2PRG GGMHybridStepReduction2RF
  PRF_ideal2 PRG_real PRG_rand PRF_ideal_cache_batch
/-- Consecutive GGM hybrids differ by one use of the underlying PRG. -/
-- easy
theorem obsEq_GGMHybrid_reduction_rf {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    ObsEq (GGMHybrid prg i)
      ((GGMHybridStepReduction2RF prg i) ◇ (PRF_ideal (BitVec i.1) (BitVec k))) := by
  apply ObsEq.symm
  let e :
      ((GGMHybridStepReduction2RF prg i) ◇
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
  obs_eq_by_abstraction e
  simp [e, game_hopping_unfold]
  congr 1
  exact Subsingleton.elim _ _

-- easy/medium
theorem obsEq_GGMHybrid2_reduction_rf {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    ObsEq (GGMHybrid2 prg i)
      ((GGMHybridStepReduction2RF prg i) ◇ (PRF_ideal2 (BitVec i.1) (BitVec k))) := by
  obs_eq_by_abstraction ← (fun st => st.2)
  rename_i q _ _ st
  cases Finmap.lookup (BitVec.extractLsb' 0 (↑i) (⟨q⟩ : BitVec n)) st <;> rfl

/-- Replacing the embedded PRG call with uniform randomness advances the hybrid by one level. -/
noncomputable def obsEq_rand_GGMHybrid_1_2 {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    Indistinguishable IndistinguishabilityAssumptions.empty
      (GGMHybrid prg i)
      (GGMHybrid2 prg i) := by
  game_hopping [
    GGMHybrid prg i,
    (GGMHybridStepReduction2RF prg i) ◇ (PRF_ideal (BitVec i.1) (BitVec k)),
    (GGMHybridStepReduction2RF prg i) ◇ (PRF_ideal2 (BitVec i.1) (BitVec k)),
    GGMHybrid2 prg i]
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid_reduction_rf prg i)
  · exact IndistinguishableI.complexInitReduction (GGMHybridStepReduction2RF prg i) none
      (indistinguishable_PRF_ideal_PRF_ideal2 (BitVec i.1) (BitVec k))
  · exact Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_reduction_rf prg i))


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
    (e := (Equiv.prodComm (BitVec k) (BitVec k)).trans (bitVecAppendEquiv k k))
    (g := f)).symm

/-- `PMF.bind`-form of `bind_uniformOfFintype_bitVec_append_do`. -/
theorem pmfBind_uniform_bitVec_append {a b : ℕ} {α : Type} (f : BitVec (a + b) → PMF α) :
    (PMF.uniformOfFintype (BitVec a)).bind (fun x₁ =>
      (PMF.uniformOfFintype (BitVec b)).bind (fun x₂ => f (x₁ ++ x₂))) =
    (PMF.uniformOfFintype (BitVec (a + b))).bind f := by
  have h := bind_uniformOfFintype_bitVec_append_do (a := a) (b := b) f
  simpa only [pmf_monad_bind_eq_bind] using h

/-- `PMF.bind`-form of `PMF.bind_uniformOfFintype_bitVec_swap_append_do`. -/
theorem pmfBind_uniform_bitVec_swap_append {k : ℕ} {α : Type} (f : BitVec (k + k) → PMF α) :
    (PMF.uniformOfFintype (BitVec k)).bind (fun x₁ =>
      (PMF.uniformOfFintype (BitVec k)).bind (fun x₂ => f (x₂ ++ x₁))) =
    (PMF.uniformOfFintype (BitVec (k + k))).bind f := by
  have h := PMF.bind_uniformOfFintype_bitVec_swap_append_do f
  simpa only [pmf_monad_bind_eq_bind] using h

noncomputable def PRF_ideal_cache_batch_flipMsb (i : ℕ) (Y : Type) [Fintype Y] [Nonempty Y] :
    RStateOracle (SecurePRFSpec (BitVec i.succ) Y) where
  stateType := Finmap (fun _x : (BitVec i.succ) => Y)
  initialState := pure ∅
  queries x :=
      letI : DecidableEq ((SecurePRFSpec (BitVec i.succ) Y).Domain) := by
        simp [SecurePRFSpec, OracleSpec.Domain]
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

noncomputable def PRF_ideal_cache_batch_flipMsb2 (i : ℕ) (k : ℕ) :
    RStateOracle (SecurePRFSpec (BitVec i.succ) (BitVec k)) where
  stateType := Finmap (fun _x : (BitVec i) => BitVec (k + k))
  initialState := pure ∅
  queries x := by
      simp[SecurePRFSpec, OracleSpec.Domain] at x
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

/-- Abstraction from the paired parent-label cache (`flipMsb2`) to the per-child cache
(`flipMsb`): a parent `x'` holding `w : BitVec (k+k)` corresponds to its two children,
each holding the appropriate half `PRG.chooseHalfI w b`. -/
noncomputable def expandCache (i k : ℕ)
    (m : Finmap (fun _ : BitVec i => BitVec (k + k))) :
    Finmap (fun _ : BitVec (i + 1) => BitVec k) :=
  FinmapFromOptionFun (fun y : BitVec (i + 1) =>
    (m.lookup (BitVec.extractLsb' 0 i y)).map (fun w => PRG.chooseHalfI w (y[i])))

@[simp] lemma expandCache_lookup (i k : ℕ)
    (m : Finmap (fun _ : BitVec i => BitVec (k + k))) (y : BitVec (i + 1)) :
    (expandCache i k m).lookup y =
      (m.lookup (BitVec.extractLsb' 0 i y)).map (fun w => PRG.chooseHalfI w (y[i])) := by
  rw [expandCache, FinmapFromOptionFun_lookup]

@[simp] lemma expandCache_mem (i k : ℕ)
    (m : Finmap (fun _ : BitVec i => BitVec (k + k))) (y : BitVec (i + 1)) :
    y ∈ (expandCache i k m).keys ↔ BitVec.extractLsb' 0 i y ∈ m.keys := by
  simp only [Finmap.mem_keys, ← Finmap.lookup_isSome, expandCache_lookup, Option.isSome_map]

@[simp] lemma expandCache_empty (i k : ℕ) :
    expandCache i k (∅ : Finmap (fun _ : BitVec i => BitVec (k + k))) = ∅ := by
  apply Finmap.ext_lookup
  intro y
  simp

/-- Inserting a parent label into the `flipMsb2` cache corresponds to inserting the two child
labels into the `flipMsb` cache. -/
lemma expandCache_insert_union (i k : ℕ)
    (m : Finmap (fun _ : BitVec i => BitVec (k + k))) (x : BitVec (i + 1)) (w : BitVec (k + k))
    (hx : BitVec.extractLsb' 0 i x ∉ m.keys) :
    expandCache i k (m.insert (BitVec.extractLsb' 0 i x) w) =
      (expandCache i k m) ∪
        ((Finmap.insert x (PRG.chooseHalfI w (x[i]))
          (∅ : Finmap (fun _ : BitVec (i + 1) => BitVec k))).insert x.flipMsb
            (PRG.chooseHalfI w (x.flipMsb[i]))) := by
  have hxnotL : x ∉ expandCache i k m := by
    rw [← Finmap.mem_keys, expandCache_mem]; exact hx
  have hfnotL : x.flipMsb ∉ expandCache i k m := by
    rw [← Finmap.mem_keys, expandCache_mem, BitVec.extractLsb'_zero_flipMsb]; exact hx
  apply Finmap.ext_lookup
  intro y
  by_cases hyx : y = x
  · subst hyx
    rw [Finmap.lookup_union_right hxnotL, Finmap.lookup_insert_of_ne _
      (Ne.symm (BitVec.flipMsb_ne_self y)), Finmap.lookup_insert]
    simp [Finmap.lookup_insert]
  · by_cases hyf : y = x.flipMsb
    · subst hyf
      rw [Finmap.lookup_union_right hfnotL, expandCache_lookup,
        BitVec.extractLsb'_zero_flipMsb, Finmap.lookup_insert, Finmap.lookup_insert]
      simp
    · have hne : BitVec.extractLsb' 0 i y ≠ BitVec.extractLsb' 0 i x := by
        intro h
        rcases BitVec.eq_or_eq_flipMsb_of_extractLsb'_eq h with h1 | h1
        · exact hyx h1
        · exact hyf h1
      by_cases hym : y ∈ expandCache i k m
      · rw [Finmap.lookup_union_left hym]
        simp [Finmap.lookup_insert_of_ne _ hne]
      · have hmnone : m.lookup (BitVec.extractLsb' 0 i y) = none := by
          rw [Finmap.lookup_eq_none]
          intro hmem
          exact hym (by rw [← Finmap.mem_keys, expandCache_mem]; exact Finmap.mem_keys.mpr hmem)
        rw [Finmap.lookup_union_right hym]
        simp [expandCache_lookup, Finmap.lookup_insert_of_ne _ hne, hmnone,
          Finmap.lookup_insert_of_ne _ hyf, Finmap.lookup_insert_of_ne _ hyx,
          Finmap.lookup_empty]

theorem obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb (i k : ℕ) :
    ObsEq
      (PRF_ideal_cache_batch_flipMsb2 i k)
      (PRF_ideal_cache_batch_flipMsb i (BitVec k)) := by
  -- TODO: change proof to use obs_eq_by_abstraction
  -- obs_eq_by_abstraction (expandCache i k)
  refine correctAbstractionImpliesObsEq _ _ (expandCache i k) ?_
  constructor
  · change PMF.map (expandCache i k) (PMF.pure ∅) = PMF.pure ∅
    rw [PMF.pure_map, expandCache_empty]
  · intro query
    ext1 st
    simp only [mapOutputState, mapInputState, PRF_ideal_cache_batch_flipMsb2,
      PRF_ideal_cache_batch_flipMsb, correctAbstractionDiagSimps, StateTSimps, RStateSimplifier,
      GameHoppingSimplifyPMF, mapSecond, SecurePRFSpec, OracleSpec.Domain]
    by_cases hc : BitVec.extractLsb' 0 i query ∈ st.keys
    · have hcE : query ∈ (expandCache i k st).keys := (expandCache_mem i k st query).mpr hc
      obtain ⟨v, hv⟩ : ∃ v, Finmap.lookup (BitVec.extractLsb' 0 i query) st = some v :=
        Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr (Finmap.mem_keys.mp hc))
      simp [hc, hcE, hv, expandCache_lookup, bind, pure, StateT.bind, StateT.pure,
        StateTSimps, GameHoppingSimplifyPMF, correctAbstractionDiagSimps]
    · have hcE : query ∉ (expandCache i k st).keys :=
        fun h => hc ((expandCache_mem i k st query).mp h)
      simp only [hc, hcE, dif_neg, if_false, not_false_eq_true, StateTSimps, RStateSimplifier,
        GameHoppingSimplifyPMF, StateT.set, StateT.lift, StateT.bind, StateT.pure, set, get,
        bindSecond, correctAbstractionDiagSimps]
      congr 1
      funext a
      congr 1
      funext b
      by_cases hqi : query[i] = true
      · rw [if_pos hqi]
        simp only [bind, StateT.set, StateT.bind, StateT.pure, pure, StateTSimps,
          GameHoppingSimplifyPMF, bindSecond, correctAbstractionDiagSimps]
        rw [expandCache_insert_union i k st query (a ++ b) hc]
        simp [hqi, PRG.chooseHalfI, BitVec.extractLsb'_append_eq_left,
          BitVec.extractLsb'_append_eq_right, BitVec.getElem_flipMsb_msb]
      · rw [if_neg hqi]
        have hqf : query[i] = false := Bool.not_eq_true _ |>.mp hqi
        simp only [bind, StateT.set, StateT.bind, StateT.pure, pure, StateTSimps,
          GameHoppingSimplifyPMF, bindSecond, correctAbstractionDiagSimps]
        rw [expandCache_insert_union i k st query (b ++ a) hc]
        simp [hqf, PRG.chooseHalfI, BitVec.extractLsb'_append_eq_left,
          BitVec.extractLsb'_append_eq_right, BitVec.getElem_flipMsb_msb]

lemma Finmap.union_insert_mem {X : Type} [DecidableEq X] {f : X → Type} (m1 m2 : Finmap f) (x : X) (v : f x)
  (hx : x ∈ m1.keys) :
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
  (hx : x ∉ m1.keys) :
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

def batch_new_vals_bij_mem {l k : ℕ} (c : Finmap (fun _ : BitVec l.succ => BitVec k)) (x : BitVec l.succ) (h_non_mem : x ∉ c.keys) (hf_mem: x.flipMsb ∈ c.keys) :
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

def batch_new_vals_bij_not_mem {l k : ℕ} (c : Finmap (fun _ : BitVec l.succ => BitVec k)) (x : BitVec l.succ) (h_non_mem : x ∉ c.keys) (hf_not_mem: x.flipMsb ∉ c.keys) :
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
lemma Finmap.from_fun_lookup (X' : Finset X) (f : X' → Y) (elem : X) [DecidableEq X] :
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
lemma Finmap.from_fun_in (X' : Finset X) (f : X' → Y) (elem : X) [DecidableEq X] :
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
  funext x c
  simp only [GGMHybrid2_Vs_3_batch, StateTSimps, RStateSimplifier, GameHoppingSimplifyPMF]
  split_ifs with hif <;> try rfl
  simp only [StateTSimps, RStateSimplifier, GameHoppingSimplifyPMF]
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
    rw [← PMF.map_uniformOfFintype_equiv (batch_new_vals_bij_not_mem c x hif hflip).symm ]
    simp [StateT.set, batch_new_vals_bij_not_mem]
    simp only [GameHoppingSimplifyPMF, StateT.set]
    congr
    ext1 a
    congr
    ext1 b
    congr 2
    -- · simp
    apply Finmap.ext_lookup
    intro e
    by_cases hex : e = x
    · subst hex
      simp
      rw [Finmap.lookup_union_right]
      · simp
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
      ((GGMHybridStepReduction2RF prg i.succ) ◇
        (PRF_ideal_cache_batch_flipMsb2 i.1 k))
      (GGMHybrid3 prg i) := by
  simp [OracleReduction.apply, GGMHybridStepReduction2RF, GGMHybrid3, PRF_ideal_cache_batch_flipMsb2]
  -- TODO: obs_eq_by_abstraction (fun (a, b) => b)
  refine correctAbstractionImpliesObsEq _ _ (fun (a,b) => b) ?_
  constructor
  · simp [PMF.map]
  · intro query
    ext1 st
    simp only [OracleReductionSimps, correctAbstractionDiagSimps, StateTSimps,
      RStateSimplifier, GameHoppingSimplifyPMF, SecurePRFSpec]
    generalize Hm : Finmap.lookup (BitVec.extractLsb' 0 (↑i) query) st.2 = m
    cases m with
    | none =>
      simp []
      rw [ite_cond_eq_false]
      · simp only [RStateSimplifier, StateTSimps, GameHoppingSimplifyPMF]
        by_cases hqi : query[i.val]
        · simp only [GameHoppingSimplifyPMF, hqi, PRG.chooseHalfI]
          simp
          conv_rhs =>
            rw [← pmfBind_uniform_bitVec_append (a := k) (b := k)]
          simp only [RStateSimplifier, StateTSimps, GameHoppingSimplifyPMF,
            StateT.set, set, MonadState.set, MonadStateOf.set]
          congr 1
          funext a
          congr 1
          funext b
          congr 3
          · exact (BitVec.extractLsb'_append_eq_left).symm
          · rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
            congr 1
        · simp only [Bool.not_eq_true] at hqi
          simp only [GameHoppingSimplifyPMF, hqi, PRG.chooseHalfI, Bool.false_eq_true,
            if_false, reduceIte]
          conv_rhs =>
            rw [← pmfBind_uniform_bitVec_swap_append]
          simp only [RStateSimplifier, StateTSimps, GameHoppingSimplifyPMF,
            StateT.set, set, MonadState.set, MonadStateOf.set]
          conv_lhs => rw [PMF.bind_comm]
          congr 1
          funext a
          congr 1
          funext b
          congr 3
          · exact (BitVec.extractLsb'_append_eq_right).symm
          · rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
            congr 1
      · have hnot : BitVec.extractLsb' 0 i.1 query ∉ st.2.keys := by
          rw [Finmap.mem_keys]
          exact Finmap.lookup_eq_none.mp Hm
        simp [hnot]
    | some x =>
      simp
      rw [ite_cond_eq_true]
      · simp only [RStateSimplifier, StateTSimps, GameHoppingSimplifyPMF]
        rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
        simp only [Nat.add_zero, Nat.zero_add, Hm, Option.getD_some]
        rw [BitVec.extractLsb'_extractLsb' (h := by omega)]
        congr 1
      · have hin : BitVec.extractLsb' 0 i.1 query ∈ st.2.keys := by
          rw [Finmap.mem_keys]
          exact Finmap.mem_of_lookup_eq_some Hm
        simp [hin]

/-- The `GGMHybrid2`/`GGMHybrid3` bridge as a symbolic indistinguishability object.

This is intentionally phrased as an `IndistinguishableI` chain rather than a direct
`ObsEq`, so the step can be assembled from the cached-random-function equivalences and
the stateful reduction that embeds the depth-`i+1` random function into the outer PRF
game. -/
noncomputable def indistinguishableI_GGMHybrid2_Vs_3
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n)
    :
    IndistinguishableI IndistinguishabilityAssumptions.empty none
      (SecurePRFSpec (BitVec n) (BitVec k))
      (GGMHybrid2 prg i.succ)
      (GGMHybrid3 prg i) := by
  game_hopping [
    GGMHybrid2 prg i.succ,
    (GGMHybridStepReduction2RF prg i.succ) ◇ (PRF_ideal2 (BitVec i.succ.1) (BitVec k)),
    (GGMHybridStepReduction2RF prg i.succ) ◇
      (PRF_ideal_cache_batch (BitVec i.succ.1) (BitVec k)
        (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)),
    (GGMHybridStepReduction2RF prg i.succ) ◇ (PRF_ideal_cache_batch_flipMsb i.1 (BitVec k)),
    (GGMHybridStepReduction2RF prg i.succ) ◇ (PRF_ideal_cache_batch_flipMsb2 i.1 k),
    GGMHybrid3 prg i]
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_reduction_rf prg i.succ)
  · refine IndistinguishableI.complexInitReduction (GGMHybridStepReduction2RF prg i.succ) none ?_
    exact IndistinguishableI.trans _ none
      (Indistinguishable.symmetric
        (indistinguishable_PRF_ideal_PRF_ideal2 (BitVec i.succ.1) (BitVec k)))
      (Indistinguishable.of_ObsEq
        (obsEq_PRF_ideal_PRF_ideal_cache_pair (BitVec i.succ.1) (BitVec k)
          (GGMHybrid2_Vs_3_batch i) (GGMHybrid2_Vs_3_batch_self i)))
  · exact IndistinguishableI.complexInitReduction (GGMHybridStepReduction2RF prg i.succ) none
      (Indistinguishable.symmetric
        (Indistinguishable.of_ObsEq
          (obsEq_PRF_ideal_cache_batch_flipMsb_GGMHybrid2_Vs_3_batch (k := k) i)))
  · exact IndistinguishableI.complexInitReduction (GGMHybridStepReduction2RF prg i.succ) none
      (Indistinguishable.symmetric
        (Indistinguishable.of_ObsEq
          (obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb i.1 k)))
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_Vs_3_batch_bridge prg i)


-- easy, just definition
-- swap PMF.uniform (BitVec k k) into ideal prg randomness
theorem obsEq_GGMHybrid2_applyStepReduction_real {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (GGMHybrid3 prg i)
      ( (GGMHybridStepReduction2PRG prg i) ◇ (PRG_rand k k)) := by
  obs_eq_by_abstraction (fun labels => (labels, ()))
  split <;>
    simp_all [set, MonadState.set, MonadStateOf.set, StateT.set,
      correctAbstractionDiagSimps, RStateSimplifier, GameHoppingSimplifyPMF,
      OracleReductionSimps, StateTSimps]

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

/-- One expansion step of `applyPRGs`, stated for a non-literal positive length. -/
lemma applyPRGs_step {k q : ℕ} (prg : PRG k k) (s : BitVec k) (bits : BitVec q) (hq : 0 < q) :
    applyPRGs prg s bits =
      applyPRGs prg (PRG.chooseHalfI (prg.draw s) (bits.getLsbD 0))
        (BitVec.extractLsb' 1 (q - 1) bits) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  rfl

-- by correct abstraction, we map each seed in cache to its prgs.
theorem obsEq_applyStepReduction_rand_GGMHybrid2 {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq ( (GGMHybridStepReduction2PRG prg i) ◇ (PRG_real prg))
      (GGMHybrid2 prg i.castSucc) := by
  apply ObsEq.symm
  obs_eq_by_abstraction
    (fun f => ⟨(Finmap.mapKeys f prg.draw), ()⟩
    : (GGMHybrid2 prg i.castSucc).stateType → (GGMHybridStepReduction2PRG prg i).stateType × (PRG_real prg).stateType)
  next query st s1 s2 =>
  generalize hlk : Finmap.lookup (BitVec.extractLsb' 0 (↑i) {toFin:=query}) ⟨s1, s2⟩ = m
  cases m with
  | none =>
    simp [OracleReductionSimps, RStateSimplifier, StateTSimps, GameHoppingSimplifyPMF]
    congr 1
    ext1 o
    simp [set, StateT.set]
    rw [applyPRGs_step prg o _ (by omega)]
    congr 4
    simp [Nat.testBit]
  | some v =>
    simp [OracleReductionSimps, RStateSimplifier, StateTSimps, GameHoppingSimplifyPMF]
    rw [applyPRGs_step prg v _ (by omega)]
    congr 4
    simp [Nat.testBit]

/-- One hybrid step is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def GGMHybrid2_step_indistinguishable_of_securePRG
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    Indistinguishable (SecurePRGAssumption' prg)
      (GGMHybrid2 prg i.castSucc)
      (GGMHybrid2 prg i.succ) := by
  game_hopping [
    GGMHybrid2 prg i.castSucc,
    (GGMHybridStepReduction2PRG prg i) ◇ (PRG_real prg),
    (GGMHybridStepReduction2PRG prg i) ◇ (PRG_rand k k),
    GGMHybrid3 prg i,
    GGMHybrid2 prg i.succ]
  · exact Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_applyStepReduction_rand_GGMHybrid2 prg i))
  · exact Indistinguishable.symmetric
      (Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_applyStepReduction_real prg i))
  · exact Indistinguishable.symmetric
      (liftEmptyAssumptions (indistinguishableI_GGMHybrid2_Vs_3 prg i))

/-- One GGM hybrid step is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def GGMHybrid_step_indistinguishable_of_securePRG
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    Indistinguishable (SecurePRGAssumption' prg)
      (GGMHybrid prg i.castSucc)
      (GGMHybrid prg i.succ) := by
  game_hopping [
    GGMHybrid prg i.castSucc,
    GGMHybrid2 prg i.castSucc,
    GGMHybrid2 prg i.succ,
    GGMHybrid prg i.succ]
  · exact liftEmptyAssumptions (obsEq_rand_GGMHybrid_1_2 prg i.castSucc)
  · exact GGMHybrid2_step_indistinguishable_of_securePRG prg i
  · exact Indistinguishable.symmetric
      (liftEmptyAssumptions (obsEq_rand_GGMHybrid_1_2 prg i.succ))

/-- All GGM hybrids are indistinguishable assuming the length-doubling PRG is secure. -/
noncomputable def GGMHybrids_indistinguishable_of_securePRG
    {k n : ℕ} (prg : lengthDoublingPRG k) :
    Indistinguishable (SecurePRGAssumption' prg)
      (GGMHybrid prg 0)
      (GGMHybrid prg (Fin.last n)) := by
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
    exact GGMHybrid_step_indistinguishable_of_securePRG prg ⟨i, hi⟩

/-- GGM is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def secureGGM_of_securePRG
    {k n : ℕ} (prg : lengthDoublingPRG k) :
    SecurePRFDef (SecurePRGAssumption' prg) (GGM prg n) := by
  game_hopping [
    PRF_real (GGM prg n),
    GGMHybrid prg 0,
    GGMHybrid prg (Fin.last n),
    PRF_ideal (BitVec n) (BitVec k)]
  · exact Indistinguishable.of_ObsEq (obsEq_real_GGMHybrid_zero prg)
  · exact GGMHybrids_indistinguishable_of_securePRG prg
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid_last_ideal prg)

end
