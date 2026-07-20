import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRG
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF
import GameHoppingInLean.Examples.Constructions.GGM
import GameHoppingInLean.Examples.Misc.RF_caching
import GameHoppingInLean.Tactic.Normalization.PMF.Simprocs
import GameHoppingInLean.Tactic.Normalization.BitVec.Simprocs
import GameHoppingInLean.ComputationalIndistinguishability.AssumptionCounting

section
attribute [-simp] bind_pure_comp
open scoped IndistinguishableI
open scoped OracleReduction

/-
# The proof security of GGM construction: from PRG to PRF.
  The proof have three parts:
  1. Definition of hybrids and reduction.
  2. Proving ObsEq of various hops in sequence.
  3. Final proof - joining all obsEqs together to form game hopping proof.
-/


/-!
# Security of the GGM construction

This file proves that the GGM construction turns a secure length-doubling PRG
into a secure PRF.

## Hybrids

The proof follows the usual GGM hybrid argument.  In the paper, the `i`-th
hybrid is described as follows.  It samples a random function

    f_i : BitVec i → BitVec k

and, on input `x : BitVec n`, uses the first `i` bits of `x` to look up a
random label, then applies the PRG along the remaining bits:

    H_i(x) =
      prg_{x_n} (
        prg_{x_{n-1}} (
          ...
            prg_{x_{i+1}} (f_i(x_1, ..., x_i))
          ...
        )
      ).

In the code, bits are read in the same order as `applyPRGs`: the prefix
`(x_1, ..., x_i)` is represented by

    BitVec.extractLsb' 0 i x

and the remaining suffix by

    BitVec.extractLsb' i (n - i) x.

Thus `H_0` is the real GGM oracle: `BitVec 0` is a singleton, so sampling
`f_0 : BitVec 0 → BitVec k` is the same as sampling one seed.  At the other
endpoint, `H_n` is the ideal random-function oracle, because no PRG applications
remain.

The final theorem instantiates `n = k`, so the PRF input length and the seed
length are both the security parameter.

## Cache representations

The same mathematical hybrid appears in several cache representations.

* `GGMHybrid prg i` is the eager version of `H_i`.
  Its state is a total table

      BitVec i → BitVec k

  sampled during initialization.

* `GGMHybrid2 prg i` is the ordinary lazy-cache version of `H_i`.
  Its state is a partial table

      Finmap (fun _ : BitVec i => BitVec k).

  On a query, it looks up the `i`-bit prefix.  If the prefix is missing, it
  samples a fresh uniform label and stores it.

* `GGMHybrid3 prg i` is the paired-cache version used in one adjacent-hybrid
  step.  Its state is a partial table

      Finmap (fun _ : BitVec i => BitVec (k + k)).

  Each cached value represents two `k`-bit labels at once.  The next input bit
  chooses which half is used.

The random-function oracles have analogous cache variants.

* `PRF_ideal X Y` is eager: it samples a total function `X → Y`.

* `PRF_ideal2 X Y` is lazy: it stores a partial cache `X ⇀ Y`.

* `PRF_ideal_cache_batch_pairs i Y` is lazy but fills the cache in pairs:
  when queried on `x : BitVec (i+1)`, it caches values for both inputs with the
  same low `i` bits.

## Proof shape

The top-level proof has the following shape:

    PRF_real (GGM prg n)
      ≈ GGMHybrid  prg 0
      ≈ GGMHybrid2 prg 0
      ≈ ...
      ≈ GGMHybrid2 prg (Fin.last n)
      ≈ GGMHybrid  prg (Fin.last n)
      ≈ PRF_ideal (BitVec n) (BitVec k)

The conversions between eager and lazy caches are observational equivalences,
proved by randomized abstractions that complete a partial cache by sampling all
missing values uniformly.

The only step using the PRG security assumption is the adjacent-hybrid step

    GGMHybrid2 prg i.succ  ≈  GGMHybrid2 prg i.castSucc.

It is proved by the chain

    GGMHybrid2 prg i.succ
      ≈ (GGMHybridStepReduction2RF  prg i.succ) ◇ (PRF_ideal2 (BitVec i.succ.1) (BitVec k))
      ≈ (GGMHybridStepReduction2RF  prg i.succ) ◇ ((PRF_ideal_cache_batch_pairs i (BitVec k))
      ≈ GGMHybrid3 prg i
      ≈ (GGMHybridStepReduction2PRG prg i) ◇ PRG_rand k k
      ≈ (GGMHybridStepReduction2PRG prg i) ◇ PRG_real prg
      ≈ GGMHybrid2 prg i.castSucc.

The reduction `GGMHybridStepReduction2PRG` maintains a paired cache indexed by
`i`-bit prefixes.  For each new prefix, it queries the PRG challenger once and
uses the resulting `BitVec (k + k)` as the two possible next labels.  With
`PRG_rand`, these two labels are uniformly random; with `PRG_real prg`, they are
the two halves of `prg.draw s` for a fresh seed `s`.

Note, that only application of assumption is under reduction (GGMHybridStepReduction2PRG prg i). This reduction is clearly polynomial!
It is interesting that some hybrids in this proof and even left side of thesis (PRF_ideal) are *not* polynomial. That does not affect correctness, because soundness theorem only cares about reduction used above application of assumption (only GGMHybridStepReduction2PRG).
-/


/-- Any indistinguishability that holds under the empty assumption set holds under
any assumption set. -/
noncomputable def liftEmptyAssumptions
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat} {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O}
    (h : IndistinguishableI IndAssumptions.empty q_b ro₁ ro₂) :
    IndistinguishableI Assumptions q_b ro₁ ro₂ := by
  induction h with
  | assumption i => exact i.elim
  | obsEqB q hObs => exact IndistinguishableI.obsEqB q hObs
  | reduction r q h ih => exact IndistinguishableI.reduction r q ih
  | symm q h ih => exact IndistinguishableI.symm q ih
  | trans ro₂ q h₁ h₂ ih₁ ih₂ => exact IndistinguishableI.trans ro₂ q ih₁ ih₂
  | longSequence l q ro hStep ih =>
      exact IndistinguishableI.longSequence l q ro (fun j hj => ih j hj)

/-- The `i`-th hybrid for the GGM proof.

The oracle samples a uniformly random label for every depth-`i` node in the GGM tree.
On input `x`, it reads the first `i` bits in the same LSB-first order used by `applyPRGs`,
looks up the corresponding random label, and then evaluates the remaining suffix with `prg`. -/
noncomputable def GGMHybrid {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    OracleImpl (SecurePRFSpec (BitVec n) (BitVec k)) where
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
  simp [sReduction, sStateT, sRState,
    sPMF, game_hopping_unfold]
  constructor
  · ext f
    simp [PMF.uniformOfFintype_apply]
  · funext query labels
    have : n - n = 0 := by omega
    rw [this]
    simp [applyPRGs]


noncomputable def GGMHybrid2 {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin (n + 1)) :
    OracleImpl (SecurePRFSpec (BitVec n) (BitVec k)) where
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
    OracleImpl (SecurePRFSpec (BitVec n) (BitVec k)) where
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
      let chosenLabel := PRG.chooseHalfI labels (remainingBits.getLsbD 0)
      pure (applyPRGs prg chosenLabel (BitVec.extractLsb' 1 (n-i.1-1) remainingBits))


/-- Skeleton reduction for one adjacent hybrid step in the GGM proof.

The implementation:
1. maintains a cache of labels for depth-`i+1` nodes,
2. querys the underlying PRG challenger once per unseen depth-`i` prefix, and
3. interprets the challenge output as the two child labels for that prefix. -/
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
    let chosenHalf := PRG.chooseHalfI labels (remainingBits.getLsbD 0)
    let output : BitVec k := applyPRGs prg chosenHalf (BitVec.extractLsb' 1 (n-i.1-1) remainingBits)
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

/- # 2. Proving ObsEqs -/

attribute [local game_hopping_unfold]
  GGMHybrid2 GGMHybrid3 GGMHybridStepReduction2PRG GGMHybridStepReduction2RF
  PRF_ideal2 PRG_real PRG_rand PRF_ideal_cache_batch
  PRF_ideal_cache_batch_pairs
-- Consecutive GGM hybrids differ by one use of the underlying PRG.


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
    IndistinguishableSingle IndAssumptions.empty
      (GGMHybrid prg i)
      (GGMHybrid2 prg i) := by
  game_hopping_basic [
    GGMHybrid prg i,
    (GGMHybridStepReduction2RF prg i) ◇ (PRF_ideal (BitVec i.1) (BitVec k)),
    (GGMHybridStepReduction2RF prg i) ◇ (PRF_ideal2 (BitVec i.1) (BitVec k)),
    GGMHybrid2 prg i]
  · apply Indistinguishable.of_ObsEq
    obs_eq_by_abstraction ← (fun st => st.2)
    congr 1
    exact Subsingleton.elim _ _
  · exact IndistinguishableI.reduction (GGMHybridStepReduction2RF prg i) none
      (indistinguishable_PRF_ideal_PRF_ideal2 (BitVec i.1) (BitVec k))
  · apply Indistinguishable.of_ObsEq
    apply ObsEq.symm
    apply obsEq_GGMHybrid2_reduction_rf

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

noncomputable def PRF_ideal_cache_batch_flipMsb2 (i : ℕ) (k : ℕ) :
    OracleImpl (SecurePRFSpec (BitVec i.succ) (BitVec k)) where
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

attribute [local game_hopping_unfold] PRF_ideal_cache_batch_pairs

lemma extractFlat : BitVec.extractLsb' 0 i (BitVec.extractLsb' 0 (i+j) x) = BitVec.extractLsb' 0 i x := by
  apply BitVec.extractLsb'_zero_extractLsb'_zero
  exact Nat.le_add_right i j

/-- Final bridge from the batch-cached random function view to the paired-label
`GGMHybrid3` view. This is the remaining randomization-shift lemma: the batch relation
will eventually cache both children of a depth-`i` node, and this lemma will identify
that cache with the `BitVec (k + k)` parent-label cache. -/
theorem obsEq_GGMHybrid2_Vs_3_batch_bridge {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq
      ((GGMHybridStepReduction2RF prg i.succ) ◇
        (PRF_ideal_cache_batch_pairs i (BitVec k)))
      (GGMHybrid3 prg i) := by
  simp [OracleReduction.apply, GGMHybridStepReduction2RF, GGMHybrid3, PRF_ideal_cache_batch_flipMsb2]
  refine correctAbstractionImpliesObsEq _ _
     (fun (a,b) => Finmap.mapKeys b (fun (x, y) => (x++y))) ?_
  solveCorrectAbstractionBasic[]
  -- constructor
  · next q1 q2 q3 w =>
    if Haa :  BitVec.extractLsb' 0 ↑i { toFin := q1 } ∈ w.keys then
      simp [Haa]
      have ⟨z , Hz⟩ := Finmap.mem_iff.mp Haa
      rw [extractFlat]
      rw [Hz]
      simp []
      simp [sRState, sPMF]
      congr 3
      · simp [choosePair, PRG.chooseHalfI]
        congr
        · simp [BitVec.extractLsb'_append_eq_left]
        · simp [BitVec.extractLsb'_append_eq_right]
      apply Eq.symm
      apply BitVec.extractLsb'_extractLsb'
      apply le_of_eq
      have : i < n := i.isLt
      refine Nat.add_sub_of_le ?_
      refine Nat.le_sub_of_add_le' ?_
      exact Order.add_one_le_iff.mpr this
    else
      simp [Haa]
      have Hz := Finmap.lookup_eq_none.mpr Haa
      rw [Hz]
      simp [sRState]
      conv =>
          rhs
          rw [bind_uniformOfFintype_bitVec_append_rev]
      simp [PRG.chooseHalfI]
      split_ifs <;> (
      -- if L : (q1.val).testBit ↑i then (
        simp [sPMF]
        congr
        ext1 a
        congr
        ext1 b
        unfold StateT.set
        simp []
        congr 3
        · simp [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
        · apply Eq.symm
          apply BitVec.extractLsb'_extractLsb'
          have : i < n := i.isLt
          grind
        )



theorem obsEq_GGMHybrid2_applyStepReduction_real {k n : ℕ}
    (prg : lengthDoublingPRG k) (i : Fin n) :
    ObsEq (GGMHybrid3 prg i)
      ( (GGMHybridStepReduction2PRG prg i) ◇ (PRG_rand k k)) := by
  obs_eq_by_abstraction (fun labels => (labels, ()))
  split <;>
    simp_all [set, MonadState.set, MonadStateOf.set, StateT.set,
      correctAbstractionDiagSimps, sRState, sPMF,
      sReduction, sStateT]

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
    simp [sReduction, sRState, sStateT, sPMF]
    congr 1
    ext1 o
    simp [set, StateT.set]
    rw [applyPRGs_step prg o _ (by omega)]
    congr 4
    simp [Nat.testBit]
  | some v =>
    simp [sReduction, sRState, sStateT, sPMF]
    rw [applyPRGs_step prg v _ (by omega)]
    congr 4
    simp [Nat.testBit]

/- # Final proof
We join all steps together. -/

/-- One hybrid step is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def GGMHybrid2_step_indistinguishable_of_securePRG
    {k n : ℕ} (prg : lengthDoublingPRG k) (i : Fin n) :
    IndistinguishableSingle (SecurePRGAssumption' prg)
      (GGMHybrid2 prg i.succ)
      (GGMHybrid2 prg i.castSucc)
      := by
  game_hopping_basic [
    GGMHybrid2 prg i.succ,
    (GGMHybridStepReduction2RF prg i.succ) ◇ (PRF_ideal2 (BitVec i.succ.1) (BitVec k)),
    (GGMHybridStepReduction2RF prg i.succ) ◇ (PRF_ideal_cache_batch_pairs i (BitVec k)),
    GGMHybrid3 prg i,
    (GGMHybridStepReduction2PRG prg i) ◇ (PRG_rand k k),
    (GGMHybridStepReduction2PRG prg i) ◇ (PRG_real prg),
    GGMHybrid2 prg i.castSucc
    ]
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_reduction_rf prg i.succ)
  · apply IndistinguishableI.reduction (GGMHybridStepReduction2RF prg i.succ) none
    exact Indistinguishable.of_ObsEq (obsEq_PRF_ideal_PRF_ideal_cache_pairs (BitVec k))
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_Vs_3_batch_bridge prg i)
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid2_applyStepReduction_real prg i)
  · game_hopping_reduce_assumption
  · apply Indistinguishable.of_ObsEq (obsEq_applyStepReduction_rand_GGMHybrid2 prg i)

/-- All GGM hybrids are indistinguishable assuming the length-doubling PRG is secure. -/
noncomputable def GGMHybrids_indistinguishable_of_securePRG
    {k n : ℕ} (prg : lengthDoublingPRG k) :
    IndistinguishableI (SecurePRGAssumption' prg) none
      (GGMHybrid2 prg 0)
      (GGMHybrid2 prg (Fin.last n)) := by
  refine Indistinguishable.long_step n
    (fun j => GGMHybrid2 prg ⟨j.1, ?_⟩)
    (GGMHybrid2 prg 0)
    (GGMHybrid2 prg (Fin.last n))
    (by rfl)
    (by rfl)
    ?_
  · exact Finset.mem_range.mp j.2
  · intro i hi
    simp [ro_seq_fixed]
    apply Indistinguishable.symmetric
    exact GGMHybrid2_step_indistinguishable_of_securePRG prg ⟨i, hi⟩

/-- GGM is secure assuming the underlying length-doubling PRG is secure. -/
noncomputable def secureGGM_of_securePRG
    (prgFam : PRGFamily id id) :
    SecurePRFDef (SecurePRGAssumptionFam prgFam) (fun κ => GGM (prgFam.prg κ) κ) := by
  intro κ
  simp [SecurePRGAssumptionFam]
  generalize (prgFam.prg κ) = prg
  game_hopping_basic [
    PRF_real (GGM prg κ),
    GGMHybrid prg 0,
    GGMHybrid2 (prg) 0,
    GGMHybrid2 (prg) (Fin.last κ),
    GGMHybrid (prg) (Fin.last κ),
    PRF_ideal (BitVec κ) (BitVec κ)]
  · exact Indistinguishable.of_ObsEq (obsEq_real_GGMHybrid_zero prg)
  · exact liftEmptyAssumptions (obsEq_rand_GGMHybrid_1_2 prg 0)
  · exact GGMHybrids_indistinguishable_of_securePRG prg
  · exact Indistinguishable.symmetric
      (liftEmptyAssumptions (obsEq_rand_GGMHybrid_1_2 prg ((Fin.last κ))))
  · exact Indistinguishable.of_ObsEq (obsEq_GGMHybrid_last_ideal prg)
end


/-- how to see bounds that we proved? The best way it to write
"assumptionCounting (secureGGM_of_securePRG prgFam κ) = sorry"
and then to simplify as below. Do not simplify reduction names!
Then replace sorry with resulting term.
Here, we see that the only reduction that affect concrete security bound is GGMHybridStepReduction2PRG -/
noncomputable def GGM_proof_constants_simp {κ : ℕ} (prgFam : PRGFamily id id)
    :
    (assumptionCounting (secureGGM_of_securePRG prgFam κ)) =
    (fun _idx ↦
      (List.ofFn fun (x : Fin κ) ↦
        [rcompose
          (OracleReduction.identity (SecurePRGSpec κ κ))
          (GGMHybridStepReduction2PRG (prgFam.prg κ) x)]
      ).flatten,
    fun _idx ↦ [])
     := by
  simp [secureGGM_of_securePRG, GGMHybrids_indistinguishable_of_securePRG, GGMHybrid2_step_indistinguishable_of_securePRG]
  have T : forall xp : Unit, Decidable (xp = PUnit.unit) := by
    intro xp
    infer_instance
  have T2 : forall x : Unit, x = PUnit.unit := by
    simp []
  simp [transitive_step_val_simple, assumptionCounting,
    Indistinguishable.of_ObsEq, Indistinguishable.symmetric, Indistinguishable.reflexive, Indistinguishable.long_step, liftEmptyAssumptions
  ]
  simp [obsEq_rand_GGMHybrid_1_2, indistinguishable_PRF_ideal_PRF_ideal2]
  simp [transitive_step_val_simple, assumptionCounting,
    Indistinguishable.of_ObsEq, Indistinguishable.symmetric, Indistinguishable.reflexive, Indistinguishable.long_step, liftEmptyAssumptions
  ]
  simp [T2, long_step_combinator_simple, long_step_combinator_simple_half]
  simp [SecurePRGAssumptionFam, SecurePRGAssumption', SecurePRGAssumptionFull]
