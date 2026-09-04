import Hopscotch.Comp.StatefulRandomOracle
import Hopscotch.Comp.OracleReductions
import Hopscotch.Comp.OracleReductionsLemmas
import Hopscotch.ObservationalEq.Defs
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec
import Hopscotch.Indistinguishability.Def
import Hopscotch.Tactic.SimpAttrLemmas
import Hopscotch.ComputationalIndistinguishability.Distance
import Hopscotch.ComputationalIndistinguishability.AdversaryAdvantage
import Hopscotch.ComputationalIndistinguishability.Sums
-- import Hopscotch.ComputationalIndistinguishability.ReductionCombiner
import Hopscotch.ComputationalIndistinguishability.ReductionCombinerList
import Hopscotch.ComputationalIndistinguishability.AssumptionCounting

import Hopscotch.ComputationalIndistinguishability.ObsEqComp
import Hopscotch.Tactic.Defs


/- # Soundness theorem
  Here we define the soundness theorem. It relates advantage of adversary A against original protocol to advantage of ∑_i n_i * advantage of (A.compose R_i) against assumption i.

  Here R_i, n_i are computed from result of assumption counting function `assumptionCountingFin` (see AssumptionCounting.lean for more on it). For each assumption, `assumptionCountingFin` returns a list of reductions l. R_i is a reduction that picks one reduction from l uniformly at random and executes it. n_i = l.length .

  We express this sum using function `advBound`. The soundness theorem is called `computationalSoundness` and can be found at the very end of file. The name comes from the fact that syntactic proofs presented as IndistinguishableI are shown to have semantic meaning. See paper for more high level discussion.

  The soundness theorem is proven by induction on the IndistinguishableI. The trans step requires reasoning about 'pick-one-at-random' reduction combination -- more details on it are in ReductionCombiner.lean.
-/

/-- bound produced by soundness theorem, given pairs of n_i and R_i -/
def advBound {Idx : Type} (Assumptions : IndAssumptions Idx) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : OracleImpl O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (distinguisher : adversaryT O)
  : Prop :=
  FreeM.depth distinguisher ≤ q_b ->
    (advantage distinguisher ro1 ro2) =
    ∑ j : { x // x ∈ asc.1.subset },
      ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.1.values j))
    - ∑ j : { x // x ∈ asc.2.subset },
       ascToReal distinguisher ((Assumptions.assumptions j)) (combine_red (asc.2.values j))

def advBoundQ {Idx : Type} (Assumptions : IndAssumptions Idx) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : OracleImpl O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  : Prop :=
  forall (distinguisher : adversaryT O),
  advBound Assumptions q_b O ro1 ro2 asc distinguisher

/-- Residual soundness bound in the presence of approximate-equivalence steps. -/
def advBoundWithError {Idx : Type} (Assumptions : IndAssumptions Idx) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : OracleImpl O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (error : NNReal) (distinguisher : adversaryT O) : Prop :=
  FreeM.depth distinguisher ≤ q_b →
    |advantage distinguisher ro1 ro2 -
      ((∑ j : { x // x ∈ asc.1.subset },
          ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.1.values j)))
       - (∑ j : { x // x ∈ asc.2.subset },
          ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.2.values j))))| ≤
      (error : Real)

def advBoundQWithError {Idx : Type} (Assumptions : IndAssumptions Idx) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : OracleImpl O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (error : NNReal) : Prop :=
  ∀ distinguisher : adversaryT O,
    advBoundWithError Assumptions q_b O ro1 ro2 asc error distinguisher

/-- The residual bound implies the conventional absolute advantage estimate. -/
lemma advBoundWithError_absolute {Idx : Type} (Assumptions : IndAssumptions Idx) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : OracleImpl O)
    (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
    (error : NNReal) (distinguisher : adversaryT O)
    (h : advBoundWithError Assumptions q_b O ro1 ro2 asc error distinguisher) :
    FreeM.depth distinguisher ≤ q_b →
      |advantage distinguisher ro1 ro2| ≤
        |(∑ j : { x // x ∈ asc.1.subset },
            ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.1.values j)))
         - (∑ j : { x // x ∈ asc.2.subset },
            ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.2.values j)))| +
        (error : Real) := by
  intro hdepth
  let assumptionTerm : Real :=
    (∑ j : { x // x ∈ asc.1.subset },
      ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.1.values j)))
    - (∑ j : { x // x ∈ asc.2.subset },
      ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.2.values j)))
  have hresidual := h hdepth
  change |advantage distinguisher ro1 ro2 - assumptionTerm| ≤ (error : Real) at hresidual
  change |advantage distinguisher ro1 ro2| ≤ |assumptionTerm| + (error : Real)
  calc
    |advantage distinguisher ro1 ro2| =
        |(advantage distinguisher ro1 ro2 - assumptionTerm) + assumptionTerm| := by
          rw [sub_add_cancel]
    _ ≤ |advantage distinguisher ro1 ro2 - assumptionTerm| + |assumptionTerm| :=
      abs_add_le _ _
    _ ≤ (error : Real) + |assumptionTerm| :=
      add_le_add hresidual (le_refl _)
    _ = |assumptionTerm| + (error : Real) := add_comm _ _


lemma obse_eq_step2
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : OracleImpl O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : advBoundQ Assumptions a O o₁ o₂ (noAssumptionUse) :=
  by
    simp [advBoundQ, advBound, AssumptionsUseT.empty, advantage, noAssumptionUse]
    intro dist
    apply obsEq_distinguishing_adv
    apply Hb


noncomputable def obse_eq_step
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : OracleImpl O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : { asc // advBoundQ Assumptions a O o₁ o₂ asc } :=
  ⟨(AssumptionsUseT.empty _ _, AssumptionsUseT.empty _ _), by
    simp [advBoundQ, advBound, AssumptionsUseT.empty, advantage]
    intro dist
    apply obsEq_distinguishing_adv
    apply Hb
  ⟩


/-- A variant of `sumJoinerCorrect` whose joiner-correctness hypothesis only needs to
hold for the actual values `val1`/`val2` at indices lying in both `D1` and `D2`
(rather than for all elements of the fibers `XJ J`). This is what is needed when the
joiner is only known to be correct under side conditions satisfied by the stored
values (e.g. positivity). -/
def sumJoinerCorrect' {Univ : Type} (XJ : Univ -> Type v) [DecidableEq Univ] {D1 D2 : Finset Univ}
  (val1 : (J : D1) -> XJ J)
  (val2 : (J : D2) -> XJ J)
  (joiner : {J : Univ} -> XJ J -> XJ J -> XJ J)
  (f : {J : Univ} -> XJ J -> Real)
  (Hjoiner : forall (j : Univ) (h1 : j ∈ D1) (h2 : j ∈ D2),
    f (val1 ⟨j, h1⟩) + f (val2 ⟨j, h2⟩) = f (joiner (val1 ⟨j, h1⟩) (val2 ⟨j, h2⟩)))
  : sumJoining XJ D1 D2 val1 val2 f (sumJoiner XJ val1 val2 joiner) := by
  classical
  let g1 : Univ → Real := fun j =>
    if h : j ∈ D1 then f (val1 ⟨j, h⟩) else 0
  let g2 : Univ → Real := fun j =>
    if h : j ∈ D2 then f (val2 ⟨j, h⟩) else 0
  let g3 : Univ → Real := fun j =>
    if h : j ∈ finsetSum D1 D2 then
      f (sumJoiner XJ val1 val2 joiner ⟨j, h⟩)
    else 0
  have hval1 :
      (∑ j : D1, f (val1 j)) = ∑ j ∈ finsetSum D1 D2, g1 j := by
    calc
      (∑ j : D1, f (val1 j)) = ∑ j : D1, g1 j := by
        apply Fintype.sum_congr
        intro j
        simp [g1]
      _ = ∑ j ∈ D1, g1 j := (Finset.sum_subtype D1 (by simp) g1).symm
      _ = ∑ j ∈ finsetSum D1 D2, g1 j := by
        apply Finset.sum_subset
        · simp [finsetSum]
        · intro j _ hj
          simp [g1, hj]
  have hval2 :
      (∑ j : D2, f (val2 j)) = ∑ j ∈ finsetSum D1 D2, g2 j := by
    calc
      (∑ j : D2, f (val2 j)) = ∑ j : D2, g2 j := by
        apply Fintype.sum_congr
        intro j
        simp [g2]
      _ = ∑ j ∈ D2, g2 j := (Finset.sum_subtype D2 (by simp) g2).symm
      _ = ∑ j ∈ finsetSum D1 D2, g2 j := by
        apply Finset.sum_subset
        · simp [finsetSum]
        · intro j _ hj
          simp [g2, hj]
  have hval3 :
      (∑ j : finsetSum D1 D2, f (sumJoiner XJ val1 val2 joiner j)) =
        ∑ j ∈ finsetSum D1 D2, g3 j := by
    calc
      (∑ j : finsetSum D1 D2, f (sumJoiner XJ val1 val2 joiner j)) =
          ∑ j : finsetSum D1 D2, g3 j := by
        apply Fintype.sum_congr
        intro j
        simp [g3]
      _ = ∑ j ∈ finsetSum D1 D2, g3 j :=
        (Finset.sum_subtype (finsetSum D1 D2) (by simp) g3).symm
  simp only [sumJoining]
  rw [hval1, hval2, hval3, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h1 : j ∈ D1 <;> by_cases h2 : j ∈ D2
  · simpa [g1, g2, g3, sumJoiner, h1, h2, hj] using
      Hjoiner j h1 h2
  · simp [g1, g2, g3, sumJoiner, h1, h2, hj]
  · simp [g1, g2, g3, sumJoiner, h1, h2, hj]
  · simp [finsetSum, h1, h2] at hj

/-- Proof of transitive step of soundness theorem -/
noncomputable def transitive_step_proof
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ℕ∞} {I : Type} {O : OracleSpec I}
  {o₁ o₂ : OracleImpl O} (rm : OracleImpl O)
  (asc1 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (asc2 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (Hasc1 : advBoundQ Assumptions q_b O o₁ rm asc1)
  (Hasc2 : advBoundQ Assumptions q_b O rm o₂ asc2) :
  advBoundQ Assumptions q_b O o₁ o₂ (transitive_step_val asc1 asc2)
:= by
      classical
      let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => listCombiner a b)
      let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => listCombiner a b)
      simp [advBoundQ, transitive_step_val]
      intro dist
      simp [advBound]
      intro Hdepth
      simp [joint, jointr, assumptionJoiner]
      let _X := Assumptions.decEq
      have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
        asc1.1.values asc2.1.values (fun a b => listCombiner a b)
        (fun x => ascToReal dist _ (combine_red x)) (by
          intro j h1 h2
          apply reduction_combiner_correct_full
        )
      simp [sumJoining] at HHx
      rw [<-HHx]
      clear HHx
      have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
        asc1.2.values asc2.2.values (fun a b => listCombiner a b)
        (fun x => ascToReal dist _ (combine_red x)) (by
          intro j h1 h2
          apply reduction_combiner_correct_full
        )
      simp [sumJoining] at HHx
      rw [<-HHx]
      clear HHx
      rw [(advantageTriangle _ rm _)]
      rw [(Hasc1 dist Hdepth)]
      rw [(Hasc2 dist Hdepth)]
      simp []
      apply sub_add_sub_comm



lemma long_Step_proof_induction
  {O : OracleSpec I}
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat} {a : ℕ}
  {ro : Finset.range (a + 1) -> OracleImpl O}
  (Hxx : (i : ℕ) → i < a → AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (HxxP :  ∀ (i : ℕ) (Hi : i < a),
  advBoundQ Assumptions q_b O
    (ro_seq_fixed a ro i (Nat.le_of_succ_le Hi))
    (ro_seq_fixed a ro (i + 1) Hi)
    (Hxx i Hi))
  : forall (i : ℕ) (Hi : i < a+1),
    advBoundQ Assumptions q_b O
      (ro ⟨0, zero_in_range _⟩)
      (ro ⟨i, Finset.mem_range.mpr Hi⟩)
      (long_step_combinator i
        (fun j Hq => Hxx j
          (Nat.lt_of_lt_of_le Hq (Nat.le_of_lt_succ Hi))
        )
      )
  := (by
    intro i Hi
    induction i
    · simp [long_step_combinator]
      apply obse_eq_step2
      exact fun queriesList ↦ congrFun rfl
    case succ n Hind =>
      have long := Hind (Nat.lt_of_succ_lt Hi)
      simp [long_step_combinator]
      apply transitive_step_proof _ _ _ long
      apply HxxP
  )

/-- An exact bound is a residual bound with zero error. -/
lemma advBoundQWithError_of_advBoundQ
    {Idx : Type} {Assumptions : IndAssumptions Idx} {q_b : ENat}
    {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
    {asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O}
    (H : advBoundQ Assumptions q_b O o₁ o₂ asc) :
    advBoundQWithError Assumptions q_b O o₁ o₂ asc 0 := by
  intro dist hdepth
  rw [H dist hdepth]
  simp

/-- The assumption-use joiner splits the assumption contribution into the two summands. -/
lemma assumptionJoiner_sum {Idx : Type} {Assumptions : IndAssumptions Idx}
    {I : Type} {O : OracleSpec I} (dist : adversaryT O)
    (a1 a2 : AssumptionsUseT Assumptions O) :
    (∑ j : { x // x ∈ (assumptionJoiner a1 a2 (fun a b => listCombiner a b)).subset },
        ascToReal dist (Assumptions.assumptions j)
          (combine_red ((assumptionJoiner a1 a2 (fun a b => listCombiner a b)).values j))) =
      (∑ j : { x // x ∈ a1.subset },
          ascToReal dist (Assumptions.assumptions j) (combine_red (a1.values j))) +
      (∑ j : { x // x ∈ a2.subset },
          ascToReal dist (Assumptions.assumptions j) (combine_red (a2.values j))) := by
  classical
  let _X := Assumptions.decEq
  have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
    a1.values a2.values (fun a b => listCombiner a b)
    (fun x => ascToReal dist _ (combine_red x)) (by
      intro j h1 h2
      apply reduction_combiner_correct_full)
  simp only [sumJoining] at HHx
  simp only [assumptionJoiner]
  rw [← HHx]

/-- Transitive composition of two residual bounds; the errors add. -/
lemma transitive_step_proof_error
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ℕ∞} {I : Type} {O : OracleSpec I}
    {o₁ o₂ : OracleImpl O} (rm : OracleImpl O)
    (asc1 asc2 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
    (e1 e2 : NNReal)
    (H1 : advBoundQWithError Assumptions q_b O o₁ rm asc1 e1)
    (H2 : advBoundQWithError Assumptions q_b O rm o₂ asc2 e2) :
    advBoundQWithError Assumptions q_b O o₁ o₂ (transitive_step_val asc1 asc2) (e1 + e2) := by
  intro dist hdepth
  have hsum1 := assumptionJoiner_sum dist asc1.1 asc2.1
  have hsum2 := assumptionJoiner_sum dist asc1.2 asc2.2
  have h1 := H1 dist hdepth
  have h2 := H2 dist hdepth
  simp only [advBoundWithError, transitive_step_val] at h1 h2 ⊢
  have key :
      advantage dist o₁ o₂ -
        ((∑ j : { x // x ∈ (assumptionJoiner asc1.1 asc2.1 (fun a b => listCombiner a b)).subset },
            ascToReal dist (Assumptions.assumptions j)
              (combine_red ((assumptionJoiner asc1.1 asc2.1
                (fun a b => listCombiner a b)).values j))) -
         (∑ j : { x // x ∈ (assumptionJoiner asc1.2 asc2.2 (fun a b => listCombiner a b)).subset },
            ascToReal dist (Assumptions.assumptions j)
              (combine_red ((assumptionJoiner asc1.2 asc2.2
                (fun a b => listCombiner a b)).values j)))) =
      (advantage dist o₁ rm -
        ((∑ j : { x // x ∈ asc1.1.subset },
            ascToReal dist (Assumptions.assumptions j) (combine_red (asc1.1.values j))) -
         (∑ j : { x // x ∈ asc1.2.subset },
            ascToReal dist (Assumptions.assumptions j) (combine_red (asc1.2.values j))))) +
      (advantage dist rm o₂ -
        ((∑ j : { x // x ∈ asc2.1.subset },
            ascToReal dist (Assumptions.assumptions j) (combine_red (asc2.1.values j))) -
         (∑ j : { x // x ∈ asc2.2.subset },
            ascToReal dist (Assumptions.assumptions j) (combine_red (asc2.2.values j))))) := by
    rw [hsum1, hsum2, advantageTriangle (distinguisher := dist) o₁ rm o₂]
    ring
  rw [key]
  refine le_trans (abs_add_le _ _) ?_
  push_cast
  exact add_le_add h1 h2

/-- Residual soundness for a long sequence of hybrids, by induction on the prefix length. -/
lemma long_step_error_induction
    {O : OracleSpec I}
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat} {a : ℕ}
    {ro : Finset.range (a + 1) -> OracleImpl O}
    (Hxx : (i : ℕ) → i < a → AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
    (err : (i : ℕ) → i < a → NNReal)
    (HxxP : ∀ (i : ℕ) (Hi : i < a),
      advBoundQWithError Assumptions q_b O
        (ro_seq_fixed a ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed a ro (i + 1) Hi)
        (Hxx i Hi) (err i Hi)) :
    ∀ (i : ℕ) (Hi : i < a + 1),
      advBoundQWithError Assumptions q_b O
        (ro ⟨0, zero_in_range _⟩)
        (ro ⟨i, Finset.mem_range.mpr Hi⟩)
        (long_step_combinator i
          (fun j Hq => Hxx j (Nat.lt_of_lt_of_le Hq (Nat.le_of_lt_succ Hi))))
        (∑ j : Fin i, err j.1
          (Nat.lt_of_lt_of_le j.2 (Nat.le_of_lt_succ Hi))) := by
  intro i Hi
  induction i with
  | zero =>
    simp only [long_step_combinator, Finset.univ_eq_empty, Finset.sum_empty]
    exact advBoundQWithError_of_advBoundQ
      (obse_eq_step2 _ _ (fun queriesList ↦ congrFun rfl))
  | succ n Hind =>
    have long := Hind (Nat.lt_of_succ_lt Hi)
    simp only [long_step_combinator, Fin.sum_univ_castSucc]
    exact transitive_step_proof_error _ _ _ _ _ long (HxxP n _)

/-- A single use of an assumption, through the trivial (identity) reduction, contributes
exactly the advantage against that assumption. -/
lemma ascToReal_identity {assumption : SingleAssumption}
    (dist : adversaryT assumption.O)
    (H : [OracleReduction.identity assumption.O].length > 0) :
    ascToReal dist assumption (combine_red ⟨[OracleReduction.identity assumption.O], H⟩) =
      advantage dist assumption.i.1 assumption.i.2 := by
  rw [ascToRealFromObsEq (combine_red ⟨[OracleReduction.identity assumption.O], H⟩)
    (1, OracleReduction.identity assumption.O)
    (fun impl => combine_red_singleton _ H (non_trivial_spec impl) impl) rfl]
  simp [ascToReal, applyreduction2_identity]

/-- Composing every reduction of an assumption use with an outer reduction `r` is the same
as composing the outer reduction with the adversary. -/
lemma ascToReal_rcompose_map {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
    {assumption : SingleAssumption}
    (dist : adversaryT O₂) (r : OracleReduction O₁ O₂)
    (l : {x : List (OracleReduction assumption.O O₁) // x.length > 0})
    (Hl : (l.val.map (fun x => rcompose x r)).length > 0) :
    ascToReal dist assumption (combine_red ⟨l.val.map (fun x => rcompose x r), Hl⟩) =
      ascToReal (OracleReduction.applyReductionToAdversary r dist) assumption
        (combine_red l) := by
  simp only [ascToReal, combine_red, List.length_map]
  congr 1
  rw [← rcompose_apply, ← advantage_reduction, ← advantage_reduction]
  simp only [advantage]
  rw [compose_combine, compose_combine]

/-- Residual symbolic soundness using the structurally convenient assumption counter. -/
theorem computationalSoundness_internal {Idx : Type} {Assumptions : IndAssumptions Idx}
      {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
      (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
      advBoundQWithError Assumptions q_b O o₁ o₂
        (assumptionCounting_low ind)
        (IndistinguishableI.statisticalError ind) := by
  induction ind with
  | assumption i =>
    intro dist hdepth
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError, advBoundWithError,
      AssumptionsUseT.empty]
    have huniv : (Finset.univ : Finset { x // x ∈ ({i} : Finset Idx) }) =
        {⟨i, Finset.mem_singleton_self i⟩} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, ?_⟩
      intro x _
      exact Subtype.ext (Finset.mem_singleton.mp x.2)
    rw [huniv, Finset.sum_singleton]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, NNReal.coe_zero,
      abs_nonpos_iff, sub_eq_zero]
    exact (ascToReal_identity dist (by simp)).symm
  | obsEqB q H =>
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError]
    exact advBoundQWithError_of_advBoundQ (obse_eq_step2 _ _ H)
  | approxEq ε H =>
    intro dist hdepth
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError, noAssumptionUse,
      AssumptionsUseT.empty, advBoundWithError] at hdepth ⊢
    simpa using H dist hdepth
  | reduction r q h ih =>
    intro dist hdepth
    have hprev := ih (OracleReduction.applyReductionToAdversary r dist) le_top
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError,
      advBoundWithError] at hprev ⊢
    have e1 := Finset.sum_congr
      (rfl (a := (Finset.univ : Finset { x // x ∈ (assumptionCounting_low h).1.subset })))
      (fun x _ => ascToReal_rcompose_map dist r ((assumptionCounting_low h).1.values x)
        (by simpa using ((assumptionCounting_low h).1.values x).2))
    have e2 := Finset.sum_congr
      (rfl (a := (Finset.univ : Finset { x // x ∈ (assumptionCounting_low h).2.subset })))
      (fun x _ => ascToReal_rcompose_map dist r ((assumptionCounting_low h).2.values x)
        (by simpa using ((assumptionCounting_low h).2.values x).2))
    rw [advantage_reduction, e1, e2]
    exact hprev
  | symm q h ih =>
    intro dist hdepth
    have hprev := ih dist hdepth
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError,
      advBoundWithError] at hprev ⊢
    have key : ∀ x y z : Real, x - (y - z) = -((-x) - (z - y)) := by intro x y z; ring
    rw [key, ← advantageReverse, abs_neg]
    exact hprev
  | trans rm q h₁ h₂ ih₁ ih₂ =>
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError]
    exact transitive_step_proof_error rm _ _ _ _ ih₁ ih₂
  | longSequence l q ro Hstep ihStep =>
    simp only [assumptionCounting_low, IndistinguishableI.statisticalError]
    exact long_step_error_induction
      (fun j Hq => assumptionCounting_low (Hstep j Hq))
      (fun j Hq => IndistinguishableI.statisticalError (Hstep j Hq))
      ihStep l (Nat.lt_succ_self l)

/- Symbolic soundness theorem - syntactic proofs presented as IndistinguishableI have semantic meaning! -/
theorem computationalSoundness {Idx : Type} {Assumptions : IndAssumptions Idx}
      {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
      (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
      advBoundQWithError Assumptions q_b O o₁ o₂
        (assumptionCountLower (assumptionCountingFin ind))
        (IndistinguishableI.statisticalError ind) :=
by
  rw [simpleCorrect]
  exact computationalSoundness_internal ind

/-- If an indistinguishability derivation has zero total statistical error, soundness
recovers the original exact equality with the combined assumption contribution. This
includes, in particular, derivations containing no `approxEq` steps. -/
theorem computationalSoundness_exact {Idx : Type} {Assumptions : IndAssumptions Idx}
      {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
      (ind : IndistinguishableI Assumptions q_b o₁ o₂)
      (herror : IndistinguishableI.statisticalError ind = 0) :
      advBoundQ Assumptions q_b O o₁ o₂
        (assumptionCountLower (assumptionCountingFin ind)) :=
by
  simp only [advBoundQ, advBound]
  intro distinguisher hdepth
  have hresidual := computationalSoundness ind distinguisher hdepth
  have hzero :
      |advantage distinguisher o₁ o₂ -
        ((∑ j : { x // x ∈ (assumptionCountLower (assumptionCountingFin ind)).1.subset },
            ascToReal distinguisher (Assumptions.assumptions j)
              (combine_red ((assumptionCountLower (assumptionCountingFin ind)).1.values j)))
         - (∑ j : { x // x ∈ (assumptionCountLower (assumptionCountingFin ind)).2.subset },
            ascToReal distinguisher (Assumptions.assumptions j)
              (combine_red ((assumptionCountLower (assumptionCountingFin ind)).2.values j))))| = 0 :=
    le_antisymm (by simpa [herror] using hresidual) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
