import GameHoppingInLean.Comp.StatefulRandomOracle
import GameHoppingInLean.Comp.OracleReductions
import GameHoppingInLean.Comp.OracleReductionsLemmas
import GameHoppingInLean.ObservationalEq.Defs
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec
import GameHoppingInLean.Indistinguishability.Def
import GameHoppingInLean.Tactic.SimpAttrLemmas
import GameHoppingInLean.ComputationalIndistinguishibility.Distance
import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ComputationalIndistinguishibility.Sums
-- import GameHoppingInLean.ComputationalIndistinguishibility.ReductionCombiner
import GameHoppingInLean.ComputationalIndistinguishibility.ReductionCombinerList
import GameHoppingInLean.ComputationalIndistinguishibility.AssumptionCounting

import GameHoppingInLean.ComputationalIndistinguishibility.ObsEqComp
import GameHoppingInLean.Tactic.Defs


/- # Soundness theorem
  Here we define the soundness theorem. It relates advantage of adversary A against original protocol to advantage of ∑_i n_i * advantage of (A.compose R_i) against assumption i.

  Here R_i, n_i are computed from result of assumption counting function `assumptionCountingFin` (see AssumptionCounting.lean for more on it). For each assumption, `assumptionCountingFin` returns a list of reductions l. R_i is a reduction that picks one reduction from l uniformly at random and executes it. n_i = l.length .

  We express this sum using function `advBound`. The soundness theorem is called `symbolicSoundness` and can be found at the very end of file. The name comes from the fact that syntactic proofs presented as IndistinguishabilityI are shown to have semantic meaning. See paper for more high level discussion.

  The soundness theorem is proven by induction on the IndistinguishabilityI. The trans step requires reasoning about 'pick-one-at-random' reduction combination -- more details on it are in ReductionCombiner.lean.
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


lemma obse_eq_step2
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : OracleImpl O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : advBoundQ Assumptions a O o₁ o₂ (noAssumptionUse) :=
  by
    simp [advBoundQ, advBound, AssumptionsUseT.empty, advantage, noAssumptionUse]
    intro dist
    apply obsEq_distinquishing_adv
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
    apply obsEq_distinquishing_adv
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
      rw [(advatangeTriangle _ rm _)]
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

/-- version of symbolic soundness theorem that uses `assumptionCounting_low` counting function -/
lemma symbolicSoundness_internal {Idx : Type} {Assumptions : IndAssumptions Idx}
      {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O} :
      (ind : IndistinguishableI Assumptions q_b o₁ o₂) ->
      advBoundQ Assumptions q_b O o₁ o₂ (assumptionCounting_low ind)
| IndistinguishableI.assumption idx =>
  by
      simp [assumptionCounting_low]
      simp [advBoundQ]
      intro dist
      simp [advBound]
      intro Hdist
      simp [AssumptionsUseT.empty]
      rw [ascToRealFromObsEq _ (1, OracleReduction.identity (Assumptions.assumptions idx).O)]
      case H2 =>
        simp [combine_red]
        intro impl
        apply combine_red_singleton
        apply non_trivial_spec
        apply impl
      case H1 =>
        simp [combine_red]
      simp [ascToReal]
      rw [applyreduction2_identity]
| IndistinguishableI.obsEqB a b =>
  by
    simp [assumptionCounting_low]
    apply obse_eq_step2 _ _ b
| IndistinguishableI.reduction r b ind => by
    let Hasc := symbolicSoundness_internal ind
    simp [advBoundQ, assumptionCounting_low]
    intro dist Hdist
    rw [advantage_reduction]
    simp [advBoundQ, advBound] at Hasc
    rw [(Hasc (OracleReduction.applyReductionToAdversary r dist) (by
      exact sup_eq_left.mp rfl))]
    congr
    · ext j
      simp [ascToReal]
      simp [combine_red]
      apply Or.inl
      apply adv_from_bobseq
      intro impl
      rw [<-rcompose_apply]
      rw [<-goodDoubleAction]
      rw [<-goodDoubleAction]
      simp [compose_combine]
    · ext j
      simp [ascToReal]
      simp [combine_red]
      apply Or.inl
      apply adv_from_bobseq
      intro impl
      rw [<-rcompose_apply]
      rw [<-goodDoubleAction]
      rw [<-goodDoubleAction]
      simp [compose_combine]
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundness_internal ind
    by
      simp [advBoundQ, advBound, assumptionCounting_low]
      intro dist
      rw [advantageReverse]
      intro Hdist
      rw [re]
      · simp []
      · assumption
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step_proof rm _ _ (symbolicSoundness_internal ind1) (symbolicSoundness_internal ind2)
| IndistinguishableI.longSequence a q_b ro Hseq => by
  simp [assumptionCounting_low]
  let Hxx := fun (i : ℕ) (Hi : i < a) =>
    assumptionCounting_low (Hseq i Hi)
  let HxxInd := (fun (i : ℕ) (Hi : i < a) => symbolicSoundness_internal (Hseq i Hi))
  have X := long_Step_proof_induction Hxx (
      by
        simp [Hxx, assumptionCounting_low]
        apply HxxInd
      )
  apply X
  exact lt_add_one a

/- Symbolic soundness theorem - syntactic proofs presented as IndistinguishabilityI have semantic meaning! -/
theorem symbolicSoundness {Idx : Type} {Assumptions : IndAssumptions Idx}
      {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
      (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
      advBoundQ Assumptions q_b O o₁ o₂ (assumptionCountLower (assumptionCountingFin ind)) :=
by
  rw [simpleCorrect]
  apply symbolicSoundness_internal
