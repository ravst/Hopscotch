import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.OracleReductionsLemmas
import GameHoppingInLean.ObservationalEquvialence
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec
import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Misc.SimpAttrLemmas
import GameHoppingInLean.ComputationalIndistinguishibility.Distance
import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ComputationalIndistinguishibility.Sums
import GameHoppingInLean.ComputationalIndistinguishibility.ReductionCombiner
import GameHoppingInLean.ComputationalIndistinguishibility.ObsEqComp

-- generic intro. move.



abbrev asUseType (Assumptions : IndistinguishabilityAssumptions) {I : Type} (O : OracleSpec I) (J : Assumptions.Idx) :=
  ℕ ×  (OracleReduction (Assumptions.assumptions J).O O)
structure AssumptionsUseT (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) where
  subset : Finset Assumptions.Idx
  values : (J : subset) -> (
    ℕ × (OracleReduction (Assumptions.assumptions J).O O)
  )


namespace AssumptionsUseT

def empty (Assumptions : IndistinguishabilityAssumptions) {I : Type} (O : OracleSpec I) :
  AssumptionsUseT Assumptions O :=
  {
    subset := ∅,
    values := fun ⟨x, x2⟩ => by
      exfalso
      exact (List.mem_nil_iff x).mp x2
  }

end AssumptionsUseT

-- joiner for two assumption families, from local joiner. We use eta-expansion in values to help with simplifiaction process (otherwise it get stack)
def assumptionJoiner {Assumptions : IndistinguishabilityAssumptions} {I : Type} {O : OracleSpec I}
  (val1 val2 : AssumptionsUseT Assumptions O)
  (joiner : {J : Assumptions.Idx} ->
    asUseType Assumptions O J ->
    asUseType Assumptions O J ->
    asUseType Assumptions O J
  )
  : AssumptionsUseT Assumptions O :=
  {
    subset := finsetSum val1.subset val2.subset
    values := fun x => sumJoiner (fun J => asUseType Assumptions O J) val1.values val2.values joiner x
  }


def advBound (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (distinguisher : adversaryT O)
  : Prop :=
  FreeM.depth distinguisher ≤ q_b ->
    (advantage distinguisher ro1 ro2) =
    ∑ j : { x // x ∈ asc.1.subset },
      ascToReal distinguisher (Assumptions.assumptions j) (asc.1.values j)
    - ∑ j : { x // x ∈ asc.2.subset },
       ascToReal distinguisher ((Assumptions.assumptions j)) (asc.2.values j)

def advBoundQ (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  : Prop :=
  forall (distinguisher : adversaryT O),
  advBound Assumptions q_b O ro1 ro2 asc distinguisher

def noAssumptionUse {Assumptions : IndistinguishabilityAssumptions} : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O :=
  (AssumptionsUseT.empty _ _, AssumptionsUseT.empty _ _)

noncomputable def obse_eq_step2
  {Assumptions : IndistinguishabilityAssumptions}
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : RStateOracle O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : advBoundQ Assumptions a O o₁ o₂ (noAssumptionUse) :=
  by
    simp [advBoundQ, advBound, AssumptionsUseT.empty, advantage, noAssumptionUse]
    intro dist
    apply obsEq_distinquishing_adv
    apply Hb


noncomputable def obse_eq_step
  {Assumptions : IndistinguishabilityAssumptions}
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : RStateOracle O)
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



noncomputable def transitive_step_val
  {Assumptions : IndistinguishabilityAssumptions}
  {I : Type}
  {O : OracleSpec I}
  (asc1 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (asc2 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O) :
  AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O
:=
  let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => reductionCombiner a b)
  let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => reductionCombiner a b)
  (joint, jointr)


noncomputable def transitive_step_proof
  {Assumptions : IndistinguishabilityAssumptions}
  {q_b : ℕ∞} {I : Type} {O : OracleSpec I}
  {o₁ o₂ : RStateOracle O} (rm : RStateOracle O)
  (asc1 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (asc2 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (Hasc1 : advBoundQ Assumptions q_b O o₁ rm asc1)
  (Hasc2 : advBoundQ Assumptions q_b O rm o₂ asc2) :
  advBoundQ Assumptions q_b O o₁ o₂ (transitive_step_val asc1 asc2)
:= by
      let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => reductionCombiner a b)
      let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => reductionCombiner a b)
      simp [advBoundQ, transitive_step_val]
      intro dist
      simp [advBound]
      intro Hdepth
      simp [joint, jointr, assumptionJoiner]
      have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
        asc1.1.values asc2.1.values (fun a b => reductionCombiner a b)
        (fun x => ascToReal dist _ x) (by
          intro j h1 h2
          apply reductionCombinerCorrect
        )
      simp [sumJoining] at HHx
      rw [<-HHx]
      clear HHx
      have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
        asc1.2.values asc2.2.values (fun a b => reductionCombiner a b)
        (fun x => ascToReal dist _ x) (by
          intro j h1 h2
          apply reductionCombinerCorrect
        )
      simp [sumJoining] at HHx
      rw [<-HHx]
      clear HHx
      rw [(advatangeTriangle _ rm _)]
      rw [(Hasc1 dist Hdepth)]
      rw [(Hasc2 dist Hdepth)]
      simp []
      apply sub_add_sub_comm

lemma nextInRange {n : ℕ} {x : ℕ} (H : x ∈ Finset.range n) : x ∈ Finset.range (n+1) :=
by
  refine Finset.mem_range_succ_iff.mpr ?_
  simp [Finset.range] at H
  exact Nat.le_of_succ_le H


-- def lengthOfIndI {Assumptions : IndistinguishabilityAssumptions}
--       {κ : ℕ} {q_b : ENat}
--       {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
--       (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) -> ℕ
-- | IndistinguishableI.assumption idx =>
--   0
-- | IndistinguishableI.obsEqB a b =>
--   0
-- | @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind =>
--   1 + lengthOfIndI ind
-- | IndistinguishableI.symm q_b ind  =>
--   1 + lengthOfIndI ind
-- | IndistinguishableI.trans rm q_b ind1 ind2 =>
--   1 + lengthOfIndI ind1 + lengthOfIndI ind2
-- | IndistinguishableI.longSequence a q_b ro Hseq =>
--   1 + ∑ i : Finset.range a, lengthOfIndI (Hseq i (by
--     cases i
--     case mk val prop =>
--     simp []
--     exact List.mem_range.mp prop
--   ))


-- theorem sum_ge_entry {X : Type u} {s : Finset X} (a : X) (ha : a ∈ s) (f : X -> ℕ):
--     f a ≤ ∑ x ∈ s, f x :=
-- by
--   apply Finset.single_le_sum
--   · intro i Hi
--     exact Nat.zero_le (f i)
--   assumption

-- theorem sum_ge_entry2 {y : ℕ} {X : Type u} {s : Finset X} (a : X) (ha : a ∈ s) (f : X -> ℕ) (Hle : y <= f a):
--     y ≤ ∑ x ∈ s, f x :=
-- by
--   apply Nat.le_trans
--   · apply Hle
--   apply sum_ge_entry
--   assumption


noncomputable def long_step_combinator {O : OracleSpec I}
  {Assumptions : IndistinguishabilityAssumptions}
  :
  (a : ℕ) ->
  (Hxx : (i : ℕ) → i < a → AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O) ->
  AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O
| 0, _ =>
  noAssumptionUse
| Nat.succ a, Hxx =>
  let long := long_step_combinator a (fun i Hi => Hxx i (Nat.lt_succ_of_lt Hi))
  transitive_step_val long (Hxx a (Nat.lt_succ_self a))


noncomputable def symbolicSoundnessBound {Assumptions : IndistinguishabilityAssumptions}
      {κ : ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) ->
      AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O
| IndistinguishableI.assumption idx =>
  (
    {subset := {idx}, values := fun xp =>
      (1, by
        have hxp1 : xp.val = idx := Finset.mem_singleton.mp xp.2
        rw [hxp1]
        exact OracleReduction.identity (Assumptions.assumptions idx).O)
    }, AssumptionsUseT.empty _ _)
| IndistinguishableI.obsEqB a b =>
  noAssumptionUse
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind => by
    let asc := symbolicSoundnessBound ind
    exact
      ({
        subset := asc.1.subset
        values := fun x => ((asc.1.values x).1, ComplexInitReduction2_compose (asc.1.values x).2 r)
      },
      {
        subset := asc.2.subset
        values := fun x => ((asc.2.values x).1, ComplexInitReduction2_compose (asc.2.values x).2 r)
      })
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundnessBound ind
    (re.2, re.1)
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step_val (symbolicSoundnessBound ind1) (symbolicSoundnessBound ind2)
| IndistinguishableI.longSequence a q_b ro Hseq =>
  long_step_combinator a
    (fun j Hq => symbolicSoundnessBound (Hseq j Hq))



lemma long_Step_proof_induction
  {O : OracleSpec I}
  {Assumptions : IndistinguishabilityAssumptions}
  {q_b : ENat} {a : ℕ}
  {ro : Finset.range (a + 1) -> RStateOracle O}
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


noncomputable def symbolicSoundness {Assumptions : IndistinguishabilityAssumptions}
      {κ : ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) ->
      advBoundQ Assumptions q_b O o₁ o₂ (symbolicSoundnessBound ind)
| IndistinguishableI.assumption idx =>
  by
      simp [symbolicSoundnessBound]
      simp [advBoundQ]
      intro dist
      simp [advBound]
      intro Hdist
      simp [ascToReal]
      rw [applyComplexInitReduction2_identity]
      simp [AssumptionsUseT.empty]
| IndistinguishableI.obsEqB a b =>
  by
    simp [symbolicSoundnessBound]
    apply obse_eq_step2 _ _ b
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind => by
    let Hasc := symbolicSoundness ind
    simp [advBoundQ, symbolicSoundnessBound]
    intro dist Hdist
    rw [advantage_reduction]
    simp [advBoundQ, advBound] at Hasc
    rw [(Hasc (OracleReduction.applyReductionToAdversary r dist) (by
      exact sup_eq_left.mp rfl))]
    congr
    · ext j
      simp [ascToReal]
      rw [ComplexInitReduction2_compose_apply]
      simp []
    · ext j
      simp [ascToReal]
      rw [ComplexInitReduction2_compose_apply]
      simp []
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundness ind
    by
      simp [advBoundQ, advBound, symbolicSoundnessBound]
      intro dist
      rw [advantageReverse]
      intro Hdist
      rw [re]
      · simp []
      · assumption
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step_proof rm _ _ (symbolicSoundness ind1) (symbolicSoundness ind2)
| IndistinguishableI.longSequence a q_b ro Hseq => by
  simp [symbolicSoundnessBound]
  let Hxx := fun (i : ℕ) (Hi : i < a) =>
    symbolicSoundnessBound (Hseq i Hi)
  let HxxInd := (fun (i : ℕ) (Hi : i < a) => symbolicSoundness (Hseq i Hi))
  have X := long_Step_proof_induction Hxx (
      by
        simp [Hxx, symbolicSoundnessBound]
        apply HxxInd
      )
  apply X
  exact lt_add_one a
