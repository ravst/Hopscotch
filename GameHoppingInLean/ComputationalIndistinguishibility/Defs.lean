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
  ℕ × (OracleReduction (Assumptions.assumptions J).O O)
structure AssumptionsUseT (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) where
  subset : Finset Assumptions.Idx
  values : (J : subset) -> (
    ℕ × (OracleReduction (Assumptions.assumptions J).O O)
  )

def positive {Assumptions : IndistinguishabilityAssumptions}
  {I : Type} {O : OracleSpec I} (x : AssumptionsUseT Assumptions O) : Prop :=
  forall i : x.subset, (x.values i).1 >= 1

def positiveP {Assumptions : IndistinguishabilityAssumptions}
  {I : Type} {O : OracleSpec I}
  (x : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O) : Prop :=
  positive x.1 ∧ positive x.2


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
    values := sumJoiner (fun J => asUseType Assumptions O J) val1.values val2.values joiner
  }




-- def advBound (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
--   {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
--   (asc : AssumptionsUseT Assumptions O)
--   [Fintype (Assumptions.Idx)]
--   (distinguisher : adversaryT O)
--   : Prop :=
--   -- forall distinguisher : adversaryT O,
--   FreeM.depth distinguisher ≤ q_b ->
--     (advantage distinguisher ro1 ro2) =
--     ∑ j, (asc.values j).1 *
--     advantage
--       (OracleReduction.applyReductionToAdversary (asc.values j).2 distinguisher)
--       (Assumptions.assumptions j).i.1 (Assumptions.assumptions j).i.2


def advBound2 (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
  {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  [Fintype (Assumptions.Idx)]
  (distinguisher : adversaryT O)
  : Prop :=
  -- forall distinguisher : adversaryT O,
  FreeM.depth distinguisher ≤ q_b ->
    (advantage distinguisher ro1 ro2) =
    ∑ j : { x // x ∈ asc.1.subset },
      ascToReal distinguisher (Assumptions.assumptions j) (asc.1.values j)
    - ∑ j : { x // x ∈ asc.2.subset },
       ascToReal distinguisher ((Assumptions.assumptions j)) (asc.2.values j)

-- lemma advBoundEq (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
--   {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
--   (asc : AssumptionsUseT Assumptions O)
--   (ascr : AssumptionsUseT Assumptions O)
--   [Fintype (Assumptions.Idx)]
--   (distinguisher : adversaryT O)
--   :
--   advBound Assumptions q_b O ro1 ro2 asc distinguisher =
--   advBound2 Assumptions q_b O ro1 ro2 asc distinguisher :=
-- by
--   simp [advBound2 , advBound, ascToReal]

def advBoundQ (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
  [Fintype (Assumptions.Idx)]
  {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
  (asc : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  : Prop :=
  forall (distinguisher : adversaryT O),
  advBound2 Assumptions q_b O ro1 ro2 asc distinguisher

noncomputable def obse_eq_step
  {Assumptions : IndistinguishabilityAssumptions} [Fintype (Assumptions.Idx)]
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : RStateOracle O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : { asc // advBoundQ Assumptions a O o₁ o₂ asc ∧ positiveP asc } :=
  ⟨(AssumptionsUseT.empty _ _, AssumptionsUseT.empty _ _), by
    constructor
    · simp [advBoundQ, advBound2, AssumptionsUseT.empty, advantage]
      intro dist
      apply obsEq_distinquishing_adv
      apply Hb
    · simp [AssumptionsUseT.empty, positiveP, positive]
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
  rw [hval1, hval2, hval3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h1 : j ∈ D1 <;> by_cases h2 : j ∈ D2
  · simpa [g1, g2, g3, sumJoiner, h1, h2, hj] using
      Hjoiner j h1 h2
  · simp [g1, g2, g3, sumJoiner, h1, h2, hj]
  · simp [g1, g2, g3, sumJoiner, h1, h2, hj]
  · simp [finsetSum, h1, h2] at hj

/-- The combined number of uses produced by `reductionCombiner` is at least one,
provided both inputs use their assumption at least once. -/
lemma reductionCombiner_fst_ge {I : Type} {O : OracleSpec I} (assumption : SingleAssumption)
  (x1 x2 : ℕ × (OracleReduction assumption.O O))
  (h1 : x1.1 ≥ 1) (h2 : x2.1 ≥ 1) :
  (reductionCombiner x1 x2).1 ≥ 1 := by
  have H : ∀ x : assumption.I, Nonempty (assumption.O x) := non_trivial_spec assumption.i.1
  rw [reductionCombiner, dif_pos H, reductionCombiner_nontrivial]
  omega

/-- `assumptionJoiner` preserves positivity, provided the joiner does. -/
lemma assumptionJoiner_positive {Assumptions : IndistinguishabilityAssumptions} {I : Type} {O : OracleSpec I}
  (val1 val2 : AssumptionsUseT Assumptions O)
  (joiner : {J : Assumptions.Idx} ->
    asUseType Assumptions O J -> asUseType Assumptions O J -> asUseType Assumptions O J)
  (H1 : positive val1) (H2 : positive val2)
  (Hjoiner : forall (J : Assumptions.Idx) (x1 x2 : asUseType Assumptions O J),
    x1.1 ≥ 1 -> x2.1 ≥ 1 -> (joiner x1 x2).1 ≥ 1)
  : positive (assumptionJoiner val1 val2 joiner) := by
  intro i
  obtain ⟨j, hj⟩ := i
  simp only [assumptionJoiner, sumJoiner]
  split_ifs with hd1 hd2 <;>
    first
    | exact H1 _
    | exact H2 _
    | exact Hjoiner j _ _ (H1 _) (H2 _)

/-- The joint assumption-use built in `transitive_step` is positive. -/
lemma transitive_step_positive {Assumptions : IndistinguishabilityAssumptions} {I : Type} {O : OracleSpec I}
  (asc1 asc2 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (H1 : positiveP asc1) (H2 : positiveP asc2) :
  positiveP (assumptionJoiner asc1.1 asc2.1 (fun a b => reductionCombiner a b),
             assumptionJoiner asc1.2 asc2.2 (fun a b => reductionCombiner a b)) := by
  refine ⟨?_, ?_⟩
  · exact assumptionJoiner_positive _ _ _ H1.1 H2.1
      (fun J x1 x2 hx1 hx2 => reductionCombiner_fst_ge _ x1 x2 hx1 hx2)
  · exact assumptionJoiner_positive _ _ _ H1.2 H2.2
      (fun J x1 x2 hx1 hx2 => reductionCombiner_fst_ge _ x1 x2 hx1 hx2)

noncomputable def transitive_step
  {Assumptions : IndistinguishabilityAssumptions} [Fintype (Assumptions.Idx)]
  {q_b : ℕ∞} {I : Type} {O : OracleSpec I}
  {o₁ o₂ : RStateOracle O} (rm : RStateOracle O)
  (as1 : {asc // advBoundQ Assumptions q_b O o₁ rm asc ∧ positiveP asc})
  (as2 : {asc // advBoundQ Assumptions q_b O rm o₂ asc ∧ positiveP asc}) :
  {asc // advBoundQ Assumptions q_b O o₁ o₂ asc ∧ positiveP asc}
:=
  let ⟨asc1, Hasc1⟩ := as1
  let ⟨asc2, Hasc2⟩ := as2
  let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => reductionCombiner a b)
  let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => reductionCombiner a b)
  ⟨(joint, jointr),
    (by
    constructor
    · simp [advBoundQ]
      intro dist
      simp [advBound2]
      intro Hdepth
      simp [joint, jointr, assumptionJoiner]
      have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
        asc1.1.values asc2.1.values (fun a b => reductionCombiner a b)
        (fun x => ascToReal dist _ x) (by
          intro j h1 h2
          apply reductionCombinerCorrect
          exact ⟨Hasc1.2.1 ⟨j, h1⟩, Hasc2.2.1 ⟨j, h2⟩⟩
        )
      simp [sumJoining] at HHx
      rw [<-HHx]
      clear HHx
      have HHx := sumJoinerCorrect' (fun J => asUseType Assumptions O J)
        asc1.2.values asc2.2.values (fun a b => reductionCombiner a b)
        (fun x => ascToReal dist _ x) (by
          intro j h1 h2
          apply reductionCombinerCorrect
          exact ⟨Hasc1.2.2 ⟨j, h1⟩, Hasc2.2.2 ⟨j, h2⟩⟩
        )
      simp [sumJoining] at HHx
      rw [<-HHx]
      clear HHx
      rw [(advatangeTriangle _ rm _)]
      -- rw [advBoundEq] at Hasc1 Hasc2
      -- simp [advBound2] at Hasc1 Hasc2
      rw [(Hasc1.1 dist Hdepth)]
      rw [(Hasc2.1 dist Hdepth)]
      simp []
      apply sub_add_sub_comm
    · exact transitive_step_positive asc1 asc2 Hasc1.2 Hasc2.2
    )
  ⟩

lemma nextInRange {n : ℕ} {x : ℕ} (H : x ∈ Finset.range n) : x ∈ Finset.range (n+1) :=
by
  refine Finset.mem_range_succ_iff.mpr ?_
  simp [Finset.range] at H
  exact Nat.le_of_succ_le H


def lengthOfIndI {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {κ : ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) -> ℕ
| IndistinguishableI.assumption idx =>
  0
| IndistinguishableI.obsEqB a b =>
  0
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind =>
  1 + lengthOfIndI ind
| IndistinguishableI.symm q_b ind  =>
  1 + lengthOfIndI ind
| IndistinguishableI.trans rm q_b ind1 ind2 =>
  1 + lengthOfIndI ind1 + lengthOfIndI ind2
| IndistinguishableI.longSequence a q_b ro Hseq =>
  1 + ∑ i : Finset.range a, lengthOfIndI (Hseq i (by
    cases i
    case mk val prop =>
    simp []
    exact List.mem_range.mp prop
  ))


theorem sum_ge_entry {X : Type u} {s : Finset X} (a : X) (ha : a ∈ s) (f : X -> ℕ):
    f a ≤ ∑ x ∈ s, f x :=
by
  apply Finset.single_le_sum
  · intro i Hi
    exact Nat.zero_le (f i)
  assumption

theorem sum_ge_entry2 {y : ℕ} {X : Type u} {s : Finset X} (a : X) (ha : a ∈ s) (f : X -> ℕ) (Hle : y <= f a):
    y ≤ ∑ x ∈ s, f x :=
by
  apply Nat.le_trans
  · apply Hle
  apply sum_ge_entry
  assumption

/-- Composing the stored reductions with a fixed reduction `r` (as done in the
`complexInitReduction` case of `symbolicSoundness`) preserves positivity, since the
number-of-uses components are left untouched. -/
lemma complexInit_positive {Assumptions : IndistinguishabilityAssumptions}
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (asc : AssumptionsUseT Assumptions O1 × AssumptionsUseT Assumptions O1)
  (r : OracleReduction O1 O2)
  (Hasc : positiveP asc) :
  positiveP
    (({ subset := asc.1.subset,
        values := fun x ↦ ((asc.1.values x).1, ComplexInitReduction2_compose (asc.1.values x).2 r) }
          : AssumptionsUseT Assumptions O2),
     ({ subset := asc.2.subset,
        values := fun x ↦ ((asc.2.values x).1, ComplexInitReduction2_compose (asc.2.values x).2 r) }
          : AssumptionsUseT Assumptions O2)) := by
  exact ⟨Hasc.1, Hasc.2⟩

noncomputable def symbolicSoundness {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {κ : ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) ->
      {asc // advBoundQ Assumptions q_b O o₁ o₂ asc ∧ positiveP asc}
| IndistinguishableI.assumption idx =>
  ⟨(
    {subset := {idx}, values := fun xp =>
      (1, by
        have hxp1 : xp.1 = idx := Finset.mem_singleton.mp xp.2
        rw [hxp1]
        exact OracleReduction.identity (Assumptions.assumptions idx).O)
    }, AssumptionsUseT.empty _ _),
    by
    constructor
    · simp [advBoundQ]
      intro dist
      simp [advBound2]
      intro Hdist
      simp [ascToReal]
      rw [applyComplexInitReduction2_identity]
      simp [AssumptionsUseT.empty]
    · refine ⟨?_, ?_⟩
      · intro i
        exact le_refl 1
      · simp [positive, AssumptionsUseT.empty]
  ⟩
| IndistinguishableI.obsEqB a b =>
  obse_eq_step o₁ o₂ b
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind => by
    let ⟨asc, Hasc⟩ := symbolicSoundness ind
    exact
      ⟨({
        subset := asc.1.subset
        values := fun x => ((asc.1.values x).1, ComplexInitReduction2_compose (asc.1.values x).2 r)
      },
      {
        subset := asc.2.subset
        values := fun x => ((asc.2.values x).1, ComplexInitReduction2_compose (asc.2.values x).2 r)
      }),
      by
      constructor
      · simp [advBoundQ]
        intro dist Hdist
        rw [advantage_reduction]
        simp [advBoundQ, advBound2] at Hasc
        rw [(Hasc.1 (OracleReduction.applyReductionToAdversary r dist) (by
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
      · exact complexInit_positive asc r Hasc.2
      ⟩
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundness ind
    ⟨(re.val.2, re.val.1), by
    constructor
    · simp [advBoundQ, advBound2]
      intro dist
      rw [advantageReverse]
      intro Hdist
      rw [re.2.1]
      · simp []
      · assumption
    · simp [positiveP]
      have X := re.2.2
      simp [positiveP] at X
      simp [X]
    ⟩
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step rm (symbolicSoundness ind1) (symbolicSoundness ind2)
| IndistinguishableI.longSequence a q_b ro Hseq => by
  have Hxx := fun (i : ℕ) (Hi : i < a) =>
    symbolicSoundness (Hseq i Hi)
  have HMain : forall (i : ℕ) (Hi : i < a+1),
    {asc //
      advBoundQ Assumptions q_b O (ro ⟨0, zero_in_range _⟩) (ro ⟨i, Finset.mem_range.mpr Hi⟩) asc
      ∧ positiveP asc}
  := (by
    intro i Hi
    induction i
    · apply obse_eq_step
      exact fun queriesList ↦ congrFun rfl
    case succ n Hind =>
      have long := Hind (Nat.lt_of_succ_lt Hi)
      apply transitive_step _ long
      apply Hxx n
      exact Nat.succ_lt_succ_iff.mp Hi
  )
  apply HMain
  exact lt_add_one a
termination_by ind => lengthOfIndI ind
decreasing_by
  all_goals simp [lengthOfIndI]
  · apply Nat.lt_add_right (lengthOfIndI ind2)
    exact lt_one_add (lengthOfIndI ind1)
  · apply Nat.lt_one_add_iff.mpr
    apply sum_ge_entry2 ⟨i, by
      simp [Finset.range, Hi]⟩
    · apply Finset.mem_attach
    · rfl
  -- sorry
