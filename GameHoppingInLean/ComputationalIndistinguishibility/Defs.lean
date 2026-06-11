import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
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




def advBound (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)
    [Fintype (Assumptions.Idx)]
    : Prop :=
    forall distinguisher,
      FreeM.depth distinguisher ≤ q_b ->
      (advantage distinguisher ro1 ro2) <= ∑ j,
        (asc.values j).1 *
        advantage
          (OracleReduction.applyReductionToAdversary (asc.values j).2 distinguisher)
          (Assumptions.assumptions j).i.1 (Assumptions.assumptions j).i.2


def advBound2 (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)
    [Fintype (Assumptions.Idx)]
    : Prop :=
    forall distinguisher,
      FreeM.depth distinguisher ≤ q_b ->
      (advantage distinguisher ro1 ro2) <= ∑ j : { x // x ∈ asc.subset },
        ascToReal distinguisher (Assumptions.assumptions j) (asc.values j)

lemma advBoundEq (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)
    [Fintype (Assumptions.Idx)] :
    advBound Assumptions q_b O ro1 ro2 asc = advBound2 Assumptions q_b O ro1 ro2 asc :=
by
  simp [advBound2 , advBound, ascToReal]



noncomputable def obse_eq_step
  {Assumptions : IndistinguishabilityAssumptions} [Fintype (Assumptions.Idx)]
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : RStateOracle O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : { asc // advBound Assumptions a O o₁ o₂ asc } :=
  ⟨AssumptionsUseT.empty _ _, by
      simp [advBound, AssumptionsUseT.empty]
      intro dist
      apply obsEq_distinquishing
      apply Hb
  ⟩

noncomputable def transitive_step
  {Assumptions : IndistinguishabilityAssumptions} [Fintype (Assumptions.Idx)]
  {q_b : ℕ∞} {I : Type} {O : OracleSpec I}
  {o₁ o₂ : RStateOracle O} (rm : RStateOracle O)
  (as1 : {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O o₁ rm asc})
  (as2 : {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O rm o₂ asc})
  : {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O o₁ o₂ asc} :=
    let ⟨asc1, Hasc1⟩ := as1
    let ⟨asc2, Hasc2⟩ := as2
    let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1 asc2 (fun a b => reductionCombiner a b)
    ⟨joint,
      (by
        rw [advBoundEq]
        simp [advBound2]
        intro dist Hdepth
        simp [joint, assumptionJoiner]
        have HHx := sumJoinerCorrect (fun J => asUseType Assumptions O J)
          asc1.values asc2.values (fun a b => reductionCombiner a b)
          (fun x => ascToReal dist _ x) (by
            intro j x1 x2
            simp []
            apply reductionCombinerCorrect
          )
        simp [sumJoining] at HHx
        rw [<-HHx]
        clear HHx
        apply le_trans (advatangeTriangle _ rm _)
        -- apply advatangeTriangle _ rm _
        rw [advBoundEq] at Hasc1 Hasc2
        simp [advBound2] at Hasc1 Hasc2
        have L1 := add_le_add (Hasc1 dist Hdepth) (Hasc2 dist Hdepth)
        apply L1
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

noncomputable def symbolicSoundness {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {κ : ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) ->
      {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O o₁ o₂ asc}
| IndistinguishableI.assumption idx =>
  ⟨{ subset := {idx}, values := fun xp => by
      cases xp
      case mk xp' Hxp =>
      simp []
      simp at Hxp
      rw [Hxp]
      exact (1, OracleReduction.identity (Assumptions.assumptions idx).O) },
    by
      simp [advBound]
      intro dist Hdist
      rw [OracleReduction.applyComplexInitReduction2_identity]
  ⟩
| IndistinguishableI.obsEqB a b =>
  obse_eq_step o₁ o₂ b
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind => by
    let ⟨asc, Hasc⟩ := symbolicSoundness ind
    exact
      ⟨{
        subset := asc.subset
        values := fun x => ((asc.values x).1, OracleReduction.ComplexInitReduction2_compose (asc.values x).2 r)
      },
      by
        simp [advBound]
        intro dist Hdist
        rw [advantage_reduction]
        simp [advBound] at Hasc
        apply le_trans (Hasc (OracleReduction.applyReductionToAdversary r dist) (by
          exact sup_eq_left.mp rfl))
        apply le_of_eq
        congr
        ext j
        rw [OracleReduction.ComplexInitReduction2_compose_apply]
      ⟩
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundness ind
    ⟨re.val, by
      simp [advBound]
      intro dist
      simp [advantage]
      rw [disPMFSymm]
      apply re.2
      ⟩
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step rm (symbolicSoundness ind1) (symbolicSoundness ind2)
| IndistinguishableI.longSequence a q_b ro Hseq => by
  have Hxx := fun (i : ℕ) (Hi : i < a) =>
    symbolicSoundness (Hseq i Hi)
  have HMain : forall (i : ℕ) (Hi : i < a+1),
    {asc : AssumptionsUseT Assumptions O //
      advBound Assumptions q_b O (ro ⟨0, zero_in_range _⟩) (ro ⟨i, Finset.mem_range.mpr Hi⟩) asc}
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
