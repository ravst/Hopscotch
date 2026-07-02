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
import GameHoppingInLean.IndistinguishabilityTactics

-- generic intro. move.


abbrev asUseType (Assumptions : IndistinguishabilityAssumptions) {I : Type} (O : OracleSpec I) (J : Assumptions.Idx) :=
  {x : List (OracleReduction (Assumptions.assumptions J).O O) // x.length > 0}

noncomputable def reduction_combiner_list_full
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : {x : List (OracleReduction O1 O2) // x.length > 0})
  : OracleReduction O1 O2 :=
  open Classical in
  if H : forall i, Nonempty (O1 i) then
    reduction_combiner_list l.val l.2 H
  else
    reductionFromEmpty H

noncomputable def combine_red
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : {x : List (OracleReduction O1 O2) // x.length > 0})
  : ℕ × OracleReduction O1 O2 :=
    (l.1.length, reduction_combiner_list_full l)

attribute [local game_hopping_unfold] combine_red reduction_combiner_list_full reduction_combiner_list


noncomputable def combine_red_singleton
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : (OracleReduction O1 O2))
  (H : [l].length > 0)
  (H2 : forall i, Nonempty (O1 i))
  (impl : RStateOracle O1)
  :
  ObsEq
    ((reduction_combiner_list_full ⟨[l], H⟩).apply impl)
    (l.apply impl) := by
    simp [combine_red, reduction_combiner_list_full, H2]
    unfold reduction_combiner_list
    simp [internal_type]
    apply ObsEq.symm
    obs_eq_by_abstraction (fun x =>
      by
        unfold OracleReduction.apply
        unfold OracleReduction.apply at x
        simp at x
        simp []
        exact (
          {
            index := 0,
            value := x.1
          }, x.2)
      )
    · intro query
      ext1 s1
      ext1 s2
      have H2 : forall x : Fin [l].length, x=0 := by
        simp [Fin, List.length]
      have H3 : forall x : internal_type [l], x.index=0 := by
        simp [H2]
      conv =>
        rhs
        arg 1
        arg 2
        arg 2
        intro a
        simp [H3]
        arg 2
        arg 2
        intro x
        arg 2
        simp [H2]
      simp [mapInputState, RStateSimplifier, StateTSimps, internal_type, OracleReductionSimps]
      -- rw [addToStateG_spec]
      sorry
    · sorry


def listCombiner (l1 l2 : {x : List X // x.length > 0}) : {x : List X // x.length > 0} :=
  ⟨l1.1++l2.1, by simp [l1.2, l2.2]⟩


lemma reduction_combiner_correct_full
  {I1 : Type} {O1 : OracleSpec I1}
  (dist : OracleComp (withPMFSpec O1) Bool)
  (assumption : SingleAssumption)
  (l1 l2 : {x : List (OracleReduction assumption.O O1) // x.length > 0})
  : ascToReal dist assumption (combine_red l1) +
    ascToReal dist assumption (combine_red l2) =
  ascToReal dist assumption (combine_red (listCombiner l1 l2)) :=
by
    have He := non_trivial_spec assumption.i.1
    have inst1 :  Nonempty (reduction_combiner_list l1.1 l1.2 He).stateType :=
       reductionNonEmpty _ He
    have inst2 :  Nonempty (reduction_combiner_list l2.1 l2.2 He).stateType :=
        reductionNonEmpty _ He
    unfold combine_red
    unfold listCombiner
    unfold reduction_combiner_list_full
    simp [He]
    apply reduction_combiner_correct


lemma compose_combine {I1 : Type} (O1 : OracleSpec I1)
  {I2 : Type} (O2 : OracleSpec I2)
  {I3 : Type} (O3 : OracleSpec I3)
  (r1 : OracleReduction O2 O3)
  (l : {x : List (OracleReduction O1 O2) // x.length > 0})
  (impl : RStateOracle O1) (dist : adversaryT O3):
  runDinstinguisher dist
    ((ComplexInitReduction2_compose (reduction_combiner_list_full l) r1).apply impl) =
  runDinstinguisher dist
    ((reduction_combiner_list_full ⟨l.val.map (fun x => ComplexInitReduction2_compose x r1),
      by simp [l.2]
    ⟩).apply impl)
 :=
  sorry

-- inductive AssumptionUse {I1 : Type} (O1 : OracleSpec I1) : {I : Type} -> (O: OracleSpec I) -> Type 1
-- | SingleAssumption {I : Type} {O: OracleSpec I} (r : OracleReduction O1 O) : AssumptionUse O1 O
-- | Listing {I : Type} {O: OracleSpec I} (n : ℕ) (l : Fin n -> (AssumptionUse O1 O)) (H : n > 0): AssumptionUse O1 O
-- | Reduction {I2 : Type} {O2: OracleSpec I2} {I3 : Type} {O3: OracleSpec I2}
--   (r : OracleReduction O2 O3) (x : AssumptionUse O1 O2)
--   : AssumptionUse O1 O3

-- def toList (T : Type _) (n : ℕ) (l : Fin n -> T) : List T :=
--   List.ofFn l


-- noncomputable def introReduction {I1 : Type} (O1 : OracleSpec I1) {I2 : Type} (O2 : OracleSpec I2) :
--   (r : AssumptionUse O1 O2) -> OracleReduction O1 O2
-- | AssumptionUse.SingleAssumption r => r
-- | AssumptionUse.Listing n l Hn =>
--   let tl := (List.ofFn (fun i => introReduction O1 O2 (l i)))
--   reduction_combiner_list_full tl (by
--     simp [List.length_map, tl, Hn])
-- | @AssumptionUse.Reduction I1 O1 I2 O2 I3 O3 r x => ComplexInitReduction2_compose (introReduction O1 O2 x) r

structure AssumptionsUseT (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) where
  subset : Finset Assumptions.Idx
  values : (J : subset) -> (
    {x : List (OracleReduction (Assumptions.assumptions J).O O) // x.length > 0}
  )


def AssumptionsUseTSimple (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) :=
  (J : Assumptions.Idx) -> List (OracleReduction (Assumptions.assumptions J).O O)


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
      ascToReal distinguisher (Assumptions.assumptions j) (combine_red (asc.1.values j))
    - ∑ j : { x // x ∈ asc.2.subset },
       ascToReal distinguisher ((Assumptions.assumptions j)) (combine_red (asc.2.values j))

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
  let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => listCombiner a b)
  let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => listCombiner a b)
  (joint, jointr)


noncomputable def transitive_step_val_simple
  {Assumptions : IndistinguishabilityAssumptions}
  {I : Type}
  {O : OracleSpec I}
  (asc1 : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O)
  (asc2 : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O) :
  AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O
:=
  ((fun x => (asc1.1 x)++(asc2.1 x)), fun x => (asc1.2 x)++(asc2.2 x))

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
      let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => listCombiner a b)
      let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => listCombiner a b)
      simp [advBoundQ, transitive_step_val]
      intro dist
      simp [advBound]
      intro Hdepth
      simp [joint, jointr, assumptionJoiner]
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

noncomputable def long_step_combinator_simple_half {O : OracleSpec I}
  {Assumptions : IndistinguishabilityAssumptions}
  (a : ℕ)
  (Hxx : (i : ℕ) → i < a → AssumptionsUseTSimple Assumptions O) :
  AssumptionsUseTSimple Assumptions O := fun idx =>
  let l := List.ofFn (fun x => Hxx x.1 x.2 idx)
  l.flatten

noncomputable def long_step_combinator_simple {O : OracleSpec I}
  {Assumptions : IndistinguishabilityAssumptions}
  (a : ℕ)
  (Hxx : (i : ℕ) → i < a → AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O) :
  AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O :=
  (
    long_step_combinator_simple_half a (fun x Hx => (Hxx x Hx).1),
    long_step_combinator_simple_half a (fun x Hx => (Hxx x Hx).2)
  )


noncomputable def symbolicSoundnessBound {Assumptions : IndistinguishabilityAssumptions}
      {κ : ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) ->
      AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O
| IndistinguishableI.assumption idx =>
  (
    {subset := {idx}, values := fun xp =>
      (by
        have hxp1 : xp.val = idx := Finset.mem_singleton.mp xp.2
        rw [hxp1]
        let ret := OracleReduction.identity (Assumptions.assumptions idx).O
        exact ⟨(List.cons ret List.nil), by simp⟩
      )
    }, AssumptionsUseT.empty _ _)
| IndistinguishableI.obsEqB a b =>
  noAssumptionUse
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind => by
    let asc := symbolicSoundnessBound ind
    exact
      ({
        subset := asc.1.subset
        values := fun x => ⟨(asc.1.values x).1.map (fun x => ComplexInitReduction2_compose x r), by
        simp [(asc.1.values x).2]⟩
      },
      {
        subset := asc.2.subset
        values := fun x => ⟨(asc.2.values x).1.map (fun x => ComplexInitReduction2_compose x r), by
        simp [(asc.2.values x).2]⟩
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


noncomputable def symbolicSoundnessBound2 {Assumptions : IndistinguishabilityAssumptions}
  {κ : ℕ} {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
  (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) ->
  AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O
| IndistinguishableI.assumption idx =>
  (
    fun xp =>
      if H : xp = idx then [H ▸ OracleReduction.identity (Assumptions.assumptions idx).O]
        else []
  , fun _ => [])
| IndistinguishableI.obsEqB a b =>
  (fun _ => [], fun _ => [])
| @IndistinguishableI.complexInitReduction Assumptions κ I1 I2 O1 O2 r ro1 o₁ b ind =>
    let asc := symbolicSoundnessBound2 ind
    (
      (fun x => (asc.1 x).map (fun x => ComplexInitReduction2_compose x r)),
      (fun x => (asc.2 x).map (fun x => ComplexInitReduction2_compose x r)),
    )
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundnessBound2 ind
    (re.2, re.1)
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step_val_simple (symbolicSoundnessBound2 ind1) (symbolicSoundnessBound2 ind2)
| IndistinguishableI.longSequence a q_b ro Hseq =>
  long_step_combinator_simple a
    (fun j Hq => symbolicSoundnessBound2 (Hseq j Hq))

def finite_support {Assumptions : IndistinguishabilityAssumptions}
  {κ : ℕ} {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O}
  (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) :
  let ret := symbolicSoundnessBound2 ind
  Fintype {x | ret.1 x ≠ []} ×
  Fintype {x | ret.2 x ≠ []} := sorry

def AssumptionsUseTSimple2other {Assumptions : IndistinguishabilityAssumptions}
  {I : Type} {O : OracleSpec I} (count : AssumptionsUseTSimple Assumptions O)
  (H : Fintype {i | count i ≠ []})
  : AssumptionsUseT Assumptions O :=
  {
    subset := ({i | count i ≠ []} : Set Assumptions.Idx).toFinset,
    values a := ⟨count a,
      by
        simp [List.length, List.length_pos_iff]
        grind only [= Set.mem_toFinset, usr Set.mem_setOf_eq]
      ⟩
  }

def AssumptionsUseTSimplePair2other {Assumptions : IndistinguishabilityAssumptions}
  {I : Type} {O : OracleSpec I}
  (count : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O)
  (H : Fintype {i | count.1 i ≠ []} × Fintype {i | count.2 i ≠ []})
  : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O :=
  (AssumptionsUseTSimple2other count.1 H.1, AssumptionsUseTSimple2other count.2 H.2)


lemma simpleCorrect {Assumptions : IndistinguishabilityAssumptions}
  {κ : ℕ} {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O}
  (ind : IndistinguishableI Assumptions κ q_b O o₁ o₂) :
  AssumptionsUseTSimplePair2other (symbolicSoundnessBound2 ind) (finite_support ind) =
    symbolicSoundnessBound ind :=
by
  sorry

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
      rw [applyComplexInitReduction2_identity]
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
      simp [combine_red]
      apply Or.inl
      apply adv_from_bobseq
      intro impl
      rw [<-ComplexInitReduction2_compose_apply]
      rw [<-goodDoubleAction]
      rw [<-goodDoubleAction]
      simp [compose_combine]
    · ext j
      simp [ascToReal]
      simp [combine_red]
      apply Or.inl
      apply adv_from_bobseq
      intro impl
      rw [<-ComplexInitReduction2_compose_apply]
      rw [<-goodDoubleAction]
      rw [<-goodDoubleAction]
      simp [compose_combine]
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
