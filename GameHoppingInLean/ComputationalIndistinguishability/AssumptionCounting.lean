import GameHoppingInLean.Indistinguishability.Def
import GameHoppingInLean.ComputationalIndistinguishability.Sums
import GameHoppingInLean.ComputationalIndistinguishability.ReductionCombinerList

/-
# Assumption Counting
We define an assumption use counting function `assumptionCounting`. For each assumption idx,
It returns a list of its uses. For each use, we put on the list the reduction from original problem to given assumption. In other words, for each use we put the composition of all reduction steps appearing above given assumption use.
In fact, we return a pair of such objects - first for original assumption use and then for use of its symmetric variant. Whenever assumption is used the parity of number of symm constructors above it determines whether we count it as the use of original or symmetric version.
   -/

abbrev asUseType {Idx : Type} (Assumptions : IndAssumptions Idx) {I : Type} (O : OracleSpec I) (J : Idx) :=
  {x : List (OracleReduction (Assumptions.assumptions J).O O) // x.length > 0}

structure AssumptionsUseT {Idx : Type} (Assumptions : IndAssumptions Idx)
  {I : Type} (O : OracleSpec I) where
  subset : Finset Idx
  values : (J : subset) -> (
    {x : List (OracleReduction (Assumptions.assumptions J).O O) // x.length > 0}
  )


def AssumptionsUseTSimple {Idx : Type} (Assumptions : IndAssumptions Idx)
  {I : Type} (O : OracleSpec I) :=
  (J : Idx) -> List (OracleReduction (Assumptions.assumptions J).O O)


namespace AssumptionsUseT

def empty {Idx : Type} (Assumptions : IndAssumptions Idx) {I : Type} (O : OracleSpec I) :
  AssumptionsUseT Assumptions O :=
  {
    subset := ∅,
    values := fun ⟨x, x2⟩ => by
      exfalso
      exact (List.mem_nil_iff x).mp x2
  }

end AssumptionsUseT

noncomputable def transitive_step_val_simple
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {I : Type}
  {O : OracleSpec I}
  (asc1 : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O)
  (asc2 : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O) :
  AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O
:=
  ((fun x => (asc1.1 x)++(asc2.1 x)), fun x => (asc1.2 x)++(asc2.2 x))

noncomputable def long_step_combinator_simple_half {O : OracleSpec I}
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  (a : ℕ)
  (Hxx : (i : ℕ) → i < a → AssumptionsUseTSimple Assumptions O) :
  AssumptionsUseTSimple Assumptions O := fun idx =>
  let l := List.ofFn (fun x => Hxx x.1 x.2 idx)
  l.flatten

lemma long_step_combinator_simple_half_next {O : OracleSpec I}
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  (a : ℕ)
  (Hxx : (i : ℕ) → i < (a + 1) → AssumptionsUseTSimple Assumptions O) :
long_step_combinator_simple_half (a + 1) Hxx = fun idx =>
long_step_combinator_simple_half a (fun i Ha => Hxx i (Nat.lt_succ_of_lt Ha)) idx ++
  (Hxx a (lt_add_one a) idx) := by
  funext idx
  simp only [long_step_combinator_simple_half, List.ofFn_succ_last, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, Fin.val_castSucc, Fin.val_last]

noncomputable def long_step_combinator_simple {O : OracleSpec I}
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  (a : ℕ)
  (Hxx : (i : ℕ) → i < a → AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O) :
  AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O :=
  (
    long_step_combinator_simple_half a (fun x Hx => (Hxx x Hx).1),
    long_step_combinator_simple_half a (fun x Hx => (Hxx x Hx).2)
  )

noncomputable def assumptionCounting {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O} :
  (ind : IndistinguishableI Assumptions q_b o₁ o₂) ->
  AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O
:=
  haveI : DecidableEq Idx := Assumptions.decEq
  fun ind => match ind with
  | IndistinguishableI.assumption idx =>
    (
      fun xp =>
        if H : xp = idx then [H ▸ OracleReduction.identity (Assumptions.assumptions idx).O]
          else []
    , fun _ => [])
  | IndistinguishableI.obsEqB a b =>
    (fun _ => [], fun _ => [])
  | IndistinguishableI.reduction r b ind =>
      let asc := assumptionCounting ind
      (
        (fun x => (asc.1 x).map (fun x => rcompose x r)),
        (fun x => (asc.2 x).map (fun x => rcompose x r)),
      )
  | IndistinguishableI.symm q_b ind  =>
      let re := assumptionCounting ind
      (re.2, re.1)
  | IndistinguishableI.trans rm q_b ind1 ind2 =>
      transitive_step_val_simple (assumptionCounting ind1) (assumptionCounting ind2)
  | IndistinguishableI.longSequence a q_b ro Hseq =>
    long_step_combinator_simple a
      (fun j Hq => assumptionCounting (Hseq j Hq))


/- # Alternative assumption counting function
for the soundness proof, it is more convenient to use a different assumption counting function, defined below. It is better for the proof, but worse for humans. We prove equivalence later.
-/

-- joiner for two assumption families, from local joiner. We use eta-expansion in values to help with simplifiaction process (otherwise it get stack)
def assumptionJoiner {Idx : Type} {Assumptions : IndAssumptions Idx} {I : Type} {O : OracleSpec I}
  (val1 val2 : AssumptionsUseT Assumptions O)
  (joiner : {J : Idx} ->
    asUseType Assumptions O J ->
    asUseType Assumptions O J ->
    asUseType Assumptions O J
  )
  : AssumptionsUseT Assumptions O :=
  haveI : DecidableEq Idx := Assumptions.decEq
  {
    subset := finsetSum val1.subset val2.subset
    values := fun x => sumJoiner (fun J => asUseType Assumptions O J) val1.values val2.values joiner x
  }



noncomputable def transitive_step_val
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  {I : Type}
  {O : OracleSpec I}
  (asc1 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (asc2 : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O) :
  AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O
:=
  let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1.1 asc2.1 (fun a b => listCombiner a b)
  let jointr : AssumptionsUseT Assumptions O := assumptionJoiner asc1.2 asc2.2 (fun a b => listCombiner a b)
  (joint, jointr)




def noAssumptionUse {Idx : Type} {Assumptions : IndAssumptions Idx} : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O :=
  (AssumptionsUseT.empty _ _, AssumptionsUseT.empty _ _)

noncomputable def long_step_combinator {O : OracleSpec I}
  {Idx : Type} {Assumptions : IndAssumptions Idx}
  :
  (a : ℕ) ->
  (Hxx : (i : ℕ) → i < a → AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O) ->
  AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O
| 0, _ =>
  noAssumptionUse
| Nat.succ a, Hxx =>
  let long := long_step_combinator a (fun i Hi => Hxx i (Nat.lt_succ_of_lt Hi))
  transitive_step_val long (Hxx a (Nat.lt_succ_self a))


noncomputable def assumptionCounting_low {Idx : Type} {Assumptions : IndAssumptions Idx}
      {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O} :
      (ind : IndistinguishableI Assumptions q_b o₁ o₂) ->
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
| IndistinguishableI.reduction r b ind => by
    let asc := assumptionCounting_low ind
    exact
      ({
        subset := asc.1.subset
        values := fun x => ⟨(asc.1.values x).1.map (fun x => rcompose x r), by
        simp [(asc.1.values x).2]⟩
      },
      {
        subset := asc.2.subset
        values := fun x => ⟨(asc.2.values x).1.map (fun x => rcompose x r), by
        simp [(asc.2.values x).2]⟩
      })
| IndistinguishableI.symm q_b ind  =>
    let re := assumptionCounting_low ind
    (re.2, re.1)
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step_val (assumptionCounting_low ind1) (assumptionCounting_low ind2)
| IndistinguishableI.longSequence a q_b ro Hseq =>
  long_step_combinator a
    (fun j Hq => assumptionCounting_low (Hseq j Hq))

-- below we prove that these two function are equivalent:

lemma assumptionCounting_finite {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
  (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
  {x | (assumptionCounting ind).1 x ≠ []}.Finite ∧
  {x | (assumptionCounting ind).2 x ≠ []}.Finite := by
  induction ind with
  | assumption idx =>
    refine ⟨?_, ?_⟩
    · apply Set.Finite.subset (Set.finite_singleton idx)
      intro x hx
      simp only [assumptionCounting, ne_eq, Set.mem_setOf_eq] at hx
      simp only [Set.mem_singleton_iff]
      by_contra hne
      rw [dif_neg hne] at hx
      exact hx rfl
    · simp only [assumptionCounting]
      simp
  | obsEqB a b =>
    refine ⟨?_, ?_⟩ <;> (simp only [assumptionCounting]; simp)
  | reduction a b ind0 Hih =>
    refine ⟨?_, ?_⟩
    · apply Set.Finite.subset Hih.1
      intro x hx
      simp only [assumptionCounting, ne_eq, Set.mem_setOf_eq, List.map_eq_nil_iff] at hx ⊢
      exact hx
    · apply Set.Finite.subset Hih.2
      intro x hx
      simp only [assumptionCounting, ne_eq, Set.mem_setOf_eq, List.map_eq_nil_iff] at hx ⊢
      exact hx
  | symm q_b ind0 HInd =>
    refine ⟨?_, ?_⟩
    · simp only [assumptionCounting]; exact HInd.2
    · simp only [assumptionCounting]; exact HInd.1
  | trans rm q_b ind1 ind2 Hind1 Hind2 =>
    refine ⟨?_, ?_⟩
    · apply Set.Finite.subset (Hind1.1.union Hind2.1)
      intro x hx
      simp only [assumptionCounting, transitive_step_val_simple, ne_eq, Set.mem_setOf_eq,
        List.append_eq_nil_iff, Set.mem_union] at hx ⊢
      tauto
    · apply Set.Finite.subset (Hind1.2.union Hind2.2)
      intro x hx
      simp only [assumptionCounting, transitive_step_val_simple, ne_eq, Set.mem_setOf_eq,
        List.append_eq_nil_iff, Set.mem_union] at hx ⊢
      tauto
  | longSequence n q_b ro Hseq Hind =>
    refine ⟨?_, ?_⟩
    · apply Set.Finite.subset (Set.finite_iUnion (fun j : Fin n => (Hind j.1 j.2).1))
      intro x hx
      simp only [assumptionCounting, long_step_combinator_simple,
        long_step_combinator_simple_half, ne_eq, Set.mem_setOf_eq] at hx
      rw [List.flatten_eq_nil_iff] at hx
      push_neg at hx
      obtain ⟨l, hl, hne⟩ := hx
      rw [List.mem_ofFn] at hl
      obtain ⟨j, hj⟩ := hl
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨j, by rw [hj]; exact hne⟩
    · apply Set.Finite.subset (Set.finite_iUnion (fun j : Fin n => (Hind j.1 j.2).2))
      intro x hx
      simp only [assumptionCounting, long_step_combinator_simple,
        long_step_combinator_simple_half, ne_eq, Set.mem_setOf_eq] at hx
      rw [List.flatten_eq_nil_iff] at hx
      push_neg at hx
      obtain ⟨l, hl, hne⟩ := hx
      rw [List.mem_ofFn] at hl
      obtain ⟨j, hj⟩ := hl
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨j, by rw [hj]; exact hne⟩

abbrev assumptionCountType {Idx : Type} (Assumptions : IndAssumptions Idx)
  {I : Type} (O : OracleSpec I) :=
  {x : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O //
    Set.Finite {i | x.1 i ≠ []} ∧ Set.Finite {i | x.2 i ≠ []} }


noncomputable def assumptionCountingFin {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
  (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
  assumptionCountType Assumptions O :=
  ⟨assumptionCounting ind, assumptionCounting_finite ind⟩

noncomputable def finite_support {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
  (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
  let ret := assumptionCounting ind
  Fintype {x | ret.1 x ≠ []} ×
  Fintype {x | ret.2 x ≠ []} :=
  ((assumptionCounting_finite ind).1.fintype,
   (assumptionCounting_finite ind).2.fintype)

/- # Equivalence of assumptionCounting functions
  The ismorphism is given by `AssumptionsUseTSimple2other`
-/

def AssumptionsUseTSimple2other {Idx : Type} {Assumptions : IndAssumptions Idx}
  {I : Type} {O : OracleSpec I} (count : AssumptionsUseTSimple Assumptions O)
  (H : Fintype {i | count i ≠ []})
  : AssumptionsUseT Assumptions O :=
  {
    subset := ({i | count i ≠ []} : Set Idx).toFinset,
    values a := ⟨count a,
      by
        simp [List.length, List.length_pos_iff]
        grind only [= Set.mem_toFinset, usr Set.mem_setOf_eq]
      ⟩
  }

noncomputable def assumptionCountLower {Idx : Type} {Assumptions : IndAssumptions Idx}
  {I : Type} {O : OracleSpec I}
  (count : assumptionCountType Assumptions O)
  : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O :=
  (AssumptionsUseTSimple2other count.1.1 count.2.1.fintype, AssumptionsUseTSimple2other count.1.2 count.2.2.fintype)

def agreeWithSimp {Idx : Type} {Assumptions : IndAssumptions Idx} {I : Type} {O : OracleSpec I}
  (p : AssumptionsUseT Assumptions O)
  (s : AssumptionsUseTSimple Assumptions O) : Prop :=
  (∀ i, (i ∈ p.subset ↔ (s i ≠ [])) ∧
  (∀ (hi : i ∈ p.subset), (p.values ⟨i, hi⟩).1 = s i))

def agreeWithSimp_lemma {Idx : Type} {Assumptions : IndAssumptions Idx} {I : Type} {O : OracleSpec I}
  (p : AssumptionsUseT Assumptions O)
  (s : AssumptionsUseTSimple Assumptions O)
  (H : agreeWithSimp p s)
  (d : Fintype {x | s x ≠ []}) :
  AssumptionsUseTSimple2other s d = p
   := by
  obtain ⟨ps, pv⟩ := p
  simp only [agreeWithSimp] at H
  have hsub : ({i | s i ≠ []} : Set Idx).toFinset = ps := by
    ext i
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    exact (H i).1.symm
  unfold AssumptionsUseTSimple2other
  subst hsub
  congr 1
  funext a
  apply Subtype.ext
  simp only
  exact ((H a.1).2 a.2).symm


def agreeWithSimpPair {Idx : Type} {Assumptions : IndAssumptions Idx} {I : Type} {O : OracleSpec I}
  (p : AssumptionsUseT Assumptions O × AssumptionsUseT Assumptions O)
  (s : AssumptionsUseTSimple Assumptions O × AssumptionsUseTSimple Assumptions O) : Prop :=
  agreeWithSimp p.1 s.1 ∧ agreeWithSimp p.2 s.2

theorem agree_trans {Idx : Type} {Assumptions : IndAssumptions Idx} {I : Type} {O : OracleSpec I}
  (p1 p2 : AssumptionsUseT Assumptions O)
  (s1 s2 : AssumptionsUseTSimple Assumptions O)
  (H1 : agreeWithSimp p1 s1) (H2 : agreeWithSimp p2 s2) :
  agreeWithSimp (assumptionJoiner p1 p2 (fun a b => listCombiner a b)) (fun x => (s1 x)++(s2 x)) := by
    simp only [agreeWithSimp]
    intro i
    simp only [listCombiner, assumptionJoiner, sumJoiner, agreeWithSimp] at *
    have X : forall {T : Type _} (l1 l2 : List T), l1++l2 ≠ [] ↔ ((l1 ≠ []) ∨ (l2 ≠ [])) := by
      intro T l1 l2
      simp []
      grind
    constructor
    · rw [X (s1 i) (s2 i)]
      rw [<-(H1 i).1]
      rw [<-(H2 i).1]
      simp [finsetSum]
    intro hi
    simp [finsetSum] at hi
    if M1 : i ∈ p1.subset then
      if M2 : i ∈ p2.subset then
        simp [M1, M2]
        rw [(H1 i).2 M1, (H2 i).2 M2]
      else
        simp [M1, M2]
        rw [(H1 i).2 M1]
        simp [(H2 i).1] at M2
        simp [M2]
    else
      if M2 : i ∈ p2.subset then
        simp [M1, M2]
        rw [(H2 i).2 M2]
        simp [(H1 i).1] at M1
        simp [M1]
      else
        simp [M1, M2] at hi


lemma simpleCorrect_in {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
  (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
  agreeWithSimpPair
    (assumptionCounting_low ind)
    (assumptionCounting ind) := by
  haveI : DecidableEq Idx := Assumptions.decEq
  induction ind
  case assumption a =>
    simp [agreeWithSimpPair, agreeWithSimp, assumptionCounting_low, assumptionCounting]
    simp [AssumptionsUseT.empty]
    intro i Hi
    subst Hi
    simp []
  case obsEqB a b c d f =>
    simp [agreeWithSimpPair, agreeWithSimp, assumptionCounting_low, assumptionCounting]
    simp [noAssumptionUse, AssumptionsUseT.empty]
  case reduction a b Hind =>
    simp [agreeWithSimpPair, agreeWithSimp, assumptionCounting_low, assumptionCounting]
    constructor
    · intro i
      constructor
      · apply (Hind.1 i).1
      intro Hi
      rw [(Hind.1 i).2]
    · intro i
      constructor
      · apply (Hind.2 i).1
      intro Hi
      rw [(Hind.2 i).2]
  case symm HInd =>
    simp [agreeWithSimpPair, assumptionCounting_low, assumptionCounting]
    constructor <;> simp [HInd.1, HInd.2]
  case trans a b c d e f Hind1 Hind2 =>
    simp [agreeWithSimpPair, assumptionCounting_low, assumptionCounting]
    generalize assumptionCounting e = e2 at *
    generalize assumptionCounting_low e = e1 at *
    generalize assumptionCounting f = f2 at *
    generalize assumptionCounting_low f = f1 at *
    simp [transitive_step_val, transitive_step_val_simple]
    constructor
    · apply agree_trans
      · apply Hind1.1
      apply Hind2.1
    · apply agree_trans
      · apply Hind1.2
      apply Hind2.2
  case longSequence n q_b c d Hind =>
    induction n
    · simp [agreeWithSimpPair, assumptionCounting_low, assumptionCounting, agreeWithSimp]
      simp [long_step_combinator, long_step_combinator_simple, long_step_combinator_simple_half
        ]
      constructor
      · intro i
        simp [noAssumptionUse, AssumptionsUseT.empty]
      · intro i
        simp [noAssumptionUse, AssumptionsUseT.empty]
    case succ n Hn =>
      simp [agreeWithSimpPair, assumptionCounting_low, assumptionCounting]
      simp [long_step_combinator, long_step_combinator_simple, long_step_combinator_simple_half
        ]
      simp [transitive_step_val, transitive_step_val_simple, long_step_combinator_simple_half]
      simp [assumptionCounting , assumptionCounting_low] at Hn
      constructor
      · rw [long_step_combinator_simple_half_next]
        apply agree_trans
        · have X := Hn (fun j => c ⟨j, by
            simp []
            cases j
            case mk a b =>
              simp [] at b
              simp [b]
              exact Nat.le_add_right_of_le b
            ⟩) (fun j Hj => d j
              (Nat.lt_add_one_of_lt Hj
              )) (fun j Hj => Hind j (Nat.lt_add_one_of_lt Hj))
          have Y := X.1
          simp at Y
          apply Y
        apply (Hind n _).1
      · rw [long_step_combinator_simple_half_next]
        apply agree_trans
        · have X := Hn (fun j => c ⟨j, by
            simp []
            cases j
            case mk a b =>
              simp [] at b
              simp [b]
              exact Nat.le_add_right_of_le b
            ⟩) (fun j Hj => d j
              (Nat.lt_add_one_of_lt Hj
              )) (fun j Hj => Hind j (Nat.lt_add_one_of_lt Hj))
          have Y := X.2
          simp at Y
          apply Y
        apply (Hind n _).2

lemma simpleCorrect {Idx : Type} {Assumptions : IndAssumptions Idx}
  {q_b : ENat}
  {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O}
  (ind : IndistinguishableI Assumptions q_b o₁ o₂) :
  assumptionCountLower (assumptionCountingFin ind) =
    assumptionCounting_low ind :=
by
  simp [assumptionCountLower]
  congr
  · apply agreeWithSimp_lemma
    apply (simpleCorrect_in ind).1
  · apply agreeWithSimp_lemma
    apply (simpleCorrect_in ind).2
