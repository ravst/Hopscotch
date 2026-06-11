import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.IndistinguishabilityAssumption

/- # Indistinguishability Definition-/

/-- In this file, we define the type called IndistinguisabilityI, which represents a proof
of indistinguishability between two stateful random oracles. It is in Type and not in Prop,
because we might want to inspect it to see how the indistinguishability is established,
e.g. in order to estabilsh a concrete bound on the advantage of an adversary or to
see what kind of reductions were used.

The definition of IndistinguishabilityI is paremetrized by the indistingushabiliy assumptions,
i.e. the set of pairs of oracles that we assume to be indistinguishable.
-/

def mk (I : Type) (O : OracleSpec I) (p : RStateOracle O × RStateOracle O)
  : (I : Type) × (O : OracleSpec I) × (RStateOracle O × RStateOracle O)
  := ⟨I, O, p⟩

/-- Inductively generated indistinguishability relation for a fixed oracle spec.

Indexed by:
* `Assumptions`: assumption pairs, per oracle spec.
* `Reductions`: allowed reductions (simple, randomized-stateless, stateful-randomized,
  complex-initialization),
  per source/target oracle specs.

The relation is homogeneous in `O`, but reduction steps may move to a different spec
by changing the index parameter of the conclusion. -/

def ro_seq_fixed {I : Type} {O : OracleSpec I} (l : ℕ)
    (ro : Finset.range (l+1) -> RStateOracle O) (i : ℕ) (H : i <= l) : RStateOracle O :=
    ro ⟨i, by
      simp [Finset.range];
      exact Nat.eq_or_lt_of_le H
      ⟩


universe u v w

lemma zero_in_range (n : ℕ) : 0 ∈ Finset.range (n+1) :=
by
  apply Finset.mem_range.mpr
  exact Nat.zero_lt_succ n

lemma n_in_range (n : ℕ) : n ∈ Finset.range (n+1) :=
  by simp [Finset.range]

inductive IndistinguishableI
    (Assumptions : IndistinguishabilityAssumptions)
    (κ : ℕ) :
    (q_b : ENat) -> {I : Type} → (O : OracleSpec I) → RStateOracle O → RStateOracle O → Type 1
  | assumption {q_b : ENat} (i : Assumptions.Idx) :
      IndistinguishableI Assumptions κ q_b ((Assumptions.assumptions i).O)
        (Assumptions.assumptions i).i.1 (Assumptions.assumptions i).i.2
  | obsEqB {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : ENat):
      ObsEqBounded ro₁ ro₂ q_b →
      IndistinguishableI Assumptions κ q_b O ro₁ ro₂
  | complexInitReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : OracleReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} (q_b : ENat):
      IndistinguishableI Assumptions κ none O₁ ro₁ ro₂ →
      IndistinguishableI Assumptions κ q_b O₂
        (OracleReduction.apply r ro₁) (OracleReduction.apply r ro₂)
  | symm {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : ENat):
      IndistinguishableI Assumptions κ q_b O ro₁ ro₂ →
      IndistinguishableI Assumptions κ q_b O ro₂ ro₁
  | trans {I : Type} {O : OracleSpec I}  {ro₁ : RStateOracle O} (ro₂: RStateOracle O) {ro₃ : RStateOracle O} (q_b : ENat):
      IndistinguishableI Assumptions κ q_b O ro₁ ro₂ →
      IndistinguishableI Assumptions κ q_b O ro₂ ro₃ →
      IndistinguishableI Assumptions κ q_b O ro₁ ro₃
  | longSequence {I : Type} {O : OracleSpec I} (l : ℕ)
    (q_b : ENat)
    (ro : Finset.range (l+1) -> RStateOracle O):
    (forall i, (Hi: i < l) ->
      IndistinguishableI Assumptions κ q_b O
        (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed l ro (i+1) Hi)
    ) ->
    IndistinguishableI Assumptions κ q_b O (ro ⟨0, zero_in_range _⟩) (ro ⟨l, n_in_range _⟩)

namespace IndistinguishableI

/-- Let `calc` compose fixed-parameter `IndistinguishableI` proofs transitively. -/
instance instTrans
    {Assumptions : IndistinguishabilityAssumptions}
    {κ : ℕ} {q_b : ENat} {I : Type} {O : OracleSpec I} :
    Trans
      (IndistinguishableI Assumptions κ q_b O)
      (IndistinguishableI Assumptions κ q_b O)
      (IndistinguishableI Assumptions κ q_b O) where
  trans h₁ h₂ := IndistinguishableI.trans _ q_b h₁ h₂

/-- Scoped notation for fixed-parameter `IndistinguishableI` `calc` chains. -/
scoped notation:50 x " ≈ᵢ[" Assumptions ", " ", " κ ", " q_b ", " O "] " y =>
  IndistinguishableI Assumptions κ q_b O x y

end IndistinguishableI

def Indistinguishable (Assumptions : IndistinguishabilityAssumptions)
    {I : Type} {O : OracleSpec I} (r1 r2 : RStateOracle O) :=
    forall κ, IndistinguishableI Assumptions κ none O r1 r2

def IndistinguishableQ (Assumptions : IndistinguishabilityAssumptions)
    {I : Type} (O : OracleSpec I) (r1 r2 : RStateOracle O) :=
    forall κ, forall q_b : ℕ , IndistinguishableI Assumptions κ q_b O r1 r2

namespace Indistinguishable

def of_ObsEq
    {Assumptions : IndistinguishabilityAssumptions}
    {κ :  ℕ} {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (H : ObsEq ro₁ ro₂) :
    IndistinguishableI Assumptions κ q_b O ro₁ ro₂ :=
  IndistinguishableI.obsEqB q_b (by
    rw [ObsEq_from_none] at H
    apply ObsEqBounded_monotone
    apply H
    exact sup_eq_left.mp rfl
    )

def transitive
    {Assumptions : IndistinguishabilityAssumptions}
    {κ :  ℕ} {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : RStateOracle O}:
    (IndistinguishableI Assumptions κ q_b O ro₁ ro₂) ->
    (IndistinguishableI Assumptions κ q_b O ro₂ ro₃) ->
    (IndistinguishableI Assumptions κ q_b O ro₁ ro₃) :=
  fun Ha Hb => IndistinguishableI.trans _ q_b Ha Hb

def symmetric
    {Assumptions : IndistinguishabilityAssumptions}
    {κ :  ℕ} {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}:
    (IndistinguishableI Assumptions κ q_b O ro₁ ro₂) ->
    (IndistinguishableI Assumptions κ q_b O ro₂ ro₁) :=
  fun Ha => IndistinguishableI.symm q_b Ha

@[refl]
def reflexive
    {Assumptions : IndistinguishabilityAssumptions}
    {κ :  ℕ} {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro : RStateOracle O}:
    (IndistinguishableI Assumptions κ q_b O ro ro) :=
  by
    apply of_ObsEq
    exact congrFun rfl

def long_step
  {Assumptions : IndistinguishabilityAssumptions}
    {κ :  ℕ} {q_b : ENat}
    {I : Type} {O : OracleSpec I}
    (l : ℕ) (ro : Finset.range (l+1) -> RStateOracle O)
    (ro_start : RStateOracle O) (ro_end :  RStateOracle O )
    (Hstart : IndistinguishableI Assumptions κ q_b O ro_start (ro ⟨0, zero_in_range _⟩))
    (Hend : IndistinguishableI Assumptions κ q_b O ro_end (ro ⟨l, n_in_range _⟩))
    (H_seq : forall i, (Hi: i < l) ->
      IndistinguishableI Assumptions κ q_b O
        (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed l ro (i+1) Hi)
    ) :
    IndistinguishableI Assumptions κ q_b O ro_start ro_end :=
    IndistinguishableI.trans _ q_b (Hstart) (
      IndistinguishableI.trans _ q_b (
        IndistinguishableI.longSequence _ q_b ro H_seq
      ) (symmetric Hend)
    )

noncomputable def indistinguishabilityI_mono {Assumptions : IndistinguishabilityAssumptions}
    {κ :  ℕ} {q₁ q₂ : ENat} {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (hle : q₁ ≤ q₂) :
    IndistinguishableI Assumptions κ q₂ O ro₁ ro₂ →
    IndistinguishableI Assumptions κ q₁ O ro₁ ro₂ := by
  intro h
  induction h with
  | assumption i =>
      exact IndistinguishableI.assumption i
  | obsEqB q H =>
      exact IndistinguishableI.obsEqB q₁
        (ObsEqBounded_monotone _ _ q₁ q H hle)
  | complexInitReduction r q h =>
      exact IndistinguishableI.complexInitReduction r q₁ h
  | symm q h ih =>
      exact IndistinguishableI.symm q₁ (ih hle)
  | trans a q h₁ h₂ ih₁ ih₂ =>
      exact IndistinguishableI.trans a q₁ (ih₁ hle) (ih₂ hle)
  | longSequence l q ro Hstep ihStep =>
      exact IndistinguishableI.longSequence l q₁ ro
        (fun i Hi => ihStep i Hi hle)

noncomputable def indistinguishabilityIUnboundedToBounded {Assumptions : IndistinguishabilityAssumptions}

    {κ :  ℕ} {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (q_b : ℕ):
    (IndistinguishableI Assumptions κ none O ro₁ ro₂) ->
    (IndistinguishableI Assumptions κ (some q_b) O ro₁ ro₂) :=
  indistinguishabilityI_mono (sup_eq_left.mp rfl)

end Indistinguishable

namespace IndistinguishableI

noncomputable instance instTransLeftUnbounded
    {Assumptions : IndistinguishabilityAssumptions}

    {κ : ℕ} {q_b : ENat} {I : Type} {O : OracleSpec I} :
    Trans
      (IndistinguishableI Assumptions κ none O)
      (IndistinguishableI Assumptions κ q_b O)
      (IndistinguishableI Assumptions κ q_b O) where
  trans h₁ h₂ :=
    IndistinguishableI.trans _ q_b
      (Indistinguishable.indistinguishabilityI_mono (sup_eq_left.mp rfl) h₁)
      h₂

noncomputable instance instTransRightUnbounded
    {Assumptions : IndistinguishabilityAssumptions}

    {κ : ℕ} {q_b : ENat} {I : Type} {O : OracleSpec I} :
    Trans
      (IndistinguishableI Assumptions κ q_b O)
      (IndistinguishableI Assumptions κ none O)
      (IndistinguishableI Assumptions κ q_b O) where
  trans h₁ h₂ :=
    IndistinguishableI.trans _ q_b h₁
      (Indistinguishable.indistinguishabilityI_mono (sup_eq_left.mp rfl) h₂)

end IndistinguishableI


def singleton (a : X) : X -> ℕ :=
   fun i =>
    if i = a then 1 else 0

def AssumptionCounting (A : IndistinguishabilityAssumptions):= A.Idx -> ℕ

def funAdd (f g : AssumptionCounting A ) : AssumptionCounting A := fun x => f x + g x


mutual
  -- def funAddLongSeq {Assumptions : IndistinguishabilityAssumptions}
  --
  --     {κ :  ℕ} {I : Type} {O : OracleSpec I} (l : ℕ) (ro : Finset.range (1+l) -> RStateOracle O)
  --     (q_b : ENat)
  --     (Hs : forall i, (Hi: i < l) ->
  --       IndistinguishableI Assumptions κ q_b O
  --         (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
  --         (ro_seq_fixed l ro (i+1) Hi)
  --     ) : AssumptionCounting :=
  --       (fun i =>
  --       Finset.sum (α := Finset.range (l)) (Finset.univ) (fun j => assumptionsUse (Hs j.1 (by
  --         cases j
  --         case mk val prop =>
  --         simp []
  --         simp [Finset.range] at prop
  --         assumption
  --       )) i))
  def assumptionsUse
      {Assumptions : IndistinguishabilityAssumptions}

      {κ :  ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
      (ind : IndistinguishableI Assumptions κ q_b O ro₁ ro₂) : AssumptionCounting Assumptions :=
      match ind with
      | IndistinguishableI.assumption index =>
        fun j =>
          if j = index then 1 else 0
      | IndistinguishableI.obsEqB q_b H => fun _ => 0
      | IndistinguishableI.complexInitReduction r q_b Hind => assumptionsUse Hind
      | IndistinguishableI.symm q_b H => assumptionsUse H
      | IndistinguishableI.trans a q_b H1 H2 => funAdd (assumptionsUse H1) (assumptionsUse H2)
      | IndistinguishableI.longSequence l q_b ro H =>
          fun i =>
            Finset.sum (ι := Finset.range (l)) (Finset.univ) (fun j => assumptionsUse (H j.1 (by
              cases j
              case mk val prop =>
              simp [Finset.range] at prop
              assumption
            )) i)
end
