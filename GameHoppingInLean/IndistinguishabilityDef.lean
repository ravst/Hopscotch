import GameHoppingInLean.Comp.StatefulRandomOracle
import GameHoppingInLean.Comp.OracleReductions
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.IndistinguishabilityAssumption

/- # Indistinguishability Definition-/

/- In this file, we define the type called IndistinguisabilityI, which represents a proof
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

/- Inductively generated indistinguishability relation for a fixed oracle spec.

Indexed by:
* `Assumptions`: assumption pairs, per oracle spec.
* `Reductions`: allowed reductions (simple, randomized-stateless, stateful-randomized,
  complex-initialization),
  per source/target oracle specs.

The relation is homogeneous in `O`, but reduction steps may move to a different spec
by changing the index parameter of the conclusion. -/

def ro_seq_fixed {I : Type} {O : OracleSpec I} (l : ℕ)
    (ro : Finset.range (l + 1) -> RStateOracle O) (i : ℕ) (H : i <= l) : RStateOracle O :=
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
    {Idx : Type}
    (Assumptions : IndAssumptions Idx) :
    (q_b : ENat) -> {I : Type} → {O : OracleSpec I} → RStateOracle O → RStateOracle O → Type 1
  | assumption {q_b : ENat} (i : Idx) :
      IndistinguishableI Assumptions q_b
        (Assumptions.assumptions i).i.1 (Assumptions.assumptions i).i.2
  | obsEqB {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : ENat):
      ObsEqBounded ro₁ ro₂ q_b →
      IndistinguishableI Assumptions q_b ro₁ ro₂
  | complexInitReduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : OracleReduction O₁ O₂) {ro₁ ro₂ : RStateOracle O₁} (q_b : ENat):
      IndistinguishableI Assumptions none ro₁ ro₂ →
      IndistinguishableI Assumptions q_b
        (OracleReduction.apply r ro₁) (OracleReduction.apply r ro₂)
  | symm {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} (q_b : ENat):
      IndistinguishableI Assumptions q_b ro₁ ro₂ →
      IndistinguishableI Assumptions q_b ro₂ ro₁
  | trans {I : Type} {O : OracleSpec I}  {ro₁ : RStateOracle O} (ro₂: RStateOracle O) {ro₃ : RStateOracle O} (q_b : ENat):
      IndistinguishableI Assumptions q_b ro₁ ro₂ →
      IndistinguishableI Assumptions q_b ro₂ ro₃ →
      IndistinguishableI Assumptions q_b ro₁ ro₃
  | longSequence {I : Type} {O : OracleSpec I} (l : ℕ)
    (q_b : ENat)
    (ro : Finset.range (l+1) -> RStateOracle O):
    (forall i, (Hi: i < l) ->
      IndistinguishableI Assumptions q_b
        (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed l ro (i+1) Hi)
    ) ->
    IndistinguishableI Assumptions q_b (ro ⟨0, zero_in_range _⟩) (ro ⟨l, n_in_range _⟩)

namespace IndistinguishableI

/-- Let `calc` compose fixed-parameter `IndistinguishableI` proofs transitively. -/
instance instTrans
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat} {I : Type} {O : OracleSpec I} :
    Trans
      (IndistinguishableI Assumptions q_b (I := I) (O := O))
      (IndistinguishableI Assumptions q_b (I := I) (O := O))
      (IndistinguishableI Assumptions q_b (I := I) (O := O)) where
  trans h₁ h₂ := IndistinguishableI.trans _ q_b h₁ h₂

/-- Scoped notation for fixed-parameter `IndistinguishableI` `calc` chains. -/
scoped notation:50 x " ≈ᵢ[" Assumptions ", " q_b "] " y =>
  IndistinguishableI Assumptions q_b x y

end IndistinguishableI

def Indistinguishable
    {I : ℕ → Type} {O : (κ : ℕ) → OracleSpec (I κ)}
    (AFam : IndAssumptionsFam)
    (O1 O2 : (κ : ℕ) → RStateOracle (O κ)) : Type 1 :=
  (κ : ℕ) → IndistinguishableI (AFam.val κ) none (O1 κ) (O2 κ)

def IndistinguishableWithQueryBound
    {I : ℕ → Type} {O : (κ : ℕ) → OracleSpec (I κ)}
    (AFam : IndAssumptionsFam)
    (O1 O2 : (κ : ℕ) → RStateOracle (O κ)) : Type 1 :=
  (b : ℕ) → (κ : ℕ) → IndistinguishableI (AFam.val κ) b (O1 κ) (O2 κ)

def IndistinguishableSingle {Idx : Type} (Assumptions : IndAssumptions Idx)
    {I : Type} {O : OracleSpec I} (r1 r2 : RStateOracle O) :=
    IndistinguishableI Assumptions none r1 r2

def IndistinguishableQ {Idx : Type} (Assumptions : IndAssumptions Idx)
    {I : Type} (O : OracleSpec I) (r1 r2 : RStateOracle O) :=
    forall q_b : ℕ , IndistinguishableI Assumptions q_b r1 r2

namespace Indistinguishable

def of_ObsEq
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (H : ObsEq ro₁ ro₂) :
    IndistinguishableI Assumptions q_b ro₁ ro₂ :=
  IndistinguishableI.obsEqB q_b (by
    rw [ObsEq_from_none] at H
    apply ObsEqBounded_monotone
    · apply H
    exact sup_eq_left.mp rfl
    )

def transitive
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : RStateOracle O} :
    (IndistinguishableI Assumptions q_b ro₁ ro₂) ->
    (IndistinguishableI Assumptions q_b ro₂ ro₃) ->
    (IndistinguishableI Assumptions q_b ro₁ ro₃) :=
  fun Ha Hb => IndistinguishableI.trans _ q_b Ha Hb

def symmetric
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
    (IndistinguishableI Assumptions q_b ro₁ ro₂) ->
    (IndistinguishableI Assumptions q_b ro₂ ro₁) :=
  fun Ha => IndistinguishableI.symm q_b Ha

@[refl]
def reflexive
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro : RStateOracle O} :
    (IndistinguishableI Assumptions q_b ro ro) :=
  by
    apply of_ObsEq
    exact congrFun rfl

def long_step
  {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I}
    (l : ℕ) (ro : Finset.range (l + 1) -> RStateOracle O)
    (ro_start : RStateOracle O) (ro_end :  RStateOracle O )
    (Hstart : IndistinguishableI Assumptions q_b ro_start (ro ⟨0, zero_in_range _⟩))
    (Hend : IndistinguishableI Assumptions q_b ro_end (ro ⟨l, n_in_range _⟩))
    (H_seq : forall i, (Hi: i < l) ->
      IndistinguishableI Assumptions q_b
        (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed l ro (i+1) Hi)
    ) :
    IndistinguishableI Assumptions q_b ro_start ro_end :=
    IndistinguishableI.trans _ q_b (Hstart) (
      IndistinguishableI.trans _ q_b (
        IndistinguishableI.longSequence _ q_b ro H_seq
      ) (symmetric Hend)
    )

noncomputable def indistinguishabilityI_mono {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q₁ q₂ : ENat} {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (hle : q₁ ≤ q₂) :
    IndistinguishableI Assumptions q₂ ro₁ ro₂ →
    IndistinguishableI Assumptions q₁ ro₁ ro₂ := by
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

noncomputable def indistinguishabilityIUnboundedToBounded {Idx : Type} {Assumptions : IndAssumptions Idx}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
    (q_b : ℕ) :
    (IndistinguishableI Assumptions none ro₁ ro₂) ->
    (IndistinguishableI Assumptions (some q_b) ro₁ ro₂) :=
  indistinguishabilityI_mono (sup_eq_left.mp rfl)

end Indistinguishable

namespace IndistinguishableI

noncomputable instance instTransLeftUnbounded
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat} {I : Type} {O : OracleSpec I} :
    Trans
      (IndistinguishableI Assumptions none (I := I) (O := O))
      (IndistinguishableI Assumptions q_b (I := I) (O := O))
      (IndistinguishableI Assumptions q_b (I := I) (O := O)) where
  trans h₁ h₂ :=
    IndistinguishableI.trans _ q_b
      (Indistinguishable.indistinguishabilityI_mono (sup_eq_left.mp rfl) h₁)
      h₂

noncomputable instance instTransRightUnbounded
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat} {I : Type} {O : OracleSpec I} :
    Trans
      (IndistinguishableI Assumptions q_b (I := I) (O := O))
      (IndistinguishableI Assumptions none (I := I) (O := O))
      (IndistinguishableI Assumptions q_b (I := I) (O := O)) where
  trans h₁ h₂ :=
    IndistinguishableI.trans _ q_b h₁
      (Indistinguishable.indistinguishabilityI_mono (sup_eq_left.mp rfl) h₂)

end IndistinguishableI
