import Hopscotch.Comp.StatefulRandomOracle
import Hopscotch.Comp.OracleReductions
import Hopscotch.ObservationalEq.Defs
import Hopscotch.ApproxEq.Defs
import Hopscotch.Indistinguishability.Assumption

/- # Indistinguishability Definition-/

/- In this file, we define the type called IndistinguishableI, which represents a proof
of indistinguishability between two stateful random oracles. It is in Type and not in Prop,
because we might want to inspect it to see how the indistinguishability is established,
e.g. in order to establish a concrete bound on the advantage of an adversary or to
see what kind of reductions were used.

The definition of IndistinguishableI is parametrized by the indistinguishability assumptions,
i.e. the set of pairs of oracles that we assume to be indistinguishable.
-/

/-- getter: given sequence of OracleImpl's `ro`, we get `i`-element -/
def ro_seq_fixed {I : Type} {O : OracleSpec I} (l : ℕ)
    (ro : Finset.range (l + 1) -> OracleImpl O)
    (i : ℕ) (H : i <= l) : OracleImpl O :=
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

/-- Inductively generated indistinguishability relation between O₁ and O₁.
Parameter `q_b` count maximal number of queries made by adversary, under which indistinguishability holds. -/
inductive IndistinguishableI
    {Idx : Type}
    (Assumptions : IndAssumptions Idx) :
    (q_b : ENat) -> {I : Type} → {O : OracleSpec I} → OracleImpl O → OracleImpl O → Type 1
  | assumption {q_b : ENat} (i : Idx) :
      IndistinguishableI Assumptions q_b
        (Assumptions.assumptions i).i.1 (Assumptions.assumptions i).i.2
  | obsEqB {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O} (q_b : ENat):
      ObsEqBounded ro₁ ro₂ q_b →
      IndistinguishableI Assumptions q_b ro₁ ro₂
  | approxEq {q_b : ENat} {I : Type} {O : OracleSpec I}
      {ro₁ ro₂ : OracleImpl O} (ε : NNReal)
      (sound : ApproxEq q_b ε ro₁ ro₂) :
      IndistinguishableI Assumptions q_b ro₁ ro₂
  | reduction {I₁ I₂ : Type} {O₁ : OracleSpec I₁} {O₂ : OracleSpec I₂}
      (r : OracleReduction O₁ O₂) {ro₁ ro₂ : OracleImpl O₁} (q_b : ENat):
      IndistinguishableI Assumptions none ro₁ ro₂ →
      IndistinguishableI Assumptions q_b
        (OracleReduction.apply r ro₁) (OracleReduction.apply r ro₂)
  | symm {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O} (q_b : ENat):
      IndistinguishableI Assumptions q_b ro₁ ro₂ →
      IndistinguishableI Assumptions q_b ro₂ ro₁
  | trans {I : Type} {O : OracleSpec I}  {ro₁ : OracleImpl O} (ro₂: OracleImpl O) {ro₃ : OracleImpl O} (q_b : ENat):
      IndistinguishableI Assumptions q_b ro₁ ro₂ →
      IndistinguishableI Assumptions q_b ro₂ ro₃ →
      IndistinguishableI Assumptions q_b ro₁ ro₃
  | longSequence {I : Type} {O : OracleSpec I} (l : ℕ)
    (q_b : ENat)
    (ro : Finset.range (l+1) -> OracleImpl O):
    (forall i, (Hi: i < l) ->
      IndistinguishableI Assumptions q_b
        (ro_seq_fixed l ro i (Nat.le_of_succ_le Hi))
        (ro_seq_fixed l ro (i+1) Hi)
    ) ->
    IndistinguishableI Assumptions q_b (ro ⟨0, zero_in_range _⟩) (ro ⟨l, n_in_range _⟩)

namespace IndistinguishableI

/-- The total statistical error introduced by the approximate-equivalence steps in an
indistinguishability derivation. -/
noncomputable def statisticalError
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat} {I : Type} {O : OracleSpec I} {o₁ o₂ : OracleImpl O} :
    IndistinguishableI Assumptions q_b o₁ o₂ → NNReal
  | .assumption _ => 0
  | .obsEqB _ _ => 0
  | .approxEq ε _ => ε
  | .reduction _ _ h => statisticalError h
  | .symm _ h => statisticalError h
  | .trans _ _ h₁ h₂ => statisticalError h₁ + statisticalError h₂
  | .longSequence l _ _ h =>
      ∑ i : Fin l, statisticalError (h i i.isLt)

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
    (O1 O2 : (κ : ℕ) → OracleImpl (O κ)) : Type 1 :=
  (κ : ℕ) → IndistinguishableI (AFam.val κ) none (O1 κ) (O2 κ)

def IndistinguishableWithQueryBound
    {I : ℕ → Type} {O : (κ : ℕ) → OracleSpec (I κ)}
    (AFam : IndAssumptionsFam)
    (O1 O2 : (κ : ℕ) → OracleImpl (O κ)) : Type 1 :=
  (b : ℕ) → (κ : ℕ) → IndistinguishableI (AFam.val κ) b (O1 κ) (O2 κ)

def IndistinguishableSingle {Idx : Type} (Assumptions : IndAssumptions Idx)
    {I : Type} {O : OracleSpec I} (r1 r2 : OracleImpl O) :=
    IndistinguishableI Assumptions none r1 r2

def IndistinguishableQ {Idx : Type} (Assumptions : IndAssumptions Idx)
    {I : Type} (O : OracleSpec I) (r1 r2 : OracleImpl O) :=
    forall q_b : ℕ , IndistinguishableI Assumptions q_b r1 r2

namespace Indistinguishable

def of_ObsEq
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O}
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
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ ro₃ : OracleImpl O} :
    (IndistinguishableI Assumptions q_b ro₁ ro₂) ->
    (IndistinguishableI Assumptions q_b ro₂ ro₃) ->
    (IndistinguishableI Assumptions q_b ro₁ ro₃) :=
  fun Ha Hb => IndistinguishableI.trans _ q_b Ha Hb

def symmetric
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O} :
    (IndistinguishableI Assumptions q_b ro₁ ro₂) ->
    (IndistinguishableI Assumptions q_b ro₂ ro₁) :=
  fun Ha => IndistinguishableI.symm q_b Ha

@[refl]
def reflexive
    {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I} {ro : OracleImpl O} :
    (IndistinguishableI Assumptions q_b ro ro) :=
  by
    apply of_ObsEq
    exact congrFun rfl

def long_step
  {Idx : Type} {Assumptions : IndAssumptions Idx}
    {q_b : ENat}
    {I : Type} {O : OracleSpec I}
    (l : ℕ) (ro : Finset.range (l + 1) -> OracleImpl O)
    (ro_start : OracleImpl O) (ro_end :  OracleImpl O )
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
    {q₁ q₂ : ENat} {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O}
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
  | approxEq ε H =>
      exact IndistinguishableI.approxEq ε (fun d hd => H d (hd.trans hle))
  | reduction r q h =>
      exact IndistinguishableI.reduction r q₁ h
  | symm q h ih =>
      exact IndistinguishableI.symm q₁ (ih hle)
  | trans a q h₁ h₂ ih₁ ih₂ =>
      exact IndistinguishableI.trans a q₁ (ih₁ hle) (ih₂ hle)
  | longSequence l q ro Hstep ihStep =>
      exact IndistinguishableI.longSequence l q₁ ro
        (fun i Hi => ihStep i Hi hle)

noncomputable def indistinguishabilityIUnboundedToBounded {Idx : Type} {Assumptions : IndAssumptions Idx}
    {I : Type} {O : OracleSpec I} {ro₁ ro₂ : OracleImpl O}
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
