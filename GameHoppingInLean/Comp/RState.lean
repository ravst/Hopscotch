import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import GameHoppingInLean.Tactic.Normalization.PMF.Lemmas
import GameHoppingInLean.Tactic.Normalization.RState.Attrs

/- # RState monad
  To define oracle implementations, we use RState monad, that enables random sampling ane keeping state.
  Here we define monad and auxilary functions. -/

-- RState: A monad combining stateful computation with randomness
abbrev RState (σ : Type u) (α : Type u) : Type u := StateT σ PMF α

namespace StateT

@[simp] lemma run_ite {m : Type u → Type v} [Monad m] {σ α : Type u}
    (p : Prop) [Decidable p] (x y : StateT σ m α) (s : σ) :
    StateT.run (if p then x else y) s = if p then StateT.run x s else StateT.run y s := by
  split_ifs <;> rfl

end StateT

namespace RState

noncomputable
def modify (f : σ → σ) : RState σ Unit := do
  let s ← get
  set (f s)

noncomputable
def run {σ α} (sd : PMF σ) (m : RState σ α) : PMF (α × σ) := do
  let s <- sd
  StateT.run m s

noncomputable
def eval {σ α} (s : PMF σ) (m : RState σ α) : PMF α :=
  (RState.run s m).map Prod.fst

noncomputable
def exec {σ α} (s : PMF σ) (m : RState σ α) : PMF σ :=
  (RState.run s m).map Prod.snd

noncomputable
def mapState {α s₁ s₂} [Nonempty s₁] (f : s₁ → s₂) (s : RState s₁ α) : RState s₂ α :=
  fun s₂ =>
    (StateT.run s (Function.invFun f s₂)).map (fun p => (p.1, f p.2))

noncomputable
def mapStateContra {α s₁ s₂} [Nonempty s₁] (f : s₁ → s₂) (s : RState s₂ α) : RState s₁ α :=
  fun s₂ =>
    (StateT.run s (f s₂)).map (fun p => (p.1, Function.invFun f p.2))

noncomputable
def mapStateBij (f : s₁ ≃ s₂) (m : RState s₁ α) : RState s₂ α :=
  fun s₂ =>
    (StateT.run m (f.invFun s₂)).map (fun p => (p.1, f.toFun p.2))

noncomputable
def runOnFst (m : RState s₁ α) : RState (s₁ × s₂) α :=
  fun st => (StateT.run m st.1).map (fun p => (p.1, (p.2, st.2)))

noncomputable
def runOnSnd (m : RState s₂ α) : RState (s₁ × s₂) α :=
  fun st => (StateT.run m st.2).map (fun p => (p.1, (st.1, p.2)))

noncomputable
def coinFlip {σ} : RState σ Bool :=
  StateT.lift (PMF.uniformOfFintype Bool)

end RState
