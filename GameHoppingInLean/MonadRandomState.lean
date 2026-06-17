import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import GameHoppingInLean.Misc.RStateSimplifierAttr
-- import VCVio.ToMathlib.Control.MonadHom

/-!
# definition of moand for statefull copmutation with randomness
-/


def MyBetterStateT (σ : Type z) (m : Type (max z u) → Type v) (α : Type u) : Type (max v z) :=
  σ → m (α × σ)
-- RState: state transformer over the probabilistic Pmf monad
abbrev MyBetterRState (σ : Type u) (α : Type v) : Type (max u v) := MyBetterStateT σ PMF α


-- RState: state transformer over the probabilistic Pmf monad
abbrev RState (σ : Type u) (α : Type u) : Type u := StateT σ PMF α

namespace StateT

@[simp] lemma run_ite {m : Type u → Type v} [Monad m] {σ α : Type u}
    (p : Prop) [Decidable p] (x y : StateT σ m α) (s : σ) :
    StateT.run (if p then x else y) s = if p then StateT.run x s else StateT.run y s := by
  split_ifs <;> rfl

end StateT

namespace PMF


@[simp] lemma map_pure_eq_pure {α β : Type} (f : α → β) (a : α) :
    PMF.map f (PMF.pure a) = PMF.pure (f a) := by
  simpa using (PMF.pure_map (f := f) a)


@[simp] lemma map_pure_eq_pure2 {α β : Type} (f : α → β) (a : α) :
    PMF.map f (pure a) = PMF.pure (f a) := by
  simp [(PMF.pure_map (f := f) a)]


@[simp] lemma monad_map_pure_eq_pure {α β : Type} (f : α → β) (a : α) :
    f <$> (PMF.pure a) = PMF.pure (f a) := by
  simp [PMF.monad_map_eq_map]

--  lemma monad_map_into_map {α β : Type} (f : α → β) (a : PMF α) :
--     f <$> (a) = PMF.map f a :=
--   by
--     exact monad_map_eq_map f a

/-- Rewriting a uniform draw over a product type as two independent uniform draws. -/
@[simp] lemma uniformOfFintype_prod_bind
    {A B α : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (f : A × B → PMF α) :
    (PMF.uniformOfFintype (A × B)).bind f =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).bind (fun b => f (a, b))) := by
  ext x
  have hprod :
      (∑' i : A × B, (f i) x) = ∑' i : A, ∑' j : B, (f (i, j)) x := by
    simpa using (ENNReal.tsum_prod' (f := fun p : A × B => (f p) x))
  simp [PMF.bind_apply, Fintype.card_prod, ENNReal.mul_inv, ENNReal.tsum_mul_left,
    mul_assoc, mul_left_comm, mul_comm, hprod]
  simp [<-Finset.mul_sum]
  rw [Fintype.sum_prod_type fun x_1 ↦ (f x_1) x]

end PMF

namespace RState

@[simp] lemma run_get {σ} (s : σ) :
    StateT.run (get : RState σ σ) s = PMF.pure (s, s) := rfl

@[simp, RStateSimplifier] lemma get_apply {σ} (s : σ) :
    (get : RState σ σ) s = PMF.pure (s, s) := rfl

@[simp] lemma run_map_get {σ α} (f : σ → α) (s : σ) :
    StateT.run (f <$> (get : RState σ σ)) s = PMF.pure (f s, s) := by
  change StateT.run (StateT.map f (get : RState σ σ)) s = PMF.pure (f s, s)
  unfold StateT.map
  change PMF.map (fun a : σ × σ => (f a.1, a.2)) (PMF.pure ((s, s) : σ × σ)) =
    PMF.pure (f s, s)
  exact PMF.pure_map (fun a : σ × σ => (f a.1, a.2)) ((s, s) : σ × σ)

@[simp, RStateSimplifier] lemma map_get_apply {σ α} (f : σ → α) (s : σ) :
    (f <$> (get : RState σ σ)) s = PMF.pure (f s, s) := by
  exact run_map_get f s

@[simp] lemma run_liftM {σ α} (x : PMF α) (s : σ) :
    StateT.run (liftM x : RState σ α) s = x.map (fun a => (a, s)) := by
  simp [liftM, MonadLift.monadLift, monadLift, StateT.lift, PMF.monad_map_eq_map]

@[simp, RStateSimplifier] lemma liftM_apply {σ α} (x : PMF α) (s : σ) :
    (liftM x : RState σ α) s = x.map (fun a => (a, s)) := by
  exact run_liftM x s

@[simp] lemma run_pure_apply {σ α} (x : α) (s : σ) :
    StateT.run (pure x : RState σ α) s = PMF.pure (x, s) := rfl

@[simp, RStateSimplifier] lemma pure_apply {σ α} (x : α) (s : σ) :
    (pure x : RState σ α) s = PMF.pure (x, s) := rfl

noncomputable
def modify (f : σ → σ) : RState σ Unit := do
  let s ← get
  set (f s)

@[simp] lemma run_modify {σ} (f : σ → σ) (s : σ) :
    StateT.run (modify f : RState σ Unit) s = PMF.pure ((), f s) := by
  simp only [modify, StateT.run_bind]
  simp []
  rfl

@[simp, RStateSimplifier] lemma modify_apply {σ} (f : σ → σ) (s : σ) :
    (modify f : RState σ Unit) s = PMF.pure ((), f s) := by
  change StateT.run (modify f : RState σ Unit) s = PMF.pure ((), f s)
  exact run_modify f s

@[simp] lemma run_monadState_modify {σ} (f : σ → σ) (s : σ) :
    StateT.run (_root_.modify f : RState σ Unit) s = PMF.pure ((), f s) := rfl

@[simp, RStateSimplifier] lemma monadState_modify_apply {σ} (f : σ → σ) (s : σ) :
    (_root_.modify f : RState σ Unit) s = PMF.pure ((), f s) := rfl

@[simp, RStateSimplifier] lemma modify_snd_apply {α β} (f : β → β) (x : α) (y : β) :
    (modify (fun p : α × β => (p.1, f p.2)) : RState (α × β) Unit) (x, y) =
      PMF.pure ((), (x, f y)) := by
  exact modify_apply (fun p : α × β => (p.1, f p.2)) (x, y)

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

lemma map_eq_do {σ α β} (f : α → β) (x : RState σ α) :
    (f <$> x : RState σ β) =
      (do
        let a ← x
        pure (f a)) := by
  rfl

@[simp] lemma ite_pure {σ α} (p : Prop) [Decidable p] (a b : α) :
    (if p then (pure a : RState σ α) else pure b) =
      (pure (if p then a else b) : RState σ α) := by
  split_ifs <;> rfl

@[RStateSimplifier] lemma ite_apply_fn {α β}
    (p : Prop) [Decidable p] (f : α → β) (a b : α) :
    (if p then f a else f b) = f (if p then a else b) := by
  split_ifs <;> rfl

@[simp] lemma ite_some {α}
    (p : Prop) [Decidable p] (a b : α) :
    (if p then (some a : Option α) else some b) = some (if p then a else b) := by
  apply ite_apply_fn

@[simp] lemma ite_get_get {σ α}
    (p : Prop) [Decidable p]
    (x y : σ → RState σ α) :
    (if p then
      (do
        let s ← (get : RState σ σ)
        x s)
    else
      (do
        let s ← (get : RState σ σ)
        y s)) =
    (do
      let s ← (get : RState σ σ)
      if p then x s else y s) := by
  split_ifs <;> rfl

@[simp] lemma do_get_ignore {σ α} (x : RState σ α) :
    (do
      let _ ← (get : RState σ σ)
      x) = x := by
  funext s
  change (PMF.pure (s, s)).bind (fun p : σ × σ => x p.2) = x s
  apply PMF.pure_bind

@[simp] lemma ite_get_left {σ α}
    (p : Prop) [Decidable p]
    (x : σ → RState σ α) (y : RState σ α) :
    (if p then
      (do
        let s ← (get : RState σ σ)
        x s)
    else y) =
    (do
      let s ← (get : RState σ σ)
      if p then x s else y) := by
  split_ifs <;> simp

@[simp] lemma ite_get_right {σ α}
    (p : Prop) [Decidable p]
    (x : RState σ α) (y : σ → RState σ α) :
    (if p then x
    else
      (do
        let s ← (get : RState σ σ)
        y s)) =
    (do
      let s ← (get : RState σ σ)
      if p then x else y s) := by
  split_ifs <;> simp


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

@[simp] lemma run_runOnFst {s₁ s₂ α}
    (m : RState s₁ α) (st : s₁ × s₂) :
    StateT.run (runOnFst (s₂ := s₂) m) st =
      (StateT.run m st.1).map (fun p => (p.1, (p.2, st.2))) := rfl

@[simp] lemma run_runOnSnd {s₁ s₂ α}
    (m : RState s₂ α) (st : s₁ × s₂) :
    StateT.run (runOnSnd (s₁ := s₁) m) st =
      (StateT.run m st.2).map (fun p => (p.1, (st.1, p.2))) := rfl

@[simp, RStateSimplifier] lemma runOnFst_pure {α s₁ s₂}
    (a : α) :
    runOnFst (s₂ := s₂) (pure a : RState s₁ α) =
      (pure a : RState (s₁ × s₂) α) := by
  funext st
  change
    PMF.map (fun p : α × s₁ => (p.1, (p.2, st.2))) (PMF.pure (a, st.1)) =
      PMF.pure (a, st)
  rw [PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnFst_bind {α β s₁ s₂}
    (x : RState s₁ α) (y : α → RState s₁ β) :
    runOnFst (s₂ := s₂) (x >>= y) =
      (runOnFst (s₂ := s₂) x >>= fun a => runOnFst (s₂ := s₂) (y a)) := by
  funext st
  change StateT.run (runOnFst (s₂ := s₂) (x >>= y)) st =
    StateT.run (runOnFst (s₂ := s₂) x >>= fun a => runOnFst (s₂ := s₂) (y a)) st
  change
    PMF.map (fun p : β × s₁ => (p.1, (p.2, st.2)))
      ((StateT.run x st.1).bind (fun p => StateT.run (y p.1) p.2)) =
    ((StateT.run x st.1).map (fun p : α × s₁ => (p.1, (p.2, st.2)))).bind
      (fun p : α × (s₁ × s₂) => StateT.run (runOnFst (s₂ := s₂) (y p.1)) p.2)
  rw [PMF.map_bind, PMF.bind_map]
  rfl

@[simp, RStateSimplifier] lemma runOnFst_get {s₁ s₂} :
    runOnFst (s₂ := s₂) (get : RState s₁ s₁) =
      (do
        let st ← (get : RState (s₁ × s₂) (s₁ × s₂))
        pure st.1) := by
  rw [← map_eq_do Prod.fst (get : RState (s₁ × s₂) (s₁ × s₂))]
  funext st
  change
    PMF.map (fun p : s₁ × s₁ => (p.1, (p.2, st.2))) (PMF.pure (st.1, st.1)) =
      PMF.map (fun p : (s₁ × s₂) × (s₁ × s₂) => (p.1.1, p.2)) (PMF.pure (st, st))
  rw [PMF.pure_map, PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnFst_set {s₁ s₂}
    (s : s₁) :
    runOnFst (s₂ := s₂) (set s : RState s₁ Unit) =
      modify (fun st : s₁ × s₂ => (s, st.2)) := by
  funext st
  change
    PMF.map (fun p : PUnit × s₁ => (p.1, (p.2, st.2))) (PMF.pure ((), s)) =
      StateT.run (modify (fun st : s₁ × s₂ => (s, st.2))) st
  rw [run_modify, PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnFst_modify {s₁ s₂}
    (f : s₁ → s₁) :
    runOnFst (s₂ := s₂) (modify f) =
      modify (fun st : s₁ × s₂ => (f st.1, st.2)) := by
  funext st
  change
    PMF.map (fun p : PUnit × s₁ => (p.1, (p.2, st.2))) (StateT.run (modify f) st.1) =
      StateT.run (modify (fun st : s₁ × s₂ => (f st.1, st.2))) st
  rw [run_modify, run_modify, PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnSnd_pure {α s₁ s₂}
    (a : α) :
    runOnSnd (s₁ := s₁) (pure a : RState s₂ α) =
      (pure a : RState (s₁ × s₂) α) := by
  funext st
  change
    PMF.map (fun p : α × s₂ => (p.1, (st.1, p.2))) (PMF.pure (a, st.2)) =
      PMF.pure (a, st)
  rw [PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnSnd_bind {α β s₁ s₂}
    (x : RState s₂ α) (y : α → RState s₂ β) :
    runOnSnd (s₁ := s₁) (x >>= y) =
      (runOnSnd (s₁ := s₁) x >>= fun a => runOnSnd (s₁ := s₁) (y a)) := by
  funext st
  change StateT.run (runOnSnd (s₁ := s₁) (x >>= y)) st =
    StateT.run (runOnSnd (s₁ := s₁) x >>= fun a => runOnSnd (s₁ := s₁) (y a)) st
  change
    PMF.map (fun p : β × s₂ => (p.1, (st.1, p.2)))
      ((StateT.run x st.2).bind (fun p => StateT.run (y p.1) p.2)) =
    ((StateT.run x st.2).map (fun p : α × s₂ => (p.1, (st.1, p.2)))).bind
      (fun p : α × (s₁ × s₂) => StateT.run (runOnSnd (s₁ := s₁) (y p.1)) p.2)
  rw [PMF.map_bind, PMF.bind_map]
  rfl

@[simp, RStateSimplifier] lemma runOnSnd_get {s₁ s₂} :
    runOnSnd (s₁ := s₁) (get : RState s₂ s₂) =
      (do
        let st ← (get : RState (s₁ × s₂) (s₁ × s₂))
        pure st.2) := by
  rw [← map_eq_do Prod.snd (get : RState (s₁ × s₂) (s₁ × s₂))]
  funext st
  change
    PMF.map (fun p : s₂ × s₂ => (p.1, (st.1, p.2))) (PMF.pure (st.2, st.2)) =
      PMF.map (fun p : (s₁ × s₂) × (s₁ × s₂) => (p.1.2, p.2)) (PMF.pure (st, st))
  rw [PMF.pure_map, PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnSnd_set {s₁ s₂}
    (s : s₂) :
    runOnSnd (s₁ := s₁) (set s : RState s₂ Unit) =
      modify (fun st : s₁ × s₂ => (st.1, s)) := by
  funext st
  change
    PMF.map (fun p : PUnit × s₂ => (p.1, (st.1, p.2))) (PMF.pure ((), s)) =
      StateT.run (modify (fun st : s₁ × s₂ => (st.1, s))) st
  rw [run_modify, PMF.pure_map]

@[simp, RStateSimplifier] lemma runOnSnd_modify {s₁ s₂}
    (f : s₂ → s₂) :
    runOnSnd (s₁ := s₁) (modify f) =
      modify (fun st : s₁ × s₂ => (st.1, f st.2)) := by
  funext st
  change
    PMF.map (fun p : PUnit × s₂ => (p.1, (st.1, p.2))) (StateT.run (modify f) st.2) =
      StateT.run (modify (fun st : s₁ × s₂ => (st.1, f st.2))) st
  rw [run_modify, run_modify, PMF.pure_map]

@[RStateSimplifier] lemma stateT_run_rstate_modify {f : α → α} :
  (RState.modify f) = fun st => pure ((), f st) := by
    ext1 st
    simp [pure, StateT.run]


@[simp] lemma mapStateBij_pure {α s₁ s₂}
    (f : s₁ ≃ s₂) (a : α) :
    mapStateBij f (pure a : RState s₁ α) = (pure a : RState s₂ α) := by
  funext s
  change PMF.map (fun p : α × s₁ => (p.1, f p.2)) (PMF.pure (a, f.symm s)) = PMF.pure (a, s)
  simp [PMF.pure_map]

@[simp] lemma mapStateBij_bind {α β s₁ s₂}
    (f : s₁ ≃ s₂) (x : RState s₁ α) (y : α → RState s₁ β) :
    mapStateBij f (x >>= y) =
      (mapStateBij f x >>= fun a => mapStateBij f (y a)) := by
  funext s
  change
    PMF.map (fun p : β × s₁ => (p.1, f p.2))
      ((StateT.run x (f.symm s)).bind (fun p => StateT.run (y p.1) p.2)) =
    ((StateT.run x (f.symm s)).map (fun p : α × s₁ => (p.1, f p.2))).bind
      (fun p : α × s₂ =>
        (StateT.run (y p.1) (f.symm p.2)).map (fun q : β × s₁ => (q.1, f q.2)))
  rw [PMF.map_bind]
  rw [PMF.bind_map]
  congr
  funext p
  rcases p with ⟨a, st⟩
  simp

@[simp] lemma mapStateBij_liftM {α s₁ s₂}
    (f : s₁ ≃ s₂) (x : PMF α) :
    mapStateBij f (liftM x : RState s₁ α) = (liftM x : RState s₂ α) := by
  funext s
  change
    PMF.map (fun p : α × s₁ => (p.1, f p.2))
      (StateT.run (StateT.lift x : RState s₁ α) (f.symm s)) =
      StateT.run (StateT.lift x : RState s₂ α) s
  rw [StateT.run_lift, StateT.run_lift]
  change PMF.map (fun p : α × s₁ => (p.1, f p.2)) (PMF.map (fun a : α => (a, f.symm s)) x) =
    PMF.map (fun a : α => (a, s)) x
  rw [PMF.map_comp]
  have hcomp :
      (fun p : α × s₁ => (p.1, f p.2)) ∘ (fun a : α => (a, f.symm s)) =
      (fun a : α => (a, s)) := by
    funext a
    simp [Function.comp, f.right_inv]
  simp [hcomp]

@[simp] lemma mapStateBij_get {s₁ s₂}
    (f : s₁ ≃ s₂) :
    mapStateBij f get =
      (do
        let s ← get
        pure (f.symm s)) := by
  funext s
  change
    PMF.map (fun p : s₁ × s₁ => (p.1, f p.2))
      (StateT.run (StateT.get : StateT s₁ PMF s₁) (f.symm s)) =
    StateT.run (((StateT.get : RState s₂ s₂) >>= fun st => pure (f.symm st)) : RState s₂ s₁) s
  rw [show StateT.run (StateT.get : StateT s₁ PMF s₁) (f.symm s) = PMF.pure (f.symm s, f.symm s) by rfl]
  rw [StateT.run_bind]
  rw [show StateT.run (StateT.get : StateT s₂ PMF s₂) s = PMF.pure (s, s) by rfl]
  simp [StateT.run_pure, PMF.pure_map, PMF.pure_bind]
  change PMF.pure (f.symm s, s) =
    PMF.map (fun a : s₂ × s₂ => (f.symm a.1, a.2)) (PMF.pure (s, s))
  rw [PMF.pure_map]

@[simp] lemma mapStateBij_set {s₁ s₂}
    (f : s₁ ≃ s₂) (s : s₁) :
    mapStateBij f (set s : RState s₁ Unit) =
      (set (f s) : RState s₂ Unit) := by
  funext st
  change
    PMF.map (fun p : Unit × s₁ => (p.1, f p.2))
      (StateT.run (StateT.set s : StateT s₁ PMF Unit) (f.symm st)) =
    StateT.run (StateT.set (f s) : StateT s₂ PMF Unit) st
  rw [show StateT.run (StateT.set s : StateT s₁ PMF Unit) (f.symm st) = PMF.pure ((), s) by rfl]
  rw [show StateT.run (StateT.set (f s) : StateT s₂ PMF Unit) st = PMF.pure ((), f s) by rfl]
  simp [PMF.pure_map]

@[simp] lemma mapStateBij_ite {α s₁ s₂}
    (f : s₁ ≃ s₂) (p : Prop) [Decidable p]
    (e1 e2 : RState s₁ α) :
    mapStateBij f (if p then e1 else e2) =
      (if p then mapStateBij f e1 else mapStateBij f e2) := by
  split_ifs <;> rfl


-- @[simp] lemma mapState_pure {α s₁ s₂} [Nonempty s₁]
--     (f : s₁ → s₂) (hf : Function.Surjective f) (a : α) :
--     mapState f (pure a : RState s₁ α) = (pure a : RState s₂ α) := by
--   funext s₂
--   change
--     PMF.map (fun p : α × s₁ => (p.1, f p.2)) (PMF.pure (a, Function.invFun f s₂)) =
--       PMF.pure (a, s₂)
--   rw [PMF.pure_map]
--   have h : f (Function.invFun f s₂) = s₂ := Function.rightInverse_invFun hf s₂
--   simp [h]

lemma mapStateContra_bind {α β s₁ s₂} [Nonempty s₁]
    (f : s₁ → s₂) (hf : Function.Surjective f)
    (x : RState s₂ α) (y : α → RState s₂ β) :
    mapStateContra f (x >>= y) =
      (mapStateContra f x >>= fun a => mapStateContra f (y a)) := by
        ext1 s
        simp [mapStateContra, bind, StateT.bind, StateT.run, PMF.map_bind]
        congr; ext1 a
        have x := Function.rightInverse_invFun hf
        simp [Function.RightInverse, Function.LeftInverse] at x
        simp [x]


-- @[simp] lemma mapState_bind {α β s₁ s₂} [Nonempty s₁]
--     (f : s₁ → s₂) (hf : Function.Injective f)
--     (x : RState s₁ α) (y : α → RState s₁ β) :
--     mapState f (x >>= y) =
--       (mapState f x >>= fun a => mapState f (y a)) := by
--   funext t
--   change
--     PMF.map (fun p => (p.1, f p.2))
--       (StateT.run (x >>= y) (Function.invFun f t)) =
--       (StateT.run (mapState f x) t).bind
--         (fun p => StateT.run (mapState f (y p.1)) p.2)
--   rw [StateT.run_bind]
--   change
--     PMF.map (fun p => (p.1, f p.2))
--       ((StateT.run x (Function.invFun f t)).bind (fun p => StateT.run (y p.1) p.2)) =
--       (StateT.run (mapState f x) t).bind
--         (fun p => StateT.run (mapState f (y p.1)) p.2)
--   rw [PMF.map_bind]
--   change
--     (StateT.run x (Function.invFun f t)).bind
--       (fun p => PMF.map (fun q => (q.1, f q.2)) (StateT.run (y p.1) p.2)) =
--       ((StateT.run x (Function.invFun f t)).map (fun p => (p.1, f p.2))).bind
--         (fun p => PMF.map (fun q => (q.1, f q.2))
--           (StateT.run (y p.1) (Function.invFun f p.2)))
--   rw [PMF.bind_map]
--   have hfun :
--       (fun p : α × s₁ =>
--         PMF.map (fun q => (q.1, f q.2)) (StateT.run (y p.1) p.2)) =
--       ((fun p : α × s₂ =>
--         PMF.map (fun q => (q.1, f q.2)) (StateT.run (y p.1) (Function.invFun f p.2))) ∘
--           (fun p : α × s₁ => (p.1, f p.2))) := by
--     funext p
--     rcases p with ⟨a, st⟩
--     have hst : Function.invFun f (f st) = st := Function.leftInverse_invFun hf st
--     simp [Function.comp, hst]
--   rw [hfun]

-- noncomputable def mapStateHom {s₁ s₂} [Nonempty s₁]
--     (f : s₁ → s₂) (hf : Function.Bijective f) : (RState s₁) →ᵐ (RState s₂) where
--   toFun := mapState f
--   toFun_pure' := mapState_pure (f := f) hf.surjective
--   toFun_bind' := mapState_bind (f := f) hf.injective

-- instance mapState_isMonadHom {s₁ s₂} [Nonempty s₁]
--     (f : s₁ → s₂) (hf : Function.Bijective f) :
--     IsMonadHom (RState s₁) (RState s₂) (mapState f) where
--   map_pure := mapState_pure (f := f) hf.surjective
--   map_bind := mapState_bind (f := f) hf.injective


@[simp] lemma run_pure {σ α} (sd : PMF σ) (a : α) :
    RState.run sd (pure a : RState σ α) = sd.map (fun s => (a, s)) := by
  simpa [PMF.monad_map_eq_map] using (by
    simp [RState.run, PMF.bind_pure_comp] : RState.run sd (pure a : RState σ α) = (Prod.mk a <$> sd))

@[simp] lemma eval_pure {σ α} (sd : PMF σ) (a : α) :
    RState.eval sd (pure a : RState σ α) = PMF.pure a := by
  rw [RState.eval, run_pure]
  rw [PMF.map_comp]
  simp [PMF.map_const]

@[simp] lemma exec_pure {σ α} (sd : PMF σ) (a : α) :
    RState.exec sd (pure a : RState σ α) = sd := by
  rw [RState.exec, run_pure]
  rw [PMF.map_comp]
  simpa using (PMF.map_id (p := sd))

@[simp] lemma run_bind {σ α β} (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.run sd (m >>= f) = (RState.run sd m).bind (fun p => StateT.run (f p.1) p.2) := by
  change sd.bind (fun s => (StateT.run m s).bind (fun p => StateT.run (f p.1) p.2)) =
      (sd.bind fun s => StateT.run m s).bind (fun p => StateT.run (f p.1) p.2)
  exact (PMF.bind_bind (p := sd) (f := fun s => StateT.run m s)
    (g := fun p => StateT.run (f p.1) p.2)).symm

@[simp] lemma run_bind2 {σ α β} (sd : σ) (m : RState σ α) (f : α → RState σ β) :
    (m >>= f) sd = (m sd).bind (fun p => StateT.run (f p.1) p.2) := by
  exact rfl

@[simp] lemma eval_bind {σ α β} (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.eval sd (m >>= f) = (RState.run sd m).bind (fun p => (StateT.run (f p.1) p.2).map Prod.fst) := by
  rw [RState.eval, run_bind, PMF.map_bind]

@[simp] lemma exec_bind {σ α β} (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.exec sd (m >>= f) = (RState.run sd m).bind (fun p => (StateT.run (f p.1) p.2).map Prod.snd) := by
  rw [RState.exec, run_bind, PMF.map_bind]

@[simp] lemma run_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.run sd (StateT.lift x : RState σ α) = sd.bind (fun s => x.map (fun a => (a, s))) := by
  change sd.bind (fun s => (fun a => (a, s)) <$> x) = sd.bind (fun s => x.map (fun a => (a, s)))
  simp [PMF.monad_map_eq_map]

@[simp] lemma eval_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.eval sd (StateT.lift x : RState σ α) = sd.bind (fun _ => x) := by
  rw [RState.eval, run_lift, PMF.map_bind]
  congr
  funext s
  rw [PMF.map_comp]
  simpa [Function.comp_def] using (PMF.map_id (p := x))

@[simp] lemma exec_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.exec sd (StateT.lift x : RState σ α) = sd := by
  rw [RState.exec, run_lift, PMF.map_bind]
  have h : (fun s : σ => PMF.map Prod.snd (PMF.map (fun a => (a, s)) x)) = (PMF.pure ∘ (id : σ → σ)) := by
    funext s
    rw [PMF.map_comp]
    change PMF.map (Function.const α s) x = PMF.pure s
    exact PMF.map_const (p := x) (b := s)
  rw [h, PMF.bind_pure_comp]
  simpa using (PMF.map_id (p := sd))

@[simp] lemma liftM_bind {σ α β} (x : PMF α) (f : α → PMF β) :
    (liftM (x >>= f) : RState σ β) =
      ((liftM x : RState σ α) >>= fun a => (liftM (f a) : RState σ β)) := by
  ext s
  simp [StateT.lift, StateT.bind, PMF.bind_bind]

@[simp] lemma liftM_pmf_bind {σ α β} (x : PMF α) (f : α → PMF β) :
    (liftM (x.bind f) : RState σ β) =
      ((liftM x : RState σ α) >>= fun a => (liftM (f a) : RState σ β)) := by
  change (liftM (x >>= f) : RState σ β) =
      ((liftM x : RState σ α) >>= fun a => (liftM (f a) : RState σ β))
  simp [liftM_bind]

@[simp] lemma liftM_pure {σ α} (a : α) :
    (liftM (PMF.pure a) : RState σ α) = (pure a : RState σ α) := by
  funext s
  change StateT.run (StateT.lift (PMF.pure a)) s = StateT.run (pure a : RState σ α) s
  rw [StateT.run_lift, StateT.run_pure]
  simpa [PMF.monad_map_eq_map] using (map_pure (f := PMF) (g := fun a => (a, s)) a)

@[simp] lemma liftM_uniformOfFintype_prod
    {σ A B : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    (liftM (PMF.uniformOfFintype (A × B)) : RState σ (A × B)) =
      (liftM
        (do
          let a ← PMF.uniformOfFintype A
          let b ← PMF.uniformOfFintype B
          pure (a, b)) : RState σ (A × B)) := by
  have h :
      PMF.uniformOfFintype (A × B) =
        (do
          let a ← PMF.uniformOfFintype A
          let b ← PMF.uniformOfFintype B
          pure (a, b)) := by
    simpa using
      (PMF.uniformOfFintype_prod_bind (A := A) (B := B)
        (f := fun p : A × B => PMF.pure p))
  simp [h]

@[simp] lemma bind_liftM_pmf_bind {σ α β γ}
    (x : PMF α) (g : α → PMF β) (rest : β → RState σ γ) :
    ((liftM (x.bind g) : RState σ β) >>= rest) =
      ((liftM x : RState σ α) >>= fun z => (liftM (g z) : RState σ β) >>= rest) := by
  funext s
  change (((StateT.lift (x.bind g) : RState σ β) >>= rest).run s) =
    (((StateT.lift x : RState σ α) >>= fun z => (StateT.lift (g z) : RState σ β) >>= rest).run s)
  simp [StateT.run_bind, StateT.run_lift]
  convert (PMF.bind_bind (p := x) (f := g) (g := fun a => StateT.run (rest a) s)) using 1

@[simp] lemma do_liftM_pmf_bind {σ α β γ}
    (x : PMF α) (g : α → PMF β) (rest : β → RState σ γ) :
    (do
      let k ← (liftM (x.bind g) : RState σ β)
      rest k) =
    (do
      let x' ← (liftM x : RState σ α)
      let k ← (liftM (g x') : RState σ β)
      rest k) := by
  simp [bind_liftM_pmf_bind (σ := σ) (x := x) (g := g) (rest := rest)]

@[simp] lemma bind_liftM_ignore {σ α β}
    (X : PMF α) (rest : RState σ β) :
    ((liftM X : RState σ α) >>= fun _ => rest) = rest := by
  funext s
  change StateT.run ((StateT.lift X : RState σ α) >>= fun _ => rest) s = StateT.run rest s
  rw [StateT.run_bind, StateT.run_lift]
  simp [PMF.bind_bind, PMF.bind_pure_comp]
  change X.bind (fun _ => StateT.run rest s) = StateT.run rest s
  rw [PMF.bind_const]

@[simp] lemma do_liftM_ignore {σ α β}
    (X : PMF α) (rest : RState σ β) :
    (do
      let _ ← (liftM X : RState σ α)
      rest) = rest := by
  simp [bind_liftM_ignore (σ := σ) (X := X) (rest := rest)]

/-- Move `get` before an independent lifted sample. -/
@[simp] lemma do_liftM_get_comm {σ α β}
    (X : PMF α) (rest : α → σ → RState σ β) :
    (do
      let x ← (liftM X : RState σ α)
      let s ← (get : RState σ σ)
      rest x s) =
    (do
      let s ← (get : RState σ σ)
      let x ← (liftM X : RState σ α)
      rest x s) := by
  funext s
  change
    StateT.run (((liftM X : RState σ α) >>= fun x =>
      (get : RState σ σ) >>= fun st => rest x st) : RState σ β) s =
      StateT.run (((get : RState σ σ) >>= fun st =>
        (liftM X : RState σ α) >>= fun x => rest x st) : RState σ β) s
  simp [StateT.run]
  rfl

/-- Collapse two consecutive `get`s into one. -/
@[simp] lemma do_get_get {σ α}
    (rest : σ → σ → RState σ α) :
    (do
      let s₁ ← (get : RState σ σ)
      let s₂ ← (get : RState σ σ)
      rest s₁ s₂) =
    (do
      let s ← (get : RState σ σ)
      rest s s) := by
  funext s
  change
    (do
      let p ← StateT.run (StateT.get : StateT σ PMF σ) s
      let p' ← StateT.run (StateT.get : StateT σ PMF σ) p.2
      StateT.run (rest p.1 p'.1) p'.2) =
    (do
      let p ← StateT.run (StateT.get : StateT σ PMF σ) s
      StateT.run (rest p.1 p.1) p.2)
  have hget : ∀ t : σ, StateT.run (StateT.get : StateT σ PMF σ) t = PMF.pure (t, t) := by
    intro t
    rfl
  simp [hget]
  change
    (PMF.pure (s, s)).bind (fun p =>
      (PMF.pure (p.2, p.2)).bind (fun p' => StateT.run (rest p.1 p'.1) p'.2)) =
    (PMF.pure (s, s)).bind (fun p => StateT.run (rest p.1 p.1) p.2)
  simp [PMF.pure_bind]

/-- Reading right after `set` returns the value that was set. -/
@[simp] lemma do_set_get {σ α}
    (s' : σ) (rest : σ → RState σ α) :
    (do
      let _ ← (set s' : RState σ Unit)
      let s ← (get : RState σ σ)
      rest s) =
    (do
      let _ ← (set s' : RState σ Unit)
      rest s') := by
  funext s
  change
    (do
      let p ← StateT.run (StateT.set s' : StateT σ PMF Unit) s
      let p' ← StateT.run (StateT.get : StateT σ PMF σ) p.2
      StateT.run (rest p'.1) p'.2) =
    (do
      let p ← StateT.run (StateT.set s' : StateT σ PMF Unit) s
      StateT.run (rest s') p.2)
  have hset : ∀ t : σ, StateT.run (StateT.set s' : StateT σ PMF Unit) t = PMF.pure ((), s') := by
    intro t
    rfl
  have hget : ∀ t : σ, StateT.run (StateT.get : StateT σ PMF σ) t = PMF.pure (t, t) := by
    intro t
    rfl
  simp [hset, hget]
  change
    PMF.bind (PMF.pure ((), s')) (fun p =>
      PMF.bind (PMF.pure (p.2, p.2)) (fun p' => StateT.run (rest p'.1) p'.2)) =
    PMF.bind (PMF.pure ((), s')) (fun p => StateT.run (rest s') p.2)
  simp [PMF.pure_bind]

/-- Two consecutive `set`s collapse to the last one. -/
@[simp] lemma do_set_set {σ α}
    (s₁ s₂ : σ) (rest : RState σ α) :
    (do
      let _ ← (set s₁ : RState σ Unit)
      let _ ← (set s₂ : RState σ Unit)
      rest) =
    (do
      let _ ← (set s₂ : RState σ Unit)
      rest) := by
  funext s
  change
    (do
      let p ← StateT.run (StateT.set s₁ : StateT σ PMF Unit) s
      let p' ← StateT.run (StateT.set s₂ : StateT σ PMF Unit) p.2
      StateT.run rest p'.2) =
    (do
      let p ← StateT.run (StateT.set s₂ : StateT σ PMF Unit) s
      StateT.run rest p.2)
  have hset1 : ∀ t : σ, StateT.run (StateT.set s₁ : StateT σ PMF Unit) t = PMF.pure ((), s₁) := by
    intro t
    rfl
  have hset2 : ∀ t : σ, StateT.run (StateT.set s₂ : StateT σ PMF Unit) t = PMF.pure ((), s₂) := by
    intro t
    rfl
  rw [hset1 s, hset2 s]
  change
    PMF.bind (PMF.pure ((), s₁))
      (fun _ : Unit × σ =>
        PMF.bind (PMF.pure ((), s₂)) (fun p' : Unit × σ => StateT.run rest p'.2)) =
    PMF.bind (PMF.pure ((), s₂)) (fun p' : Unit × σ => StateT.run rest p'.2)
  rw [PMF.pure_bind]

/-- Reading and immediately writing back the same state is a no-op. -/
@[simp] lemma do_get_set {σ α}
    (rest : σ → RState σ α) :
    (do
      let s ← (get : RState σ σ)
      (set s : RState σ Unit)
      rest s) =
    (do
        let s ← get
        rest s) := by
  funext st
  simp [get, bind, getThe, MonadStateOf.get, StateT.get, StateT.bind, pure, set, StateT.set]


/-- Move `set` before an independent lifted sample. -/
@[simp] lemma do_liftM_set_comm {σ α β}
    (X : PMF α) (s' : σ) (rest : α → RState σ β) :
    (do
      let x ← (liftM X : RState σ α)
      let _ ← (set s' : RState σ Unit)
      rest x) =
    (do
      let _ ← (set s' : RState σ Unit)
      let x ← (liftM X : RState σ α)
      rest x) := by
  funext s
  change
    StateT.run (((StateT.lift X : RState σ α) >>= fun x =>
      (set s' : RState σ Unit) >>= fun _ => rest x) : RState σ β) s =
      StateT.run (((set s' : RState σ Unit) >>= fun _ =>
        (StateT.lift X : RState σ α) >>= fun x => rest x) : RState σ β) s
  simp [set, StateT.set, StateT.run_bind, StateT.run_lift, PMF.bind_bind]
  simpa using
    (PMF.bind_comm (p := X) (q := (StateT.set s').run s)
      (f := fun a p => StateT.run (rest a) p.2))

/-- Commuting two independent lifted `PMF` samples in `RState`.

Not marked `[simp]` to avoid commutativity rewrite loops. -/
lemma do_liftM_comm {σ α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → RState σ γ) :
    (do
      let x ← (liftM A : RState σ α)
      let y ← (liftM B : RState σ β)
      rest x y) =
    (do
      let y ← (liftM B : RState σ β)
      let x ← (liftM A : RState σ α)
      rest x y) := by
  funext s
  change StateT.run ((liftM A : RState σ α) >>= fun x => do
      let y ← (liftM B : RState σ β)
      rest x y) s =
    StateT.run ((liftM B : RState σ β) >>= fun y => do
      let x ← (liftM A : RState σ α)
      rest x y) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_bind]
  simpa using (PMF.bind_comm (p := A) (q := B) (f := fun a b => StateT.run (rest a b) s))

/-- Commuting an independent lifted sample past a subsequent lifted sample that depends on
an earlier draw. -/
lemma do_liftM_comm_dep {σ α β γ δ}
    (B : PMF β) (A : PMF α) (C : β → PMF γ) (rest : β → α → γ → RState σ δ) :
    (do
      let b ← (liftM B : RState σ β)
      let a ← (liftM A : RState σ α)
      let c ← (liftM (C b) : RState σ γ)
      rest b a c) =
    (do
      let b ← (liftM B : RState σ β)
      let c ← (liftM (C b) : RState σ γ)
      let a ← (liftM A : RState σ α)
      rest b a c) := by
  refine congrArg (fun f => Bind.bind (liftM B : RState σ β) f) ?_
  funext b
  simpa using
    (do_liftM_comm (A := A) (B := C b) (rest := fun a c => rest b a c))

/-- Rewriting a lifted uniform draw over pairs as two lifted independent uniform draws. -/
@[simp] lemma do_liftM_uniformOfFintype_prod
    {σ A B α : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (rest : A × B → RState σ α) :
    (do
      let p ← (liftM (PMF.uniformOfFintype (A × B)) : RState σ (A × B))
      rest p) =
    (do
      let a ← (liftM (PMF.uniformOfFintype A) : RState σ A)
      let b ← (liftM (PMF.uniformOfFintype B) : RState σ B)
      rest (a, b)) := by
  funext s
  change
    StateT.run (((liftM (PMF.uniformOfFintype (A × B)) : RState σ (A × B)) >>= fun p => rest p) :
      RState σ α) s =
      StateT.run (((liftM (PMF.uniformOfFintype A) : RState σ A) >>= fun a =>
        ((liftM (PMF.uniformOfFintype B) : RState σ B) >>= fun b => rest (a, b))) :
          RState σ α) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_lift, PMF.bind_bind]

/-- Transporting a uniform `PMF` sample across an equivalence. -/
lemma bind_uniformOfFintype_equiv {X Y α : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) (g : Y → PMF α) :
    (PMF.uniformOfFintype Y).bind g =
      (PMF.uniformOfFintype X).bind (fun x => g (e x)) := by
  ext a
  have htsum :
      ∑' y : Y, ((Fintype.card Y : ENNReal)⁻¹ * (g y) a) =
        ∑' x : X, ((Fintype.card Y : ENNReal)⁻¹ * (g (e x)) a) := by
    simpa using
      (Equiv.tsum_eq e (fun y : Y => ((Fintype.card Y : ENNReal)⁻¹ * (g y) a))).symm
  calc
    ((PMF.uniformOfFintype Y).bind g) a =
        ∑' y : Y, ((Fintype.card Y : ENNReal)⁻¹ * (g y) a) := by
          simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    _ = ∑' x : X, ((Fintype.card Y : ENNReal)⁻¹ * (g (e x)) a) := htsum
    _ = ((PMF.uniformOfFintype X).bind (fun x => g (e x))) a := by
          simp [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- Transporting a lifted uniform sample across an equivalence in `RState`.

Not marked `[simp]`; use explicitly where needed. -/
lemma do_liftM_uniformOfFintype_equiv {σ X Y α : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) (g : Y → RState σ α) :
    (do
      let y ← (liftM (PMF.uniformOfFintype Y) : RState σ Y)
      g y) =
    (do
      let x ← (liftM (PMF.uniformOfFintype X) : RState σ X)
      g (e x)) := by
  funext s
  change
    StateT.run (((liftM (PMF.uniformOfFintype Y) : RState σ Y) >>= fun y => g y) : RState σ α) s =
      StateT.run (((liftM (PMF.uniformOfFintype X) : RState σ X) >>= fun x => g (e x)) :
        RState σ α) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_lift]
  simpa using bind_uniformOfFintype_equiv (e := e) (g := fun y => StateT.run (g y) s)

/-- Rewriting a lifted uniform sample via an equivalence, in direct `liftM` form. -/
lemma liftM_uniformOfFintype_equiv {σ X Y : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) :
    (liftM (PMF.uniformOfFintype Y) : RState σ Y) =
      (liftM
        (do
          let x ← PMF.uniformOfFintype X
          pure (e x)) : RState σ Y) := by
  have h :
      PMF.uniformOfFintype Y =
        (do
          let x ← PMF.uniformOfFintype X
          pure (e x)) := by
    calc
      PMF.uniformOfFintype Y = (PMF.uniformOfFintype Y).bind PMF.pure := by simp
      _ = (PMF.uniformOfFintype X).bind (fun x => PMF.pure (e x)) := by
            simpa using (bind_uniformOfFintype_equiv (e := e) (g := PMF.pure))
      _ = (do
            let x ← PMF.uniformOfFintype X
            pure (e x)) := rfl
  simp [h]

/-- Equivalence between `(BitVec n × BitVec m)` and `BitVec (n + m)` via concatenation. -/
def bitVecAppendEquiv (n m : ℕ) : (BitVec n × BitVec m) ≃ BitVec (n + m) where
  toFun p := p.1 ++ p.2
  invFun z := (z.extractLsb' m n, z.setWidth m)
  left_inv := by
    intro p
    rcases p with ⟨x, y⟩
    apply Prod.ext
    · simpa using
        (BitVec.extractLsb'_append_eq_of_le
          (xhi := x) (xlo := y) (start := m) (len := n)
          (h := Nat.le_refl m))
    · simpa using (BitVec.setWidth_append (x := x) (y := y) (k := m))
  right_inv := by
    intro z
    apply BitVec.eq_of_getElem_eq
    intro i hi
    by_cases hlt : i < m
    · rw [BitVec.getElem_append (x := z.extractLsb' m n) (y := z.setWidth m) (h := hi)]
      simp [hlt]
      exact BitVec.getLsbD_eq_getElem (x := z) (i := i) hi
    · rw [BitVec.getElem_append (x := z.extractLsb' m n) (y := z.setWidth m) (h := hi)]
      simp [hlt]
      have hi' : m + (i - m) = i := by omega
      simpa [hi'] using
        (BitVec.getLsbD_eq_getElem (x := z) (i := m + (i - m)) (h := by omega))

/-- The low `k` bits of `y ++ x` are exactly `x`. -/
@[simp] lemma extractLsb'_zero_append_right {k m : ℕ}
    (x : BitVec k) (y : BitVec m) :
    BitVec.extractLsb' 0 k (y ++ x) = x := by
  rw [← BitVec.setWidth_eq_extractLsb' (x := y ++ x) (w := k) (h := by omega)]
  simp [BitVec.setWidth_append]

/-- The high `k` bits of `x ++ y` (starting at offset `m`) are exactly `x`. -/
@[simp] lemma extractLsb'_append_high_right {k m : ℕ}
    (x : BitVec k) (y : BitVec m) :
    BitVec.extractLsb' m k (x ++ y) = x := by
  simpa using
    (BitVec.extractLsb'_append_eq_of_le
      (xhi := x) (xlo := y) (start := m) (len := k)
      (h := Nat.le_refl m))

/-- Relating generic `cast` on `BitVec` to `BitVec.cast`. -/
lemma cast_congrArg_bitVec_eq_bitVec_cast {n m : ℕ} (h : n = m) (z : BitVec n) :
    (cast (congrArg BitVec h) z : BitVec m) = BitVec.cast h z := by
  cases h
  rfl

/-- Specialized cast-normalization for `BitVec (k + k)` to `BitVec (2 * k)`. -/
@[simp] lemma cast_bitVec_two_mul_eq {k : ℕ} (z : BitVec (k + k)) :
    (cast (by simp [two_mul]) z : BitVec (2 * k)) = BitVec.cast (by simp [two_mul]) z := by
  have h : (k + k) = (2 * k) := by simp [two_mul]
  simpa [h] using (cast_congrArg_bitVec_eq_bitVec_cast (h := h) (z := z))

/-- Direct `liftM` form of the append equivalence rewrite for `BitVec`. -/
@[simp] lemma liftM_uniformOfFintype_bitVec_append
    {σ : Type} {n m : ℕ}
    [Fintype (BitVec n)] [Nonempty (BitVec n)]
    [Fintype (BitVec m)] [Nonempty (BitVec m)]
    [Fintype (BitVec (n + m))] [Nonempty (BitVec (n + m))] :
    (liftM (PMF.uniformOfFintype (BitVec (n + m))) : RState σ (BitVec (n + m))) =
      (liftM
        (do
          let p ← PMF.uniformOfFintype (BitVec n × BitVec m)
          pure (p.1 ++ p.2)) : RState σ (BitVec (n + m))) := by
  simpa [bitVecAppendEquiv] using
    (liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec n × BitVec m) (Y := BitVec (n + m))
      (e := bitVecAppendEquiv n m))

/-- Instantiation of `do_liftM_uniformOfFintype_equiv` for `BitVec` concatenation.

Not marked `[simp]`; use explicitly where needed. -/
lemma do_liftM_uniformOfFintype_bitVec_append
    {σ α : Type} {n m : ℕ}
    [Fintype (BitVec n)] [Nonempty (BitVec n)]
    [Fintype (BitVec m)] [Nonempty (BitVec m)]
    [Fintype (BitVec (n + m))] [Nonempty (BitVec (n + m))]
    (g : BitVec (n + m) → RState σ α) :
    (do
      let z ← (liftM (PMF.uniformOfFintype (BitVec (n + m))) : RState σ (BitVec (n + m)))
      g z) =
    (do
      let p ← (liftM (PMF.uniformOfFintype (BitVec n × BitVec m)) : RState σ (BitVec n × BitVec m))
      g (p.1 ++ p.2)) := by
  simp [bitVecAppendEquiv, do_liftM_uniformOfFintype_equiv (σ := σ)]

/-- Bind-form variant of `do_liftM_uniformOfFintype_bitVec_append`.

Not marked `[simp]`; use explicitly where needed. -/
lemma bind_uniformOfFintype_bitVec_append
    {σ α : Type} {n m : ℕ}
    [Fintype (BitVec n)] [Nonempty (BitVec n)]
    [Fintype (BitVec m)] [Nonempty (BitVec m)]
    [Fintype (BitVec (n + m))] [Nonempty (BitVec (n + m))]
    (g : BitVec (n + m) → RState σ α) :
    ((liftM (PMF.uniformOfFintype (BitVec (n + m))) : RState σ (BitVec (n + m))) >>= g) =
      ((liftM (PMF.uniformOfFintype (BitVec n × BitVec m)) : RState σ (BitVec n × BitVec m)) >>=
        fun p => g (p.1 ++ p.2)) := by
  simp [do_liftM_uniformOfFintype_bitVec_append (σ := σ) (n := n) (m := m) (g := g)]

/-- Equivalence between `BitVec (k + k)` and `BitVec (2 * k)`. -/
def bitVecAddEquivTwoMul (k : ℕ) : BitVec (k + k) ≃ BitVec (2 * k) where
  toFun x := BitVec.cast (by simp [two_mul]) x
  invFun y := BitVec.cast (by simp [two_mul]) y
  left_inv := by intro x; simp
  right_inv := by intro y; simp

/-- Rewriting uniform sampling on `BitVec (2 * k)` as sampling on `BitVec (k + k)`.

Marked `[simp]` so terms that sample `BitVec (2 * k)` can normalize to `k + k` shape. -/
@[simp] lemma do_liftM_uniformOfFintype_bitVec_two_mul
    {σ α : Type} {k : ℕ}
    [Fintype (BitVec (k + k))] [Nonempty (BitVec (k + k))]
    [Fintype (BitVec (2 * k))] [Nonempty (BitVec (2 * k))]
    (g : BitVec (2 * k) → RState σ α) :
    (do
      let y ← (liftM (PMF.uniformOfFintype (BitVec (2 * k))) : RState σ (BitVec (2 * k)))
      g y) =
    (do
      let x ← (liftM (PMF.uniformOfFintype (BitVec (k + k))) : RState σ (BitVec (k + k)))
      g (cast (by simp [two_mul]) x)) := by
  simpa [bitVecAddEquivTwoMul] using
    (do_liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec (k + k)) (Y := BitVec (2 * k))
      (e := bitVecAddEquivTwoMul k) (g := g))

@[simp] lemma liftM_uniformOfFintype_bitVec_two_mul
    {σ : Type} {k : ℕ}
    [Fintype (BitVec (k + k))] [Nonempty (BitVec (k + k))]
    [Fintype (BitVec (2 * k))] [Nonempty (BitVec (2 * k))] :
    (liftM (PMF.uniformOfFintype (BitVec (2 * k))) : RState σ (BitVec (2 * k))) =
      (liftM
        (do
          let x ← PMF.uniformOfFintype (BitVec (k + k))
          pure (cast (by simp [two_mul]) x)) : RState σ (BitVec (2 * k))) := by
  simpa [bitVecAddEquivTwoMul] using
    (liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec (k + k)) (Y := BitVec (2 * k))
      (e := bitVecAddEquivTwoMul k))

noncomputable
def coinFlip {σ} : RState σ Bool :=
  StateT.lift (PMF.uniformOfFintype Bool)

end RState
