import GameHoppingInLean.Comp.RState

/-!
Applied normalization lemmas for `RState`.

This file intentionally avoids lemmas that rewrite one unapplied `RState`
computation into another.  The lemmas here expose the result of running or
applying an `RState` computation.
-/

namespace RState

@[RStateSimplifier] lemma run_get {σ} (s : σ) :
    StateT.run (get : RState σ σ) s = PMF.pure (s, s) := rfl

@[RStateSimplifier] lemma get_apply {σ} (s : σ) :
    (get : RState σ σ) s = PMF.pure (s, s) := rfl

@[RStateSimplifier] lemma run_map_get {σ α} (f : σ → α) (s : σ) :
    StateT.run (f <$> (get : RState σ σ)) s = PMF.pure (f s, s) := by
  change StateT.run (StateT.map f (get : RState σ σ)) s = PMF.pure (f s, s)
  unfold StateT.map
  change PMF.map (fun a : σ × σ => (f a.1, a.2)) (PMF.pure ((s, s) : σ × σ)) =
    PMF.pure (f s, s)
  exact PMF.pure_map (fun a : σ × σ => (f a.1, a.2)) ((s, s) : σ × σ)

@[RStateSimplifier] lemma map_get_apply {σ α} (f : σ → α) (s : σ) :
    (f <$> (get : RState σ σ)) s = PMF.pure (f s, s) := by
  exact run_map_get f s

@[RStateSimplifier] lemma run_liftM {σ α} (x : PMF α) (s : σ) :
    StateT.run (liftM x : RState σ α) s = x.map (fun a => (a, s)) := by
  change x.bind (PMF.pure ∘ fun a => (a, s)) = x.map (fun a => (a, s))
  rw [PMF.bind_pure_comp]

@[RStateSimplifier] lemma liftM_apply {σ α} (x : PMF α) (s : σ) :
    (liftM x : RState σ α) s = x.map (fun a => (a, s)) := by
  exact run_liftM x s

@[RStateSimplifier] lemma stateT_lift_apply {σ α} (x : PMF α) (s : σ) :
    (StateT.lift x : RState σ α) s = x.map (fun a => (a, s)) := by
  exact run_liftM x s

@[RStateSimplifier] lemma run_pure_apply {σ α} (x : α) (s : σ) :
    StateT.run (pure x : RState σ α) s = PMF.pure (x, s) := rfl

@[RStateSimplifier] lemma pure_apply {σ α} (x : α) (s : σ) :
    (pure x : RState σ α) s = PMF.pure (x, s) := rfl

@[RStateSimplifier] lemma run_modify {σ} (f : σ → σ) (s : σ) :
    StateT.run (modify f : RState σ Unit) s = PMF.pure ((), f s) := by
  simp only [modify, StateT.run_bind]
  simp [GameHoppingSimplifyPMF]

@[RStateSimplifier] lemma modify_apply {σ} (f : σ → σ) (s : σ) :
    (modify f : RState σ Unit) s = PMF.pure ((), f s) := by
  change StateT.run (modify f : RState σ Unit) s = PMF.pure ((), f s)
  exact run_modify f s

@[RStateSimplifier] lemma run_monadState_modify {σ} (f : σ → σ) (s : σ) :
    StateT.run (_root_.modify f : RState σ Unit) s = PMF.pure ((), f s) := rfl

@[RStateSimplifier] lemma monadState_modify_apply {σ} (f : σ → σ) (s : σ) :
    (_root_.modify f : RState σ Unit) s = PMF.pure ((), f s) := rfl

@[RStateSimplifier] lemma modify_snd_apply {α β} (f : β → β) (x : α) (y : β) :
    (modify (fun p : α × β => (p.1, f p.2)) : RState (α × β) Unit) (x, y) =
      PMF.pure ((), (x, f y)) := by
  exact modify_apply (fun p : α × β => (p.1, f p.2)) (x, y)

@[RStateSimplifier] lemma run_runOnFst {s₁ s₂ α}
    (m : RState s₁ α) (st : s₁ × s₂) :
    StateT.run (runOnFst (s₂ := s₂) m) st =
      (StateT.run m st.1).map (fun p => (p.1, (p.2, st.2))) := rfl

@[RStateSimplifier] lemma run_runOnSnd {s₁ s₂ α}
    (m : RState s₂ α) (st : s₁ × s₂) :
    StateT.run (runOnSnd (s₁ := s₁) m) st =
      (StateT.run m st.2).map (fun p => (p.1, (st.1, p.2))) := rfl

@[RStateSimplifier] lemma run_pure {σ α} (sd : PMF σ) (a : α) :
    RState.run sd (pure a : RState σ α) = sd.map (fun s => (a, s)) := by
  simpa [RState.run, Function.comp_def] using
    (PMF.bind_pure_comp (p := sd) (f := fun s => (a, s)))

@[RStateSimplifier] lemma eval_pure {σ α} (sd : PMF σ) (a : α) :
    RState.eval sd (pure a : RState σ α) = PMF.pure a := by
  rw [RState.eval, run_pure]
  rw [PMF.map_comp]
  simp [PMF.map_const]

@[RStateSimplifier] lemma exec_pure {σ α} (sd : PMF σ) (a : α) :
    RState.exec sd (pure a : RState σ α) = sd := by
  rw [RState.exec, run_pure]
  rw [PMF.map_comp]
  simpa using (PMF.map_id (p := sd))

@[RStateSimplifier] lemma run_bind {σ α β}
    (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.run sd (m >>= f) =
      (RState.run sd m).bind (fun p => StateT.run (f p.1) p.2) := by
  change sd.bind (fun s => (StateT.run m s).bind (fun p => StateT.run (f p.1) p.2)) =
      (sd.bind fun s => StateT.run m s).bind (fun p => StateT.run (f p.1) p.2)
  exact (PMF.bind_bind (p := sd) (f := fun s => StateT.run m s)
    (g := fun p => StateT.run (f p.1) p.2)).symm

@[RStateSimplifier] lemma run_bind2 {σ α β} (sd : σ) (m : RState σ α)
    (f : α → RState σ β) :
    (m >>= f) sd = (m sd).bind (fun p => StateT.run (f p.1) p.2) := by
  rfl

@[RStateSimplifier] lemma eval_bind {σ α β}
    (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.eval sd (m >>= f) =
      (RState.run sd m).bind (fun p => (StateT.run (f p.1) p.2).map Prod.fst) := by
  rw [RState.eval, run_bind, PMF.map_bind]

@[RStateSimplifier] lemma exec_bind {σ α β}
    (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.exec sd (m >>= f) =
      (RState.run sd m).bind (fun p => (StateT.run (f p.1) p.2).map Prod.snd) := by
  rw [RState.exec, run_bind, PMF.map_bind]

@[RStateSimplifier] lemma run_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.run sd (StateT.lift x : RState σ α) =
      sd.bind (fun s => x.map (fun a => (a, s))) := by
  apply congrArg (fun f => sd.bind f)
  funext s
  change x.bind (PMF.pure ∘ fun a => (a, s)) = x.map (fun a => (a, s))
  rw [PMF.bind_pure_comp]

@[RStateSimplifier] lemma eval_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.eval sd (StateT.lift x : RState σ α) = sd.bind (fun _ => x) := by
  rw [RState.eval, run_lift, PMF.map_bind]
  congr
  funext s
  rw [PMF.map_comp]
  simpa [Function.comp_def] using (PMF.map_id (p := x))

@[RStateSimplifier] lemma exec_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.exec sd (StateT.lift x : RState σ α) = sd := by
  rw [RState.exec, run_lift, PMF.map_bind]
  have h : (fun s : σ => PMF.map Prod.snd (PMF.map (fun a => (a, s)) x)) =
      (PMF.pure ∘ (id : σ → σ)) := by
    funext s
    rw [PMF.map_comp]
    change PMF.map (Function.const α s) x = PMF.pure s
    exact PMF.map_const (p := x) (b := s)
  rw [h, PMF.bind_pure_comp]
  simpa using (PMF.map_id (p := sd))

end RState
