import Mathlib.Tactic.Attr.Register

/-- Simp set for unfolding oracle-reduction plumbing. -/
register_simp_attr sReduction

/-- Simp set for unfolding correct-abstraction state-diagram plumbing. -/
register_simp_attr correctAbstractionDiagSimps

/-- Simp set for unfolding basic `StateT` operations. -/
register_simp_attr sStateT

/-- Simp set for definitions that game-hopping automation may unfold. -/
register_simp_attr game_hopping_unfold

/-- Simp set for the state-commutation step of `goodDoubleAction`: it unfolds the
simulation/state-threading plumbing while keeping `simulateQ` folded so induction
hypotheses still match. -/
register_simp_attr goodDoubleActionSimps
register_simp_attr universal
