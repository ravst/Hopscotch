import Mathlib.Tactic.Attr.Register

/-- Simp set for unfolding oracle-reduction plumbing. -/
register_simp_attr OracleReductionSimps

/-- Simp set for unfolding correct-abstraction state-diagram plumbing. -/
register_simp_attr correctAbstractionDiagSimps

/-- Simp set for unfolding basic `StateT` operations. -/
register_simp_attr StateTSimps

/-- Simp set for definitions that game-hopping automation may unfold. -/
register_simp_attr game_hopping_unfold
