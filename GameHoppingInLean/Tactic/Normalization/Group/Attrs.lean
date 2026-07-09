import Mathlib.Tactic.Attr.Register

/-- Simp set for routine group normalization lemmas used in GameHoppingInLean. -/
register_simp_attr GH_group_norm

/--
Simp set for rewrites that replace sampled generator exponents by uniform group samples.
These rewrites can destroy syntactic exponent structure, so keep them separate from
`GH_group_norm` and invoke them deliberately.
-/
register_simp_attr GH_group_random_exp
