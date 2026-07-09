import Mathlib.Tactic.Attr.Register

/-- Simp set for PMF-normalization lemmas used in GameHoppingInLean. -/
register_simp_attr sPMF

/-- Simp set for rewriting normalized `PMF` terms back into monadic notation for display. -/
register_simp_attr GameHoppingPrettyPrintPMF
