# Summary of changes for run a22b61a0-0482-4b4b-b913-71bf967d305e
Completed the original task on `GameHoppingInLean/Examples/Proofs/GGMSecurePRF.lean`.

The file did not contain literal `sorry`s but had three broken proof steps inside `obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb` that caused the build to fail (an unsolved-goals error and two `simp made no progress` errors). All three were in the state-monad/PMF reduction of the cache-abstraction commuting square.

Fixes, following the requested style (`simp [correctAbstractionDiagSimps, sRState, sPMF]` and the project's `sStateT` set):
- In the cached-query (`pos`) branch, extended the closing `simp` with `bind, pure, StateT.bind, StateT.pure` and the project simp sets so the `StateT.pure`/`PMF.bind` reduction goes through.
- In both uncached-query sub-branches (`query[i] = true` / `false`), added `bind` and `pure` to the `simp only` so the `StateT.set >>= …` (a genuine `Bind.bind`) actually unfolds, letting the subsequent `expandCache_insert_union` rewrite apply.

Verification: `lake build` completes successfully for the whole project; `GGMSecurePRF.lean` contains no `sorry`/`admit`; and `#print axioms` for both the fixed lemma `obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb` and the top-level result `secureGGM_of_securePRG` lists only `[propext, Classical.choice, Quot.sound]`.

Only cosmetic linter warnings (whitespace, isolated `·`, `show` vs `change`, empty line) remain in the file; these do not affect correctness or the build.

# Summary of changes for run 7a5df0c4-57af-4076-b684-09339b7f92ed
Filled in the `sorry` in `abstraction_with_levels_and_reach` in `GameHoppingInLean/ComputationalIndistinguishibility/ObservationEquivalenceReach.lean`.

The lemma is an abstraction/bisimulation statement: given a probabilistic state map `cs : T → PMF S`, a level function `lvl`, a reachability predicate `reach`, a per-step level/reachability preservation hypothesis, and a commuting-square step hypothesis (valid while the budget `q_b` is not exhausted), it shows that running any oracle computation `c` (over `withPMFSpec O`) through the two simulated implementations yields the same output distribution, as long as `lvl τ + depth c ≤ q_b`.

The proof proceeds by structural induction on the computation `c`:
- pure case: both sides reduce to `pure x`, using that `cs τ` is a probability measure (`PMF.bind_const`).
- roll/oracle case (an actual oracle query): unfold `simulateQ` and the state-monad bind, derive `lvl τ + 1 ≤ q_b` and the per-output budget bound from the depth equation, apply the commuting-square hypothesis `HSTEP`, then close pointwise on the support via the induction hypothesis, using `Hstep_reach` for the level/reachability side conditions.
- roll/sample case (internal sampling, state unchanged): unfold the lift, commute the sampling distribution past `cs τ` (`PMF.bind_comm`), and apply the induction hypothesis pointwise.

Verified: the file builds cleanly with the module built explicitly, no `sorry` remains, the dependent file `ObsEqComp.lean` still compiles, and the lemma depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

# Summary of changes for run e3d13779-e4ec-4e37-aeb8-be3833593266
I filled both `sorry`s in `GameHoppingInLean/ComputationalIndistinguishibility/ObsEqComp.lean`, so that file (and the whole project) now builds with **no `sorry`**, and the affected theorems depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

The two originally-unproven lemmas were:

1. `behavioral_eq_from_obsEq` — bounded observational equivalence of two oracles implies their behavioural oracles (`BehavioralOracle.into`) are equal. Short proof: reduce to equality of the `process` fields and apply the hypothesis to the reversed query list.

2. `rState2Rstate_non_dist` — the hard one (the original authors marked it "quite hard" and left it open): passing an adversary through the behavioural-oracle round-trip `rState2Rstate q_b o` does not change its output distribution, provided the adversary asks at most `q_b` queries. With it, the downstream lemmas `obsEq_distinquishing`, `obsEq_distinquishing_adv`, and `obsEq_distinquishing_ub` are now fully proven too.

To prove (2) I added a new, self-contained, Mathlib-only file `GameHoppingInLean/ComputationalIndistinguishibility/PMFDisintegration.lean` containing the probability-theoretic core (all fully proven):
- `PMF.condOn` (defaulted conditioning) and the disintegration law `PMF.map_bind_condOn_fiber`;
- conditioning algebra: `PMF.condOn_eq_self`, `PMF.condOn_map`, `PMF.condOn_condOn`, `PMF.condOn_bind_of_upstream`, `PMF.condOn_congr_on_support`, `PMF.map_congr_on_support`, `PMF.bindCongrOnSupport`;
- a generic adaptive-computation model `GTree` with evaluator `geval`/`GTree.depth`, and the key induction `geval_reconstruct`: if a reconstructed oracle and a conditional-state map satisfy a one-step compatibility square (within budget, on reachable states), then any bounded-depth computation has the same output distribution against the original kernel and against the reconstruction.

In `ObsEqComp.lean` I then built the bridge from the concrete VCVio constructions to this generic lemma: `toGTree` (free-monad → `GTree`), the `geval`/`simulateQ` correspondence, depth agreement, the conditional-state `condState`, the reconstructed-oracle query equation `rState2Rstate_queries_eq`, the joint-distribution append lemma, a reachability predicate with its preservation (`reachT`, `Hstep_reach`), and the central conditional-probability identities (`condState_bind_query_eq`, `behavioral_process_eq`, `hstep`) which discharge the compatibility square via the disintegration engine.

Note on tooling: the automated prover could not load this project directly because a VCVio dependency (`ToMathlib.PFunctor.*`) is compiled with Lean's experimental `module` system, whose split data files its loader could not find (reported separately). I worked around this by isolating all reusable, dependency-free probability lemmas into the new Mathlib-only file (where automation does work) and assembling the VCVio-typed remainder by hand.

Verification: `lake build` completes successfully for the whole project; `GameHoppingInLean.ComputationalIndistinguishibility.ObsEqComp` and `...PMFDisintegration` contain no `sorry`/`axiom`/`@[implemented_by]`; and `#print axioms` for `rState2Rstate_non_dist`, `behavioral_eq_from_obsEq`, and `obsEq_distinquishing_ub` lists only `[propext, Classical.choice, Quot.sound]`.