# Summary of changes for run b13763cf-16ec-41b2-8c0f-a3f34446974c
Both remaining proof holes are filled; `lake build` succeeds for the whole project with no `sorry` (or `admit`/`axiom`/`@[implemented_by]`) anywhere, and `#print axioms` for the affected results lists only `propext`, `Classical.choice`, `Quot.sound`.

**1. `correctUntilBad_approxEq` (`Hopscotch/ApproxEq/CorrectUntilBad.lean`)** — the fundamental lemma of game playing. The statement, the two structures and `initialBadEventBound` are untouched; the one-sided bad-event bound (given only for `queries₁`) is what the proof uses. Added proof-internal helpers, all `private` inside a new `CorrectUntilBad` namespace:
- splitting a `tsum` into its bad and good parts;
- `badmass_eq` / `badexp_eq`: two kernels agreeing outside the bad set assign the same mass, and the same expectation to any valuation equal to 1 on bad states — this is what makes the one-sided bound suffice for both directions;
- `exp_le_of_agree`: the one-step expectation estimate; `exp_le_of_uniform`: averaging a uniform estimate;
- `enat_pred`: peeling one unit of query budget in `ℕ∞`; a local restatement of the `simulateQ`/`FreeM.roll` unfolding (its usual home is not among this file's imports, which I left unchanged);
- `run_le`: the main induction over the adversary's free-monad computation, giving two-sided `ENNReal` estimates for the probability of output `true` (oracle-query nodes consume budget and invoke the Bellman-style bound; sampling nodes do not).
These are averaged over the initial-state distributions and converted to the real-valued advantage.

**2. `computationalSoundness_internal` (`Hopscotch/ComputationalIndistinguishability/Soundness.lean`)** — proved by induction on the `IndistinguishableI` derivation, keeping the residual formulation `|advantage − assumption contribution| ≤ statistical error` exactly as stated. Added helper lemmas next to the existing ones in the same file: `advBoundQWithError_of_advBoundQ`, `assumptionJoiner_sum` (splitting the joined assumption contribution), `transitive_step_proof_error` (errors add across a transitive step), `long_step_error_induction` (long hybrid sequences, errors summing over the prefix), `ascToReal_identity` (an assumption used through the trivial reduction contributes exactly its advantage) and `ascToReal_rcompose_map` (composing all stored reductions with an outer reduction equals composing that reduction with the adversary). The `approxEq` case uses the `ApproxEq` hypothesis directly, so the statistical error propagates through `trans`, `symm`, `reduction` and `longSequence` as defined.

No theorem statements, definitions, imports or other existing declarations were modified; the only additions are the helper lemmas above. `ARISTOTLE_SUMMARY.md` records the changes, and all work is committed and pushed.

# Summary of changes for run a22b61a0-0482-4b4b-b913-71bf967d305e
Completed the original task on `Hopscotch/Examples/Proofs/GGMSecurePRF.lean`.

The file did not contain literal `sorry`s but had three broken proof steps inside `obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb` that caused the build to fail (an unsolved-goals error and two `simp made no progress` errors). All three were in the state-monad/PMF reduction of the cache-abstraction commuting square.

Fixes, following the requested style (`simp [correctAbstractionDiagSimps, sRState, sPMF]` and the project's `sStateT` set):
- In the cached-query (`pos`) branch, extended the closing `simp` with `bind, pure, StateT.bind, StateT.pure` and the project simp sets so the `StateT.pure`/`PMF.bind` reduction goes through.
- In both uncached-query sub-branches (`query[i] = true` / `false`), added `bind` and `pure` to the `simp only` so the `StateT.set >>= …` (a genuine `Bind.bind`) actually unfolds, letting the subsequent `expandCache_insert_union` rewrite apply.

Verification: `lake build` completes successfully for the whole project; `GGMSecurePRF.lean` contains no `sorry`/`admit`; and `#print axioms` for both the fixed lemma `obsEq_PRF_ideal_cache_batch_flipMsb2_flipMsb` and the top-level result `secureGGM_of_securePRG` lists only `[propext, Classical.choice, Quot.sound]`.

Only cosmetic linter warnings (whitespace, isolated `·`, `show` vs `change`, empty line) remain in the file; these do not affect correctness or the build.

# Summary of changes for run 7a5df0c4-57af-4076-b684-09339b7f92ed
Filled in the `sorry` in `abstraction_with_levels_and_reach` in `Hopscotch/ComputationalIndistinguishability/ObservationEquivalenceReach.lean`.

The lemma is an abstraction/bisimulation statement: given a probabilistic state map `cs : T → PMF S`, a level function `lvl`, a reachability predicate `reach`, a per-step level/reachability preservation hypothesis, and a commuting-square step hypothesis (valid while the budget `q_b` is not exhausted), it shows that running any oracle computation `c` (over `withPMFSpec O`) through the two simulated implementations yields the same output distribution, as long as `lvl τ + depth c ≤ q_b`.

The proof proceeds by structural induction on the computation `c`:
- pure case: both sides reduce to `pure x`, using that `cs τ` is a probability measure (`PMF.bind_const`).
- roll/oracle case (an actual oracle query): unfold `simulateQ` and the state-monad bind, derive `lvl τ + 1 ≤ q_b` and the per-output budget bound from the depth equation, apply the commuting-square hypothesis `HSTEP`, then close pointwise on the support via the induction hypothesis, using `Hstep_reach` for the level/reachability side conditions.
- roll/sample case (internal sampling, state unchanged): unfold the lift, commute the sampling distribution past `cs τ` (`PMF.bind_comm`), and apply the induction hypothesis pointwise.

Verified: the file builds cleanly with the module built explicitly, no `sorry` remains, the dependent file `ObsEqComp.lean` still compiles, and the lemma depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

# Summary of changes for run e3d13779-e4ec-4e37-aeb8-be3833593266
I filled both `sorry`s in `Hopscotch/ComputationalIndistinguishability/ObsEqComp.lean`, so that file (and the whole project) now builds with **no `sorry`**, and the affected theorems depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

The two originally-unproven lemmas were:

1. `behavioral_eq_from_obsEq` — bounded observational equivalence of two oracles implies their behavioural oracles (`BehavioralOracle.into`) are equal. Short proof: reduce to equality of the `process` fields and apply the hypothesis to the reversed query list.

2. `rState2Rstate_non_dist` — the hard one (the original authors marked it "quite hard" and left it open): passing an adversary through the behavioural-oracle round-trip `rState2Rstate q_b o` does not change its output distribution, provided the adversary asks at most `q_b` queries. With it, the downstream lemmas `obsEq_distinguishing`, `obsEq_distinguishing_adv`, and `obsEq_distinguishing_ub` are now fully proven too.

To prove (2) I added a new, self-contained, Mathlib-only file `Hopscotch/ComputationalIndistinguishability/PMFDisintegration.lean` containing the probability-theoretic core (all fully proven):
- `PMF.condOn` (defaulted conditioning) and the disintegration law `PMF.map_bind_condOn_fiber`;
- conditioning algebra: `PMF.condOn_eq_self`, `PMF.condOn_map`, `PMF.condOn_condOn`, `PMF.condOn_bind_of_upstream`, `PMF.condOn_congr_on_support`, `PMF.map_congr_on_support`, `PMF.bindCongrOnSupport`;
- a generic adaptive-computation model `GTree` with evaluator `geval`/`GTree.depth`, and the key induction `geval_reconstruct`: if a reconstructed oracle and a conditional-state map satisfy a one-step compatibility square (within budget, on reachable states), then any bounded-depth computation has the same output distribution against the original kernel and against the reconstruction.

In `ObsEqComp.lean` I then built the bridge from the concrete VCVio constructions to this generic lemma: `toGTree` (free-monad → `GTree`), the `geval`/`simulateQ` correspondence, depth agreement, the conditional-state `condState`, the reconstructed-oracle query equation `rState2Rstate_queries_eq`, the joint-distribution append lemma, a reachability predicate with its preservation (`reachT`, `Hstep_reach`), and the central conditional-probability identities (`condState_bind_query_eq`, `behavioral_process_eq`, `hstep`) which discharge the compatibility square via the disintegration engine.

Note on tooling: the automated prover could not load this project directly because a VCVio dependency (`ToMathlib.PFunctor.*`) is compiled with Lean's experimental `module` system, whose split data files its loader could not find (reported separately). I worked around this by isolating all reusable, dependency-free probability lemmas into the new Mathlib-only file (where automation does work) and assembling the VCVio-typed remainder by hand.

Verification: `lake build` completes successfully for the whole project; `Hopscotch.ComputationalIndistinguishability.ObsEqComp` and `...PMFDisintegration` contain no `sorry`/`axiom`/`@[implemented_by]`; and `#print axioms` for `rState2Rstate_non_dist`, `behavioral_eq_from_obsEq`, and `obsEq_distinguishing_ub` lists only `[propext, Classical.choice, Quot.sound]`.
# Summary of changes for run correct-until-bad-and-soundness
Filled the two remaining proof holes.

1. `correctUntilBad_approxEq` (`Hopscotch/ApproxEq/CorrectUntilBad.lean`) — the fundamental lemma of
game playing. Proof-internal helpers (all `private`, in namespace `CorrectUntilBad`): splitting a
`tsum` into its bad and good part, equality of the bad mass of two kernels agreeing outside the bad
set (`badmass_eq`, `badexp_eq`), the one-step expectation estimate `exp_le_of_agree`, the averaging
lemma `exp_le_of_uniform`, budget arithmetic in `ℕ∞` (`enat_pred`), a local restatement of the
`simulateQ`/`FreeM.roll` unfolding, and the main induction `run_le` over the adversary's
free-monad computation (query nodes consume one unit of budget, sampling nodes do not). The
`ENNReal` estimates in both directions are then averaged over the initial state distributions and
converted to the real-valued advantage. Only the one-sided bad-event bound for `queries₁` is used.

2. `computationalSoundness_internal` (`Hopscotch/ComputationalIndistinguishability/Soundness.lean`) —
by induction on the `IndistinguishableI` derivation, preserving the residual formulation
`|advantage − assumption contribution| ≤ statistical error`. New helper lemmas:
`advBoundQWithError_of_advBoundQ`, `assumptionJoiner_sum`, `transitive_step_proof_error`,
`long_step_error_induction`, `ascToReal_identity`, `ascToReal_rcompose_map`.

Verification: `lake build` succeeds for the whole project, no `sorry` remains, and
`#print axioms` for `correctUntilBad_approxEq`, `computationalSoundness_internal` and
`computationalSoundness` lists only `[propext, Classical.choice, Quot.sound]`.
