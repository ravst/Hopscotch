import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ComputationalIndistinguishibility.BehavioralOracle
import GameHoppingInLean.ComputationalIndistinguishibility.PMFDisintegration
import GameHoppingInLean.ComputationalIndistinguishibility.ObservationEquivalenceReach
import GameHoppingInLean.ObservationalEq.Defs
import GameHoppingInLean.Tactic.SimpAttrLemmas

/- # Prove that Observation Equivalence (ObsEq) imply that no adversary distinguishes (called AdvEq here)
It is easy to prove that correctAbstractin lead both to ObsEq and AdvEq.
But proving that ObsEq imply AdvEq is challenging. We provie this here.
The harndess comes partialy from the fact that adversary can run for unbounded time --  its running time could be proportial to anser to first query. On the orher hand, ObsEq states that for any fixed length of interaction we have equal ditribuitions. To lift it to total prove, we need to consider conditinal probabilites related to each new transition. This conditioning make the prove rather hard.

To do that, we define behavioral oracle: an definition of oracle without internla state,
only defines via input output relation. This definine them in BehavioralOracle.lean.
Then we can convert back to statefull. This roundtrip is called rState2Rstate (see BehavioralOracle.lean)
Then we prove three facts (a : OracleImpl O):
1) ObsEq A B imply to BehavioralOracle.into A = BehavioralOracle.into B . That is obvious from definition.
2) There is an form of abstraction between rState2Rstate A -> A.
3) This form of abstraction imply AdvEq.
We use abstration defined as abstraction_with_levels_and_reach in ObservationalEquivalenceReach.
It allow for transition function to be defined only on reachable state. Additionally it tracks number of queries made. Alternativly, the proof can be carried using correctAbstractionBindBound. In fact, exactly that is done in AbstractionComplete.lean. We keep this form of abstraction in the proof of ObsEqComp, as such proof is nicer, shorter and simpler.

Most of this file is the proof of 2).
This part was done by Aristotele (who generalized form of abstraction need here, proved 2 and 3, including generation of lemmas from PMFDisintegration). Impressive!
-/


lemma behavioral_eq_from_obsEq (ro₁ ro₂ : OracleImpl O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b) :
  BehavioralOracle.into q_b ro₁ = BehavioralOracle.into q_b ro₂ := by
  unfold BehavioralOracle.into
  congr 1
  funext ql H
  have : runQueriesOnlyOut ro₁ ql.reverse = runQueriesOnlyOut ro₂ ql.reverse := by
    apply obs_eq
    rw [List.length_reverse]
    exact H
  rw [this]


/-- The conditional distribution of `o`'s internal state given that the observable transcript so
far equals `τ` (recorded newest-first).  We replay the chronological queries `(τ.reverse).map input`
and condition the resulting joint on having produced the transcript `τ.reverse`. -/
noncomputable def condState {I : Type} {O : OracleSpec I} (o : OracleImpl O)
    (τ : List (QueryWithResult O)) : PMF o.stateType :=
  ((runQueries2 o ((τ.reverse).map QueryWithResult.input)).condOn {p | p.1 = τ.reverse}).map Prod.snd

/-- For the empty transcript the conditional state is just the initial-state distribution. -/
lemma condState_nil {I : Type} {O : OracleSpec I} (o : OracleImpl O) :
    condState o [] = o.initialState := by
  unfold condState
  simp only [List.reverse_nil, List.map_nil]
  have hrun : runQueries2 o [] = o.initialState.map (fun s => (([] : List (QueryWithResult O)), s)) := by
    unfold runQueries2
    rw [show runQueries2Aux o.queries [] = (fun s => PMF.pure (([] : List (QueryWithResult O)), s)) from rfl]
    rw [PMF.map]; rfl
  rw [PMF.condOn_eq_self _ _ ?hsub]
  case hsub =>
    intro a ha
    rw [hrun, PMF.mem_support_map_iff] at ha
    obtain ⟨b, _, hb⟩ := ha
    simp only [Set.mem_setOf_eq, ← hb]
  · rw [hrun, PMF.map_comp]
    exact PMF.map_id o.initialState

/-- The reconstructed oracle, run on the newest-first transcript `τ` (within budget), draws the
next answer from the behavioural oracle and pushes the new query/answer onto the transcript. -/
theorem rState2Rstate_queries_eq {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat)
    (i : I) (τ : List (QueryWithResult O)) (H : (τ.length : ℕ∞) ≤ q_b) :
    ((rState2Rstate q_b o).queries i) τ
      = (((behavioralOracle1to2 (BehavioralOracle.into q_b o)).process τ H i).map
          (fun out => (out, (⟨i, out⟩ :: τ : List (QueryWithResult O))))) := by
  change StateT.run ((rState2Rstate q_b o).queries i) τ = _
  unfold rState2Rstate behavioralOracle1toRstate behavioralOracle2toRstate
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
    LawfulMonad.pure_bind, dif_pos H, bind_assoc, RState.run_liftM]
  rw [PMF.map]
  change (((behavioralOracle1to2 (BehavioralOracle.into q_b o)).process τ H i).bind
      (PMF.pure ∘ fun a => (a, τ))).bind
      (fun p => PMF.pure (p.1, (⟨i, p.1⟩ :: τ : List (QueryWithResult O)))) = _
  rw [PMF.bind_bind]
  congr 1; funext a; simp [Function.comp, PMF.pure_bind]

/-- The reconstructed oracle extends the transcript by exactly one entry (within budget). -/
lemma condState_lvl {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) :
    ∀ (i : I) (τ : List (QueryWithResult O)), (τ.length : ℕ∞) + 1 ≤ q_b →
      ∀ p ∈ (((rState2Rstate q_b o).queries i) τ).support, (p.2.length : ℕ∞) = (τ.length : ℕ∞) + 1 := by
  intro i τ hb p hp
  have H : (τ.length : ℕ∞) ≤ q_b := le_trans le_self_add hb
  rw [rState2Rstate_queries_eq o q_b i τ H, PMF.mem_support_map_iff] at hp
  obtain ⟨out, _, hout⟩ := hp
  rw [← hout]
  simp

/-- Running `[i]` extends the recorded transcript by the single entry `⟨i, out⟩`. -/
theorem runQueries2Aux_single {I : Type} {O : OracleSpec I} (o : OracleImpl O) (i : I)
    (s : o.stateType) :
    runQueries2Aux o.queries [i] s
      = ((o.queries i) s).map (fun q => (([(⟨i, q.1⟩ : QueryWithResult O)]), q.2)) := by
  change (StateT.run (o.queries i) s).bind
      (fun x => (runQueries2Aux o.queries [] x.2).bind
        (fun y => PMF.pure ((⟨i, x.1⟩ : QueryWithResult O) :: y.1, y.2))) = _
  rw [PMF.map]
  congr 1; funext x
  rw [show runQueries2Aux o.queries ([] : List I) x.2
        = PMF.pure (([] : List (QueryWithResult O)), x.2) from rfl, PMF.pure_bind]
  rfl

/-- Joint distribution after `qs ++ [i]`: run `qs`, then run the extra query `i` and append its
recorded entry. -/
theorem runQueries2_append_single {I : Type} {O : OracleSpec I} (o : OracleImpl O) (qs : List I)
    (i : I) :
    runQueries2 o (qs ++ [i])
      = (runQueries2 o qs).bind
          (fun p => ((o.queries i) p.2).map (fun q => (p.1 ++ [(⟨i, q.1⟩ : QueryWithResult O)], q.2))) := by
  unfold runQueries2
  rw [show (o.initialState >>= runQueries2Aux o.queries (qs ++ [i]))
        = o.initialState.bind (runQueries2Aux o.queries (qs ++ [i])) from rfl,
      show (o.initialState >>= runQueries2Aux o.queries qs)
        = o.initialState.bind (runQueries2Aux o.queries qs) from rfl,
      PMF.bind_bind]
  congr 1; funext s0
  rw [runQueries2Aux_append]
  congr 1; funext p
  rw [runQueries2Aux_single, PMF.map_comp]
  rfl

/-- Unfolding `condState` for a transcript extended by one entry. -/
lemma condState_ext {I : Type} {O : OracleSpec I} (o : OracleImpl O) (i : I) (out : O.Range i)
    (τ : List (QueryWithResult O)) :
    condState o (⟨i, out⟩ :: τ)
      = ((runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i])).condOn
          {p | p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)]}).map Prod.snd := by
  unfold condState
  congr 2
  · simp [List.reverse_cons, List.map_append]
  · simp [List.reverse_cons]

/-- **BRIDGE.** Querying `i` from the conditional state of `τ` equals conditioning the joint after
`qs ++ [i]` on the recorded prefix `τ.reverse`, then reading off the last answer and the state. -/
lemma condState_bind_query_eq {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) (i : I)
    (τ : List (QueryWithResult O)) :
    (condState o τ).bind (fun s => (o.queries i) s)
      = ((runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i])).condOn
          {p | p.1.dropLast = τ.reverse}).map
          (fun p => (extractHead i (Classical.choice ((BehavioralOracle.into q_b o).good_spec i)) p.1.reverse, p.2)) := by
  unfold condState
  rw [runQueries2_append_single o ((τ.reverse).map QueryWithResult.input) i]
  rw [PMF.condOn_bind_of_upstream (runQueries2 o ((τ.reverse).map QueryWithResult.input))
        (fun p => ((o.queries i) p.2).map (fun r => (p.1 ++ [(⟨i, r.1⟩ : QueryWithResult O)], r.2)))
        {p | p.1.dropLast = τ.reverse} {p | p.1 = τ.reverse} ?compat]
  · rw [PMF.map_bind, PMF.bind_map]
    congr 1
    funext p
    simp only [Function.comp]
    rw [PMF.map_comp]
    conv_lhs => rw [← PMF.map_id ((o.queries i) p.2)]
    congr 1
    funext q
    simp [Function.comp, List.reverse_append, extractHead]
  case compat =>
    intro p b hb
    rw [PMF.mem_support_map_iff] at hb
    obtain ⟨q, _, hq⟩ := hb
    simp only [Set.mem_setOf_eq, ← hq, List.dropLast_concat]

/-- **LemmaB2.** The behavioural oracle's answer distribution equals the conditional last-answer
distribution of the joint after `qs ++ [i]` given the recorded prefix `τ.reverse`. -/
lemma behavioral_process_eq {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) (i : I)
    (τ : List (QueryWithResult O)) (H : (τ.length : ℕ∞) ≤ q_b) (hb : (τ.length : ℕ∞) + 1 ≤ q_b)
    (hex : ∃ a ∈ {l : List (QueryWithResult O) | l.tail = τ},
        a ∈ ((runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i])).map (fun p => p.1.reverse)).support) :
    (behavioralOracle1to2 (BehavioralOracle.into q_b o)).process τ H i
      = ((runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i])).condOn
          {p | p.1.dropLast = τ.reverse}).map
          (fun p => extractHead i (Classical.choice ((BehavioralOracle.into q_b o).good_spec i)) p.1.reverse) := by
  set dflt := Classical.choice ((BehavioralOracle.into q_b o).good_spec i) with hdflt
  set J' := runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i]) with hJ'
  rw [show (behavioralOracle1to2 (BehavioralOracle.into q_b o)).process τ H i
        = condMap ((BehavioralOracle.into q_b o).process (i :: τ.map QueryWithResult.input) (by simpa using hb))
            {l | l.tail = τ} (extractHead i dflt) dflt from by
        simp only [behavioralOracle1to2]
        rw [dif_pos (show ((τ.length + 1 : ℕ) : ℕ∞) ≤ q_b by exact_mod_cast hb)]]
  have hD : (BehavioralOracle.into q_b o).process (i :: τ.map QueryWithResult.input) (by simpa using hb)
      = J'.map (fun p => p.1.reverse) := by
    change (runQueriesOnlyOut o (i :: τ.map QueryWithResult.input).reverse).map List.reverse = _
    rw [runQueriesOnlyOut, PMF.map_comp]; congr 1; simp [List.reverse_cons, List.map_reverse, hJ']
  rw [hD, condMap, dif_pos hex]
  rw [show ((J'.map (fun p => p.1.reverse)).filter {l | l.tail = τ} hex)
        = (J'.map (fun p => p.1.reverse)).condOn {l | l.tail = τ} from by
      unfold PMF.condOn; rw [dif_pos hex]]
  rw [PMF.condOn_map]
  have hset : (fun p : List (QueryWithResult O) × o.stateType => p.1.reverse) ⁻¹' {l | l.tail = τ}
      = {p | p.1.dropLast = τ.reverse} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, List.tail_reverse]
    constructor
    · intro h; rw [← h, List.reverse_reverse]
    · intro h; rw [h, List.reverse_reverse]
  rw [hset, PMF.map_comp]
  rfl

/-- A transcript `τ` is *reachable* when its recorded prefix `τ.reverse` has positive probability of
being produced by replaying the chronological queries `(τ.reverse).map input`. -/
def reachT {I : Type} {O : OracleSpec I} (o : OracleImpl O) (τ : List (QueryWithResult O)) : Prop :=
  ∃ p ∈ (runQueries2 o ((τ.reverse).map QueryWithResult.input)).support, p.1 = τ.reverse

def reachT2 {I : Type} {O : OracleSpec I} (o : OracleImpl O) (τ : List (QueryWithResult O)) : Prop :=
  τ.reverse ∈ (runQueriesOnlyOut o ((τ.reverse).map QueryWithResult.input)).support

lemma reachT_eq {I : Type} {O : OracleSpec I} (o : OracleImpl O) (τ : List (QueryWithResult O)) :
  reachT o τ = reachT2 o τ := by
  apply propext
  unfold reachT reachT2 runQueriesOnlyOut
  rw [PMF.mem_support_map_iff]

/-- The empty transcript is reachable. -/
lemma reachT_nil {I : Type} {O : OracleSpec I} (o : OracleImpl O) : reachT o [] := by
  unfold reachT
  simp only [List.reverse_nil, List.map_nil]
  obtain ⟨s, hs⟩ := PMF.support_nonempty o.initialState
  refine ⟨([], s), ?_, rfl⟩
  have : runQueries2 o [] = o.initialState.map (fun s => (([] : List (QueryWithResult O)), s)) := by
    unfold runQueries2
    rw [show runQueries2Aux o.queries [] = (fun s => PMF.pure (([] : List (QueryWithResult O)), s)) from rfl]
    rw [PMF.map]; rfl
  rw [this, PMF.mem_support_map_iff]
  exact ⟨s, hs, rfl⟩

/-- Transcripts produced by `runQueries2 o L` always have inputs `L`. -/
lemma runQueries2_input_eq {I : Type} {O : OracleSpec I} (o : OracleImpl O) (L : List I)
    (p : List (QueryWithResult O) × o.stateType) (hp : p ∈ (runQueries2 o L).support) :
    p.1.map QueryWithResult.input = L := by
  have hkey : (runQueries2 o L).map (fun p => p.1.map QueryWithResult.input) = PMF.pure L := by
    have := runQueriesOnlyOut_map_input o L
    rw [runQueriesOnlyOut, PMF.map_comp] at this
    convert this using 2
  have hmem : (fun p : List (QueryWithResult O) × o.stateType => p.1.map QueryWithResult.input) p
      ∈ ((runQueries2 o L).map (fun p => p.1.map QueryWithResult.input)).support := by
    rw [PMF.mem_support_map_iff]; exact ⟨p, hp, rfl⟩
  rw [hkey] at hmem
  simpa using hmem

/-- From reachability of `τ`, the behavioural oracle's conditioning event is non-empty. -/
lemma reach_hex {I : Type} {O : OracleSpec I} (o : OracleImpl O) (i : I)
    (τ : List (QueryWithResult O))
    (hreach : reachT o τ) :
    ∃ a ∈ {l : List (QueryWithResult O) | l.tail = τ},
      a ∈ ((runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i])).map (fun p => p.1.reverse)).support := by
  obtain ⟨p0, hp0, hp0eq⟩ := hreach
  obtain ⟨q0, hq0⟩ := PMF.support_nonempty ((o.queries i) p0.2)
  refine ⟨(⟨i, q0.1⟩ : QueryWithResult O) :: τ, by simp [Set.mem_setOf_eq], ?_⟩
  rw [PMF.mem_support_map_iff]
  refine ⟨(p0.1 ++ [⟨i, q0.1⟩], q0.2), ?_, ?_⟩
  · rw [runQueries2_append_single, PMF.mem_support_bind_iff]
    exact ⟨p0, hp0, by rw [PMF.mem_support_map_iff]; exact ⟨q0, hq0, rfl⟩⟩
  · simp [List.reverse_append, hp0eq]

/-- One-step compatibility: querying `i` from the conditional state `condState o τ` agrees with
taking the reconstructed step `(rState2Rstate q_b o).queries i τ` and then re-expanding the
conditional state of the new transcript. -/
lemma hstep {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) :
    ∀ (i : I) (τ : List (QueryWithResult O)), reachT o τ → (τ.length : ℕ∞) + 1 ≤ q_b →
      (condState o τ).bind (fun s => (o.queries i) s) =
        (((rState2Rstate q_b o).queries i) τ).bind
          (fun p => (condState o p.2).map (fun s' => (p.1, s'))) := by
  intro i τ hreach hb
  have H : (τ.length : ℕ∞) ≤ q_b := le_trans le_self_add hb
  have hex := reach_hex o i τ hreach
  set dflt := Classical.choice ((BehavioralOracle.into q_b o).good_spec i) with hdflt
  set J' := runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i]) with hJ'
  set S1 : Set (List (QueryWithResult O) × o.stateType) := {p | p.1.dropLast = τ.reverse} with hS1
  set g : List (QueryWithResult O) × o.stateType → O.Range i := fun p => extractHead i dflt p.1.reverse with hg
  set F : List (QueryWithResult O) × o.stateType → O.Range i × o.stateType := fun p => (g p, p.2) with hF
  have hS1ex : ∃ a ∈ S1, a ∈ J'.support := by
    obtain ⟨a, ha_tail, ha_mem⟩ := hex
    obtain ⟨pa, hpa, hpaeq⟩ := (PMF.mem_support_map_iff _ _ _).mp ha_mem
    refine ⟨pa, ?_, hpa⟩
    have : (pa.1.reverse).tail = τ := by rw [hpaeq]; exact ha_tail
    rw [List.tail_reverse] at this
    change pa.1.dropLast = τ.reverse
    rw [← this, List.reverse_reverse]
  have hset_eq : ∀ (out : O.Range i) (p : List (QueryWithResult O) × o.stateType), p ∈ J'.support →
      ((p.1.dropLast = τ.reverse ∧ extractHead i dflt p.1.reverse = out)
        ↔ p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)]) := by
    intro out p hp
    have hin := runQueries2_input_eq o _ p hp
    have hne : p.1 ≠ [] := by intro h; rw [h] at hin; simp at hin
    obtain ⟨last, rest, hrev⟩ : ∃ last rest, p.1.reverse = last :: rest := by
      cases hh : p.1.reverse with
      | nil => exact absurd (by have := congrArg List.reverse hh; simpa using this) hne
      | cons a l => exact ⟨a, l, rfl⟩
    have hp1 : p.1 = rest.reverse ++ [last] := by
      have := congrArg List.reverse hrev; simpa using this
    obtain ⟨linp, lout⟩ := last
    have hlast_input : linp = i := by
      rw [hp1] at hin
      simp only [List.map_append, List.map_cons, List.map_nil] at hin
      simpa using List.append_inj_right' hin (by simp)
    subst hlast_input
    rw [hp1]
    simp only [extractHead, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.dropLast_concat, dite_true]
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro h
      obtain ⟨hl, hr⟩ := List.append_inj' h (by simp)
      refine ⟨hl, ?_⟩
      simp only [List.cons.injEq, QueryWithResult.mk.injEq, true_and] at hr
      exact eq_of_heq hr.1
  rw [condState_bind_query_eq o q_b i τ, rState2Rstate_queries_eq o q_b i τ H, PMF.bind_map,
      behavioral_process_eq o q_b i τ H hb hex]
  conv_lhs => rw [← PMF.map_bind_condOn_fiber ((J'.condOn S1).map F) Prod.fst]
  rw [show ((J'.condOn S1).map F).map Prod.fst = (J'.condOn S1).map g from by rw [PMF.map_comp]; rfl]
  apply PMF.bindCongrOnSupport
  intro out hout
  obtain ⟨pw, hpw_mem0, hpw_g⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have hMfilter : J'.condOn S1 = J'.filter S1 hS1ex := by unfold PMF.condOn; rw [dif_pos hS1ex]
  rw [hMfilter] at hpw_mem0
  rw [PMF.mem_support_filter_iff] at hpw_mem0
  rw [PMF.condOn_map]
  rw [show ((J'.condOn S1).condOn (F ⁻¹' {q | q.1 = out})) = J'.condOn (S1 ∩ (F ⁻¹' {q | q.1 = out})) from by
      apply PMF.condOn_condOn
      exact ⟨pw, hpw_mem0.1, hpw_g, hpw_mem0.2⟩]
  rw [PMF.condOn_congr_on_support J' (S1 ∩ (F ⁻¹' {q | q.1 = out}))
      {p | p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)]} (by
        intro p hp
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hS1, hF, hg]
        exact hset_eq out p hp)]
  have hFeq : ∀ p ∈ (J'.condOn {p | p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)]}).support,
      F p = (out, p.2) := by
    intro p hp
    have hex2 : ∃ a ∈ {p | p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)]}, a ∈ J'.support :=
      ⟨pw, (hset_eq out pw hpw_mem0.2).mp ⟨hpw_mem0.1, hpw_g⟩, hpw_mem0.2⟩
    rw [show J'.condOn {p | p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)]} = J'.filter _ hex2 from by
        unfold PMF.condOn; rw [dif_pos hex2]] at hp
    rw [PMF.mem_support_filter_iff] at hp
    have hp1 : p.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)] := hp.1
    rw [hF, hg]
    simp only [hp1, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, extractHead, dite_true]
  rw [PMF.map_congr_on_support _ hFeq]
  simp only [Function.comp]
  rw [condState_ext, PMF.map_comp]
  rfl

/-- Combined level/reachability preservation for the reconstructed oracle. -/
lemma Hstep_reach {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) :
    ∀ (i : I) (τ : List (QueryWithResult O)), reachT o τ → (τ.length : ℕ∞) + 1 ≤ q_b →
      ∀ p ∈ (((rState2Rstate q_b o).queries i) τ).support,
        (p.2.length : ℕ∞) = (τ.length : ℕ∞) + 1 ∧ reachT o p.2 := by
  intro i τ hreach hb p hp
  have H : (τ.length : ℕ∞) ≤ q_b := le_trans le_self_add hb
  refine ⟨condState_lvl o q_b i τ hb p hp, ?_⟩
  have hex := reach_hex o i τ hreach
  set dflt := Classical.choice ((BehavioralOracle.into q_b o).good_spec i) with hdflt
  set J' := runQueries2 o ((τ.reverse).map QueryWithResult.input ++ [i]) with hJ'
  set S1 : Set (List (QueryWithResult O) × o.stateType) := {p | p.1.dropLast = τ.reverse} with hS1
  have hS1ex : ∃ a ∈ S1, a ∈ J'.support := by
    obtain ⟨a, ha_tail, ha_mem⟩ := hex
    obtain ⟨pa, hpa, hpaeq⟩ := (PMF.mem_support_map_iff _ _ _).mp ha_mem
    refine ⟨pa, ?_, hpa⟩
    have : (pa.1.reverse).tail = τ := by rw [hpaeq]; exact ha_tail
    rw [List.tail_reverse] at this
    change pa.1.dropLast = τ.reverse
    rw [← this, List.reverse_reverse]
  have hset_eq : ∀ (out : O.Range i) (pp : List (QueryWithResult O) × o.stateType), pp ∈ J'.support →
      (pp.1.dropLast = τ.reverse ∧ extractHead i dflt pp.1.reverse = out)
        → pp.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)] := by
    intro out pp hpp hcond
    have hin := runQueries2_input_eq o _ pp hpp
    have hne : pp.1 ≠ [] := by intro h; rw [h] at hin; simp at hin
    obtain ⟨last, rest, hrev⟩ : ∃ last rest, pp.1.reverse = last :: rest := by
      cases hh : pp.1.reverse with
      | nil => exact absurd (by have := congrArg List.reverse hh; simpa using this) hne
      | cons a l => exact ⟨a, l, rfl⟩
    have hp1 : pp.1 = rest.reverse ++ [last] := by
      have := congrArg List.reverse hrev; simpa using this
    obtain ⟨linp, lout⟩ := last
    have hlast_input : linp = i := by
      rw [hp1] at hin
      simp only [List.map_append, List.map_cons, List.map_nil] at hin
      simpa using List.append_inj_right' hin (by simp)
    subst hlast_input
    rw [hp1] at hcond ⊢
    simp only [extractHead, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.dropLast_concat, dite_true] at hcond
    rw [hcond.1, hcond.2]
  rw [rState2Rstate_queries_eq o q_b i τ H] at hp
  rw [PMF.mem_support_map_iff] at hp
  obtain ⟨out, hout, hpeq⟩ := hp
  rw [← hpeq]
  rw [behavioral_process_eq o q_b i τ H hb hex] at hout
  obtain ⟨pw, hpw_mem0, hpw_g⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have hMfilter : J'.condOn S1 = J'.filter S1 hS1ex := by unfold PMF.condOn; rw [dif_pos hS1ex]
  rw [hMfilter] at hpw_mem0
  rw [PMF.mem_support_filter_iff] at hpw_mem0
  have hpw1 : pw.1 = τ.reverse ++ [(⟨i, out⟩ : QueryWithResult O)] :=
    hset_eq out pw hpw_mem0.2 ⟨hpw_mem0.1, hpw_g⟩
  change reachT o (⟨i, out⟩ :: τ)
  unfold reachT
  refine ⟨pw, ?_, ?_⟩
  · have heq2 : ((⟨i, out⟩ :: τ : List (QueryWithResult O)).reverse).map QueryWithResult.input
        = (τ.reverse).map QueryWithResult.input ++ [i] := by
      simp [List.reverse_cons, List.map_append]
    rw [heq2]; exact hpw_mem0.2
  · rw [hpw1]; simp [List.reverse_cons]

-- /-- `runDinstinguisher` expressed through the generic `geval`. -/
-- lemma runDinstinguisher_geval {I : Type} {O : OracleSpec I} (o : OracleImpl O) (dist : adversaryT O) :
--     runDinstinguisher dist o =
--       o.initialState.bind (fun s => (geval (fun i s => (o.queries i) s) (toGTree dist) s).map Prod.fst) := by
--   simp only [runDinstinguisher]
--   congr 1; funext init
--   rw [← geval_simulate_corr o dist init]
--   rfl

/-- `runDinstinguisher` expressed through the generic `geval`. -/
lemma runDinstinguisher_unfold {I : Type} {O : OracleSpec I} (o : OracleImpl O) (dist : adversaryT O) :
    runDinstinguisher dist o =
      o.initialState.bind (fun s => (simulateQ (addPMFtoImpl (o.queries)) (dist) s).map Prod.fst) := by
  simp only [runDinstinguisher]
  congr 1





/- This lemma states that passing an adversary through the behavioural-oracle round trip
`rState2Rstate` does not change its output distribution, provided the adversary asks at most `q_b`
queries.  It is reduced (via the generic `geval_reconstruct`) to the conditional-probability facts
`condState_nil`, `condState_lvl` and `hstep`. -/
lemma rState2Rstate_non_dist {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) (dist : adversaryT O)
  (Hdist : FreeM.depth dist <= q_b) :
  runDinstinguisher dist o = runDinstinguisher dist (rState2Rstate q_b o) := by
  have key2 := abstraction_with_levels_and_reach q_b (fun i s => (o.queries i) s)
      (fun i τ => ((rState2Rstate q_b o).queries i) τ) (condState o) (fun τ => (τ.length : ℕ∞))
      (reachT o) (Hstep_reach o q_b) (hstep o q_b) (dist) [] (reachT_nil o)
      (by simpa [] using Hdist)
  rw [condState_nil] at key2
  rw [runDinstinguisher_unfold o dist]
  rw [runDinstinguisher_unfold (rState2Rstate q_b o) dist]
  rw [key2]
  rw [show (rState2Rstate q_b o).initialState = PMF.pure [] from rfl, PMF.pure_bind]




lemma obsEq_distinquishing (ro₁ ro₂ : OracleImpl O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b)
  (dist : adversaryT O) (Hdist : FreeM.depth dist <= q_b) :
    runDinstinguisher dist ro₁ = runDinstinguisher dist ro₂ :=
by
  have H1 := rState2Rstate_non_dist ro₁ q_b dist Hdist
  have H2 := rState2Rstate_non_dist ro₂ q_b dist Hdist
  have H3p : BehavioralOracle.into q_b ro₁ = BehavioralOracle.into q_b ro₂ := behavioral_eq_from_obsEq ro₁ ro₂ q_b obs_eq
  have H3 : runDinstinguisher dist (rState2Rstate q_b ro₁) = runDinstinguisher dist (rState2Rstate q_b ro₂)
  := by
    simp [rState2Rstate]
    rw [H3p]
  rw [H1, H2, H3]

lemma obsEq_distinquishing_adv (ro₁ ro₂ : OracleImpl O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b)
  (dist : adversaryT O) (Hdist : FreeM.depth dist <= q_b) :
    advantage dist ro₁ ro₂ = 0 :=
by
  simp [advantage, pdistancePMF]
  rw [obsEq_distinquishing ro₁ ro₂ q_b]
  · simp []
  · assumption
  · assumption


lemma adv_from_bobseq (ro₁ ro₂ : OracleImpl O)
  (dist1 dist2 : adversaryT O)
  (Hd : forall impl, runDinstinguisher dist1 impl = runDinstinguisher dist2 impl)
   :
    advantage dist1 ro₁ ro₂ = advantage dist2 ro₁ ro₂ :=
by
  simp [advantage, pdistancePMF]
  rw [Hd]
  rw [Hd]

lemma obsEq_distinquishing_ub (ro₁ ro₂ : OracleImpl O) (obs_eq : ObsEq ro₁ ro₂)
  (dist : adversaryT O) :
    runDinstinguisher dist ro₁ = runDinstinguisher dist ro₂ :=
by
  apply obsEq_distinquishing (q_b := none)
  · exact (ObsEq_from_none ro₁ ro₂).mp obs_eq
  · exact le_of_sup_eq' rfl


lemma ascToRealFromObsEq {I : Type} {O : OracleSpec I}
  {distinguisher : OracleComp (withPMFSpec O) Bool}
  {assumption : SingleAssumption}
  (x1 x2 : ℕ × (OracleReduction assumption.O O))
  (H2 : forall impl, ObsEq (x1.2.apply impl) (x2.2.apply impl))
  (H1 : x1.1 = x2.1)
  :
  ascToReal distinguisher assumption x1 = ascToReal distinguisher assumption x2 :=
by
  simp [ascToReal]
  rw [H1]
  congr 1
  simp [advantage]
  repeat rw [<-goodDoubleAction]
  congr 1
  · apply obsEq_distinquishing_ub
    apply H2
  · apply obsEq_distinquishing_ub
    apply H2


-- lemma correctAbstraction2ind_inner {I : Type _} {O : OracleSpec I} {stateType₁ stateType₂ : Type _} (dist : OracleComp O Bool)
--   (ro₁ : QueryImpl O (RState stateType₁))
--   (ro₂ : QueryImpl O (RState stateType₂))
--   (f : stateType₁ → PMF stateType₂)
--   (Habs : ∀ (query : O.Domain),
--       bindOutputState f (ro₁ query) =
--       bindInputState f (ro₂ query)) :
--   forall (init : stateType₁),
--   pdistancePMF
--     (runDinstinguisher_inner dist ro₁ init)
--     (do
--       let init_v <- f init
--       runDinstinguisher_inner dist ro₂ init_v)= 0
--   :=  by
--   induction dist
--   case pure v =>
--     simp [advantage, runDinstinguisher_inner, simulateQ]
--     simp [pdistancePMF, distSelf]
--   case roll β cont Hind =>
--     intro init
--     simp [runDinstinguisher_inner_bind]
--     have X := congr_fun (Habs β) init
--     simp [bindOutputState, bindInputState] at X
--     simp [StateT.run] at X
--     rw [<-PMF.bind_bind]
--     rw [<-X]
--     simp [bindSecond]
--     apply obseEq_from_2_steps
--     intro a
--     apply Hind a.1
-- lemma correctAbstractionAfterwithPMFSpec {I : Type _} {stateType₁ stateType₂ : Type _} {O : OracleSpec I}
--   (ro₁ : QueryImpl O (RState stateType₁)) (ro₂ : QueryImpl O (RState stateType₂))
--   (f : stateType₁ → PMF stateType₂) (Habs : correctAbstractionBindDiag ro₁ ro₂ f)
--   : correctAbstractionBindDiag (addPMFtoImpl ro₁) (addPMFtoImpl ro₂) f := by
--   simp [correctAbstractionBindDiag] at Habs
--   simp [correctAbstractionBindDiag]
--   intro q
--   ext1 z
--   simp [bindOutputState, bindInputState]
--   simp [StateT.run, addPMFtoImpl]
--   cases q
--   case oracle x =>
--     simp []
--     have X := congr_fun (Habs x)
--     simp [bindOutputState, bindInputState, StateT.run] at X
--     apply X
--   case sample y =>
--     simp [bindSecond, Function.comp, PMF.map]
--     conv =>
--       rhs
--       rw [PMF.bind_comm]
--     congr

-- lemma correctAbstraction2ind {I : Type} {O : OracleSpec I} (dist : adversaryT O)
--   (ro₁ ro₂ : OracleImpl O) (f : ro₁.stateType → PMF ro₂.stateType)
--   (Habs : correctAbstractionBind ro₁ ro₂ f) :
--   advantage dist ro₁ ro₂ = 0
-- := by
--     simp [advantage]
--     simp [runDinstinguisher2inner]
--     rw [<-Habs.1]
--     simp []
--     apply obseEq_from_2_steps
--     intro a
--     simp [adversaryT] at dist
--     have X := correctAbstraction2ind_inner (O := withPMFSpec O) dist (addPMFtoImpl ro₁.queries) (addPMFtoImpl ro₂.queries) f
--     apply X
--     -- correct abstraction after addPMFtoIMPL, todo.
--     apply correctAbstractionAfterwithPMFSpec
--     apply Habs.2
