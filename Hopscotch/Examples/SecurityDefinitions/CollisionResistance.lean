import Hopscotch.Indistinguishability.Def

/-!
# Collision resistance as indistinguishability of hash-comparison oracles

Both worlds answer `computeHash m` with `hash m`. The concrete world answers
`compareHashes m₁ m₂` by comparing hashes; the ideal world compares messages.
The hash function is the same public parameter in the two worlds.
-/

namespace Hopscotch.HashComparison

inductive Query (Message : Type) where
  | computeHash (message : Message)
  | compareHashes (message₁ message₂ : Message)

def Spec (Message Digest : Type) : OracleSpec (Query Message)
  | .computeHash _ => Digest
  | .compareHashes _ _ => Bool

variable {Message Digest : Type} [DecidableEq Message] [DecidableEq Digest]

/-- The concrete oracle implements hash equality. -/
noncomputable def concrete (hash : Message → Digest) : OracleImpl (Spec Message Digest) where
  stateType := Unit
  initialState := pure ()
  queries := fun
    | .computeHash m => fun st => pure (hash m, st)
    | .compareHashes m₁ m₂ => fun st => pure (decide (hash m₁ = hash m₂), st)

/-- The ideal oracle retains real hash outputs but implements message equality. -/
noncomputable def ideal (hash : Message → Digest) : OracleImpl (Spec Message Digest) where
  stateType := Unit
  initialState := pure ()
  queries := fun
    | .computeHash m => fun st => pure (hash m, st)
    | .compareHashes m₁ m₂ => fun st => pure (decide (m₁ = m₂), st)

/-- The collision-resistance assumption is an ordinary HOPSCOTCH
indistinguishability premise, usable by the existing reduction rule. -/
abbrev CollisionResistanceI {Idx : Type} (Assumptions : IndAssumptions Idx)
    (q : ENat) (hash : Message → Digest) :=
  IndistinguishableI Assumptions q (concrete hash) (ideal hash)

@[simp] theorem computeHash_same (hash : Message → Digest) (m : Message) (st : Unit) :
    (concrete hash).queries (.computeHash m) st =
      (ideal hash).queries (.computeHash m) st := rfl

/-- Comparison answers differ exactly on a collision of distinct messages. -/
theorem comparison_diff_iff_collision (hash : Message → Digest) (m₁ m₂ : Message) :
    decide (hash m₁ = hash m₂) ≠ decide (m₁ = m₂) ↔
      m₁ ≠ m₂ ∧ hash m₁ = hash m₂ := by
  by_cases hm : m₁ = m₂
  · subst m₂
    simp
  · simp [hm]

end Hopscotch.HashComparison


namespace Hopscotch.HashComparison

/-- Public setup samples one hash key for both worlds. The two operational
queries retain the fixed-key interface above. -/
inductive PublicQuery (Message : Type) where
  | getHashKey
  | computeHash (message : Message)
  | compareHashes (message₁ message₂ : Message)

def PublicSpec (HashKey Message Digest : Type) : OracleSpec (PublicQuery Message)
  | .getHashKey => HashKey
  | .computeHash _ => Digest
  | .compareHashes _ _ => Bool

variable {HashKey Message Digest : Type} [DecidableEq Message] [DecidableEq Digest]

/-- Both worlds sample and reveal the same public key and compute the same
hashes. Only the comparison answer changes. -/
noncomputable def publicOracle (real : Bool) (keyGen : PMF HashKey)
    (hash : HashKey → Message → Digest) : OracleImpl (PublicSpec HashKey Message Digest) where
  stateType := HashKey
  initialState := keyGen
  queries := fun
    | .getHashKey => fun hk => pure (hk, hk)
    | .computeHash m => fun hk => pure (hash hk m, hk)
    | .compareHashes m₁ m₂ => fun hk =>
        pure ((if real then decide (hash hk m₁ = hash hk m₂) else decide (m₁ = m₂)), hk)

noncomputable abbrev publicConcrete (keyGen : PMF HashKey) (hash : HashKey → Message → Digest) :=
  publicOracle true keyGen hash

noncomputable abbrev publicIdeal (keyGen : PMF HashKey) (hash : HashKey → Message → Digest) :=
  publicOracle false keyGen hash

/-- Collision resistance for a sampled public hash key. The key is chosen by
the source oracle once, rather than chosen independently by a reduction. -/
abbrev PublicCollisionResistanceI {Idx : Type} (Assumptions : IndAssumptions Idx)
    (q : ENat) (keyGen : PMF HashKey) (hash : HashKey → Message → Digest) :=
  IndistinguishableI Assumptions q (publicConcrete keyGen hash) (publicIdeal keyGen hash)

end Hopscotch.HashComparison
