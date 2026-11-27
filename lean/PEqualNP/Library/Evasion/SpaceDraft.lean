import PEqualNP.Defs.Base

/-!
# Space-bounded classes: draft definitions

Draft, NOT under the definitions root; with the red team. The machine model is the one of
`Defs/Base.lean` (Mathlib's `Turing.FinTM2`: finitely many stacks, the input on one of them).

Caveat stated up front: the input sits on a work stack and is consumed by reading, so every
stack counts toward the space and no machine decides in space below the input length. The
classes below are therefore meaningful for bounds `s n ≥ n` only (linear space and above).

Trap found by the red team's read: exact `DSPACE s` is EMPTY if `s n < n` for some `n` or if
`s 0 = 0` (the one-symbol answer on the empty input). So `DSPACE (fun n => n)` is empty. A
statement with exact `DSPACE` as a hypothesis or on its left side needs `s n ≥ n` and `s 0 ≥ 1`,
or should use `DSPACEO`. Sanity lemmas owed before these go under the root: monotone;
`DSPACEO (fun n => n)` nonempty by a named language; `P ⊆ PSPACE`; `DTIME t ⊆ DSPACEO (t + n)`;
`DSPACE s` inside time exponential in `s`.
-/

namespace PEqualNP.Library

/-- The machine of `c` uses space at most `s (length of the encoded input)`: every
configuration reachable from the initial one has every stack of length at most that bound. -/
def UsesSpace {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (c : Turing.TM2Computable ea eb f) (s : ℕ → ℕ) : Prop :=
  ∀ (a : α) (cfg : c.tm.Cfg),
    Relation.ReflTransGen (fun x y => y ∈ c.tm.step x)
      (Turing.initList c.tm (List.map c.inputAlphabet.invFun (ea a))) cfg →
    ∀ k, (cfg.stk k).length ≤ s (ea a).length

/-- `f` is computed by some machine within space `s`. -/
def ComputableInSpace {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (s : ℕ → ℕ) : Prop :=
  ∃ c : Turing.TM2Computable ea eb f, UsesSpace c s

/-- The set `S` is decided within space `s`. -/
def DecidableInSpace {α αΓ : Type} (ea : α → List αΓ) (S : Set α) (s : ℕ → ℕ) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧
    ComputableInSpace ea Computability.encodeBool f s

/-- DSPACE(s): the languages decided within space `s (input length)`. -/
def DSPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | DecidableInSpace (fun x : List Bool => x) L s}

/-- DSPACE up to a constant factor and an additive constant. -/
def DSPACEO (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ K : ℕ, L ∈ DSPACE (fun n => K * s n + K)}

/-- PSPACE: polynomial space. -/
def PSPACE : Set (Language Bool) :=
  {L | ∃ k : ℕ, L ∈ DSPACE (fun n => n ^ k + k)}

end PEqualNP.Library
