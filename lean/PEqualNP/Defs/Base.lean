import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Language

/-!
# The definitions this project stands on

The ruling behind this file is `Library/README.md`. In short:

* Machines, their step function, running time and "computes `f` within a time bound" are
  Mathlib's: `Turing.FinTM2` (a multi-stack machine with finitely many stacks, labels and
  internal states), `Turing.TM2OutputsInTime`, `Turing.TM2ComputableInTime` and
  `Turing.TM2ComputableInPolyTime`.
* Mathlib stops there. It has no decision problems, no P, no NP and no reductions, and its
  notions are data (`Type`), not propositions. Everything below is the thin layer of
  propositions on top.

Inputs are binary strings, `List Bool`, encoded as themselves. A language is a
`Language Bool`, which is `Set (List Bool)`.
-/

namespace PEqualNP.Library

/-- `f` is computed by some machine within `t (length of the encoded input)` steps. -/
def ComputableInTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (t : ℕ → ℕ) : Prop :=
  ∃ c : Turing.TM2ComputableInTime ea eb f, ∀ n, c.time n ≤ t n

/-- `f` is computed by some machine within a polynomial number of steps in the length of the
encoded input. -/
def ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) :
    Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- The set `S` is decided within time `t`: some `f` computed within `t` steps answers `true`
exactly on the members of `S`. The answer is the one-symbol string `[true]` or `[false]`. -/
def DecidableInTime {α αΓ : Type} (ea : α → List αΓ) (S : Set α) (t : ℕ → ℕ) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧ ComputableInTime ea Computability.encodeBool f t

/-- The set `S` is decided in polynomial time. -/
def DecidableInPolyTime {α αΓ : Type} (ea : α → List αΓ) (S : Set α) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧ ComputableInPolyTime ea Computability.encodeBool f

/-- A pair of binary strings, written over the alphabet `Bool ⊕ Bool`: the first string tagged
`Sum.inl`, then the second tagged `Sum.inr`. This is the `encode` of Mathlib's
`Computability.encodingProd` on two copies of `Computability.encodingList Bool`. Its length is
the sum of the two lengths. -/
def encodePair (p : List Bool × List Bool) : List (Bool ⊕ Bool) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

/-- DTIME(t): the languages decided within `t (input length)` steps. -/
def DTIME (t : ℕ → ℕ) : Set (Language Bool) :=
  {L | DecidableInTime (fun x : List Bool => x) L t}

/-- P: the languages decided in polynomial time. -/
def P : Set (Language Bool) :=
  {L | DecidableInPolyTime (fun x : List Bool => x) L}

/-- NP, by verifiers: `L` is in NP when there are a polynomial-time decidable set `R` of pairs
(input, witness) and a polynomial `p` such that `x` is in `L` exactly when some witness `w` of
length at most `p (length of x)` has `(x, w)` in `R`. -/
def NP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R}

/-- Polynomial-time many-one (Karp) reducibility: a polynomial-time computable `f` maps members
of `L₁` to members of `L₂` and non-members to non-members. -/
def PolyTimeReducible (L₁ L₂ : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool,
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/-- `L` is NP-hard: every language in NP reduces to it in polynomial time. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, PolyTimeReducible L' L

/-- `L` is NP-complete: in NP and NP-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

end PEqualNP.Library
