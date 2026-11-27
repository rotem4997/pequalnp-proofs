import PEqualNP.Library.Ladner.Defs
import PEqualNP.Defs.Base

/-!
# Plan for the delayed diagonalization (Ladner 1975)

Helper module: the design and the chain of statements, as propositions that elaborate. Nothing
is proved here.

## Route

The padding form of the theorem (the textbook proof by padding an NP-complete language with a
slowly growing exponent) and not the classical form that blows holes in SAT. Reason: the
interpreter `V` of the toolbox only tests one answer bit, so polynomial-time deciders can be
enumerated as codes, but reductions (string outputs) cannot without new machinery. In the
padding form only deciders are enumerated; NP-hardness is refuted by iterating a given
reduction, which shrinks its input, with the bounded iteration combinator.

Let `A = Acq cA q` be NP-complete (`np_code` gives `cA`, `q` for any NP language). Let
`LL = {y | psi y ∈ A ∧ (|psi y| + 2) ^ stage |psi y| ≤ |y|}`. The stage function counts the
`true` symbols of a history string that grows by one symbol per step. The symbol added at step
`n` is `true` when the candidate string number `n` shows, within budget `n`, that decider
number `stage n` differs from `LL`. Membership of short strings in `LL` is read off the history
(for the stage of a shorter length) and decided by exhaustive search for `A`.

## Pure mathematics (`Core.lean`, theorem `core`), from the stated properties of the stage function

* `LL ∈ NP`: `LL` reduces to `A` (send `y` to `psi y` when the padding condition holds, to a
  fixed non-member otherwise).
* `LL ∉ P`: otherwise some decider `i` equals `LL`, the stage never passes `i`, and
  `x ↦ pairB x (un ((|x| + 2) ^ i))` reduces `A` to `LL`, so `A ∈ P` and `P = NP`.
* `LL` not NP-hard: otherwise `A` reduces to `LL` by some `f` with output length at most
  `(|x| + 2) ^ c`. The stage is unbounded (else the last decider equals `LL`, so `LL ∈ P`).
  The map `g x = psi (f x)` when the padding condition holds for `f x` and `psi (f x)` is
  shorter than `x`, and `g x = x` otherwise, preserves membership in `A`, never lengthens, and
  its fixed points in `A` are shorter than a constant. So `x ↦ g^[|x|] x` reduces `A` to a
  bounded exhaustive search, which is in P.

## Machine part

* `PlanSpec`: soundness and liveness of the witness bit (string functions against their
  meaning; no machines).
* `PlanCover`: every language in P is one of the enumerated deciders (the compiler).
* `PlanDecider`: every enumerated decider is in P (the interpreter and the clock).
* `PlanPad`: the padding condition is polynomial-time decidable (the history is computed by
  bounded iteration of `hstep`; the witness bit is built from combinators).
* `PlanBrute`: `A` on strings shorter than a constant is covered by a subset of `A` in P.
-/

namespace PEqualNP.Library.Ladner

open PEqualNP.Library PEqualNP.Library.Universal

/-- The stage moves by the witness bit. -/
def PlanStageSucc (cA : List Bool) (q : Polynomial ℕ) : Prop :=
  ∀ n, stage cA q (n + 1) = stage cA q n + (if Wb cA q (Hs cA q n) = true then 1 else 0)

/-- Soundness of the witness bit: when the stage moves, the current decider is wrong
somewhere. -/
def PlanSound (cA : List Bool) (q : Polynomial ℕ) : Prop :=
  ∀ n, Wb cA q (Hs cA q n) = true →
    ∃ z, ¬ (Dd (stage cA q n) z = true ↔ z ∈ LL cA q)

/-- Liveness of the witness bit: a wrong decider is caught at arbitrarily late steps. -/
def PlanLive (cA : List Bool) (q : Polynomial ℕ) : Prop :=
  ∀ i z, ¬ (Dd i z = true ↔ z ∈ LL cA q) → ∀ n₀, ∃ n, n₀ ≤ n ∧
    (stage cA q n = i → Wb cA q (Hs cA q n) = true)

/-- Every language in P is one of the enumerated deciders. -/
def PlanCover : Prop :=
  ∀ L ∈ P, ∃ i, ∀ z, Dd i z = true ↔ z ∈ L

/-- Every enumerated decider is in P. -/
def PlanDecider : Prop :=
  ∀ i, {z : List Bool | Dd i z = true} ∈ P

/-- The padding condition is in P. -/
def PlanPad (cA : List Bool) (q : Polynomial ℕ) : Prop :=
  {y : List Bool | Gp cA q y} ∈ P

/-- Strings of `A` shorter than a constant are covered by a subset of `A` in P. -/
def PlanBrute (cA : List Bool) (q : Polynomial ℕ) : Prop :=
  ∀ n₁ : ℕ, ∃ B ∈ P, (∀ x ∈ B, x ∈ Acq cA q) ∧ ∀ x ∈ Acq cA q, x.length < n₁ → x ∈ B

/-- The pure-mathematics core: from the properties above, the language works. -/
def PlanCore (cA : List Bool) (q : Polynomial ℕ) : Prop :=
  NPComplete (Acq cA q) → PlanStageSucc cA q → PlanSound cA q → PlanLive cA q → PlanCover →
    PlanDecider → PlanPad cA q → PlanBrute cA q → P ≠ NP →
    LL cA q ∈ NP ∧ LL cA q ∉ P ∧ ¬ NPHard (LL cA q)

/-- An NP-complete verifier language exists. -/
def PlanVerifier : Prop :=
  ∃ (cA : List Bool) (q : Polynomial ℕ), NPComplete (Acq cA q)

end PEqualNP.Library.Ladner
