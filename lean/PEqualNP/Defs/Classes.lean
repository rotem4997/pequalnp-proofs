import PEqualNP.Defs.Base

/-!
# Further uniform classes: coNP, EXP, NEXP

On top of `Defs/Base.lean` (machines, time bounds, `DTIME`, `P`, `NP`), in the same namespace.
Nothing here is in the pinned Mathlib.

* `coNP`: the complements of the NP languages.
* `EXP`: the languages decided within `2 ^ (n ^ k) + k` steps for some `k`.
* `NEXP`, by verifiers, as `NP` is: a polynomial-time decidable relation with witnesses of
  length at most `2 ^ (n ^ k) + k` for some `k`. The verifier is polynomial in the length of
  the pair, so exponential in the length of the input.

Every bound `2 ^ p(n)` with `p` a polynomial is below `2 ^ (n ^ k) + k` for some `k`, so the
single family of bounds loses nothing.
-/

namespace PEqualNP.Library

/-- coNP: the languages whose complement is in NP. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- EXP: the languages decided within `2 ^ (n ^ k) + k` steps for some `k`. -/
def EXP : Set (Language Bool) :=
  {L | ∃ k : ℕ, L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)}

/-- NEXP, by verifiers: `L` is in NEXP when there are a polynomial-time decidable set `R` of
pairs (input, witness) and a `k` such that `x` is in `L` exactly when some witness `w` of length
at most `2 ^ (length of x ^ k) + k` has `(x, w)` in `R`. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (k : ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ (x, w) ∈ R}

end PEqualNP.Library
