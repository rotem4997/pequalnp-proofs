import PEqualNP.Defs.Base

/-!
# Time classes up to constants, alternation in verifier form, and the fixed-pair link

Definitions for the conditional steps of the evasion chain. Read by the red team as drafts
(`reviews/attack-defs-2026-11-22.md`, last section) before they were placed here.

* `DTIMEO t`: deterministic time `K * t + K` for some `K` (no linear speedup is proved for the
  machine model, so classes are read up to constants).
* `NLIN a`: nondeterministic linear time in verifier form; the witness bound `a * |x|` is carried
  inside the relation.
* `Alt j s P`: `j` alternating blocks of length exactly `s`, the leading block existential.
  `Alt 0` is degenerate: use `j ≥ 1`.
* `SigmaV j T`: `j` alternations of blocks of length exactly `T |x|`, then a linear-time check.
* `Constructible T`: monotone, at least the identity, unary pad writable in time `c * T + c`.
* `HLint c`, `FP3 p q`: the hard link in integer-exponent form and its fixed-pair form at three
  alternations. These are HYPOTHESES of conditional statements; neither is proved.
* `rootUp v x`: the ceiling of the `v`-th root of `x`; `Coll u v`: nondeterministic linear time
  inside deterministic time of order `n^(u/v)`.
-/

namespace PEqualNP.Library

/-- D1. DTIME up to a constant factor and an additive constant. -/
def DTIMEO (t : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ K : ℕ, L ∈ DTIME (fun n => K * t n + K)}

/-- D2. Nondeterministic linear time in verifier form. The witness length bound `a * |x|` is
carried inside the relation (fix F7 of the route's note 210). -/
def NLIN (a : ℕ) : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (K : ℕ),
    DecidableInTime encodePair R (fun l => K * l + K) ∧
      (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ a * x.length) ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x, w) ∈ R}

/-- D3. `i` alternating blocks of length exactly `s`, the leading block existential. -/
def Alt : ℕ → ℕ → (List Bool → Prop) → Prop
  | 0, _, P => P []
  | i + 1, s, P => ∃ y : List Bool, y.length = s ∧ ¬ Alt i s (fun w => ¬ P (y ++ w))

/-- D4. Sigma_j time O(T) in verifier form: `j` blocks of length exactly `T |x|`, then a
linear-time check of the pair (input, all blocks). -/
def SigmaV (j : ℕ) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (K : ℕ),
    DecidableInTime encodePair R (fun l => K * l + K) ∧
      ∀ x : List Bool, x ∈ L ↔ Alt j (T x.length) (fun w => (x, w) ∈ R)}

/-- D5. Time-constructible, monotone, at least linear. -/
def Constructible (T : ℕ → ℕ) : Prop :=
  Monotone T ∧ (∀ n, n ≤ T n) ∧ ∃ c : ℕ,
    ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (T x.length) true) (fun n => c * T n + c)

/-- The hard link in integer-exponent form, for one collapse exponent `c`. -/
def HLint (c : ℕ) : Prop :=
  ∃ j p q : ℕ, 1 ≤ j ∧ 1 ≤ p ∧ c ^ j * p < q ∧
    ∀ L ∈ DTIMEO (fun m => 2 ^ (q * m)),
      ∃ K : ℕ, 1 ≤ K ∧ L ∈ SigmaV j (fun m => K * 2 ^ (p * m) + K)

/-- The fixed-pair link at three alternations, all languages: deterministic time `2^(q m)` up to
constants is inside three-alternation time `O(2^(p m))`. -/
def FP3 (p q : ℕ) : Prop :=
  ∀ L ∈ DTIMEO (fun m => 2 ^ (q * m)),
    ∃ K : ℕ, 1 ≤ K ∧ L ∈ SigmaV 3 (fun m => K * 2 ^ (p * m) + K)

/-- The least `r` with `x ≤ r ^ v`: the ceiling of the `v`-th root of `x` (for `v ≥ 1`). -/
noncomputable def rootUp (v x : ℕ) : ℕ := sInf {r : ℕ | x ≤ r ^ v}

/-- The collapse hypothesis at the rational exponent `u / v`: nondeterministic linear time inside
deterministic time `O(ceil (n^(u/v)))`. -/
def Coll (u v : ℕ) : Prop :=
  ∀ a : ℕ, NLIN a ⊆ DTIMEO (fun n => rootUp v (n ^ u))

end PEqualNP.Library
