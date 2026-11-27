import PEqualNP.Defs.TimeAlt

/-!
# Evasion chain, conditional steps: draft definitions and the statements of the pieces

The definitions are in `PEqualNP/Defs/TimeAlt.lean` (read by the red team as drafts first).
Source: `routes/evasion/notes/156-builder-sketches.md` (definitions D1 to D5, steps C2, C3, C5
and the small tasks of its section 8) after `00-adversary-builder-sketches.md`.
Each piece is stated as a `Prop`; each is proved in its own file of this folder.
-/

namespace PEqualNP.Library

namespace Evasion

/-- An injective pairing into binary strings: the bits of the first string doubled, then
`false, true`, then the second string. -/
def enc2 (p : List Bool × List Bool) : List Bool :=
  (p.1.flatMap fun b => [b, b]) ++ [false, true] ++ p.2

/-- C2. -/
def StmtC2 : Prop :=
  P = NP → ∃ d : ℕ, ∀ a : ℕ, NLIN a ⊆ DTIMEO (fun n => n ^ d)

/-- C3. -/
def StmtC3 : Prop :=
  ∀ c : ℕ, (∀ a : ℕ, NLIN a ⊆ DTIMEO (fun n => n ^ c)) → 1 ≤ c →
    ∀ j : ℕ, 1 ≤ j → ∀ T : ℕ → ℕ, Constructible T →
      SigmaV j T ⊆ DTIMEO (fun n => T n ^ (c ^ j))

/-- C5: the chain's conclusion from the hard link. -/
def StmtC5 : Prop :=
  (∀ c : ℕ, 1 ≤ c → HLint c) → P ≠ NP

/-- T2u. -/
def StmtT2u : Prop :=
  ∀ V : List Bool × List Bool → Bool,
    ComputableInPolyTime encodePair Computability.encodeBool V →
      {z : List Bool | ∃ w : List Bool, w.length ≤ z.length ∧ V (z, w) = true} ∈ NP

/-- T2a. -/
def StmtT2a : Prop :=
  ∀ a b : ℕ, ∃ C : ℕ, ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate (a * x.length + b) true) (fun n => C * n + C)

/-- T2b. -/
def StmtT2b : Prop :=
  ∀ (f : List Bool → List Bool) (C d : ℕ) (L L' : Language Bool),
    ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f (fun n => C * n + C) →
    (∀ x, (f x).length ≤ C * x.length + C) → f ⁻¹' L' = L →
    L' ∈ DTIMEO (fun n => n ^ d) → 1 ≤ d → L ∈ DTIMEO (fun n => n ^ d)

/-- T3a. -/
def StmtT3a : Prop :=
  ∀ (L : Language Bool) (t : ℕ → ℕ), L ∈ DTIME t → Lᶜ ∈ DTIME (fun n => t n + 1)

/-- T3b. -/
def StmtT3b : Prop :=
  ∀ b e : ℕ, 1 ≤ e → Constructible (fun n => ((b + 1) * n + 1) ^ e)

/-- T3c. -/
def StmtT3c : Prop :=
  Function.Injective enc2 ∧ ∃ C : ℕ,
    ComputableInTime encodePair (fun x : List Bool => x) enc2 (fun l => C * l + C) ∧
      ∀ p : List Bool × List Bool, (enc2 p).length ≤ C * (p.1.length + p.2.length) + C

/-- T3d. -/
def StmtT3d : Prop :=
  (∀ (s : ℕ) (Q : List Bool → Prop), Alt 1 s Q ↔ ∃ y : List Bool, y.length = s ∧ Q y) ∧
  (∀ (s : ℕ) (Q : List Bool → Prop), Alt 2 s Q ↔
    ∃ y1 : List Bool, y1.length = s ∧ ∀ y2 : List Bool, y2.length = s → Q (y1 ++ y2)) ∧
  (∀ (i s : ℕ) (Q : List Bool → Prop), ¬ Alt (i + 1) s Q ↔
    ∀ y : List Bool, y.length = s → Alt i s (fun w => ¬ Q (y ++ w)))

/-- T5a. -/
def StmtT5a : Prop :=
  ∀ t t' : ℕ → ℕ, (∀ n, t n ≤ t' n) → DTIMEO t ⊆ DTIMEO t'

/-- T5b, the patch lemma. `C0` is fixed before the language. -/
def StmtT5b : Prop :=
  ∃ C0 : ℕ, ∀ (L : Language Bool) (s t : ℕ → ℕ) (K : ℕ),
    L ∈ DTIME (fun n => K * s n + K) →
    (∃ n0 : ℕ, ∀ n, n0 ≤ n → K * s n + K + 2 * n + C0 ≤ t n) →
    (∀ n, n + C0 ≤ t n) → L ∈ DTIME t

/-- T5c. -/
def StmtT5c : Prop :=
  ∀ r C0 : ℕ, 1 ≤ r → Constructible (fun m => 2 ^ (r * m) + m + C0)

/-- T5d. -/
def StmtT5d : Prop :=
  ∀ p' q : ℕ, p' < q → ∀ k : ℕ, ∃ i : ℕ, 2 * k * p' ^ i ≤ q ^ i

/-- T5e. -/
def StmtT5e : Prop :=
  ∀ p' q : ℕ, 1 ≤ p' → p' < q →
    (∀ s : ℕ, 1 ≤ s → DTIMEO (fun m => 2 ^ (q * s * m)) ⊆ DTIMEO (fun m => 2 ^ (p' * s * m))) →
    ∀ i r : ℕ, 1 ≤ r →
      DTIMEO (fun m => 2 ^ (q ^ i * r * m)) ⊆ DTIMEO (fun m => 2 ^ (p' ^ i * r * m))

/-- The target: the fixed-pair link refutes the collapse at every exponent `u / v` with
`(u / v)^3 < q / p`. -/
def StmtRung : Prop :=
  ∀ p q u v : ℕ, 1 ≤ p → 1 ≤ v → v ≤ u → p * u ^ 3 < q * v ^ 3 → FP3 p q → Coll u v → False

/-- No collapse of exponential time classes that holds at every scale (a padding form of the
time hierarchy, from the checked L-lib-088). -/
def StmtNoScaledCollapse : Prop :=
  ∀ P Q : ℕ, 1 ≤ P → P < Q →
    (∀ s : ℕ, 1 ≤ s → DTIMEO (fun m => 2 ^ (Q * s * m)) ⊆ DTIMEO (fun m => 2 ^ (P * s * m))) →
    False

/-- 3.1 of note 210. -/
def StmtDtimeoO : Prop :=
  ∀ (t t' : ℕ → ℕ) (A : ℕ), (∀ n, t n ≤ A * t' n + A) → DTIMEO t ⊆ DTIMEO t'

/-- 3.2 of note 210: the exponential clock with constants. -/
def StmtCLK : Prop :=
  ∀ p K : ℕ, 1 ≤ p → 1 ≤ K → Constructible (fun m => K * 2 ^ (p * m) + K)

end Evasion

end PEqualNP.Library
