import PEqualNP.Defs.SearchQ

/-!
# Definitions of the P = NP algorithm search: cutting planes and triangle dags

Cutting planes over the integers (Cook, Coullard and Turan 1987) for CNFs on `V`. A line is
an inequality `∑ a_v x_v ≥ c` with integer coefficients over 0/1 variables. Rules: an axiom
(a clause read as the sum of its literals `≥ 1`, literal `x` or `1 - x`); the Boolean axioms
`x_v ≥ 0` and `-x_v ≥ -1`; the sum of two earlier lines; an earlier line times a nonnegative
integer; an earlier line divided by a positive integer `d` dividing all its coefficients, the
constant rounded up. A refutation contains `0 ≥ 1`. Its size here is its number of lines.

Triangles for a split (Hrubes and Pudlak 2017; Sokolov 2017; Beame and Whitmeyer 2025): a set
`{x | a x < b x}` with `a` reading only the first player's coordinates and `b` only the
second's. Integer labels: on a finite cube real labels give the same sets.
-/

namespace PEqualNP.Search

/-- A cutting planes line `∑ v, e.1 v * x v ≥ e.2`: coefficients and constant. -/
abbrev CPLine (V : Type) : Type := (V → ℤ) × ℤ

/-- The 0/1 point `a` satisfies the line `e`. -/
def CPLine.Holds {V : Type} [Fintype V] (a : V → Bool) (e : CPLine V) : Prop :=
  e.2 ≤ ∑ v, e.1 v * (if a v then 1 else 0)

/-- The line of a clause: the sum over its literals of `x_v` for `(v, true)` and `1 - x_v` for
`(v, false)`, at least `1`. -/
def clauseCP {V : Type} [DecidableEq V] (C : PEqualNP.ProofComplexity.Clause V) : CPLine V :=
  (fun v => ∑ l ∈ C, if l.1 = v then (if l.2 then 1 else -1) else 0,
   1 - ∑ l ∈ C, if l.2 then 0 else 1)

/-- `IsCPDerivation F π`: the list `π` of lines is a cutting planes derivation from the
clauses `F`, written NEWEST LINE FIRST. -/
inductive IsCPDerivation {V : Type} [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : List (CPLine V) → Prop
  | nil : IsCPDerivation F []
  | ax {π : List (CPLine V)} (C : PEqualNP.ProofComplexity.Clause V) :
      IsCPDerivation F π → C ∈ F → IsCPDerivation F (clauseCP C :: π)
  | boolLo {π : List (CPLine V)} (v : V) :
      IsCPDerivation F π → IsCPDerivation F ((fun u => if u = v then 1 else 0, 0) :: π)
  | boolHi {π : List (CPLine V)} (v : V) :
      IsCPDerivation F π → IsCPDerivation F ((fun u => if u = v then -1 else 0, -1) :: π)
  | add {π : List (CPLine V)} {e e' : CPLine V} :
      IsCPDerivation F π → e ∈ π → e' ∈ π → IsCPDerivation F ((e.1 + e'.1, e.2 + e'.2) :: π)
  | mul {π : List (CPLine V)} {e : CPLine V} (k : ℕ) :
      IsCPDerivation F π → e ∈ π → IsCPDerivation F (((k : ℤ) • e.1, (k : ℤ) * e.2) :: π)
  | div {π : List (CPLine V)} {e : CPLine V} (d : ℕ) :
      IsCPDerivation F π → e ∈ π → 0 < d → (∀ v, (d : ℤ) ∣ e.1 v) →
      IsCPDerivation F ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π)

/-- A cutting planes refutation: a derivation containing `0 ≥ 1`. Its size is `π.length`. -/
def IsCPRefutation {V : Type} [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (CPLine V)) : Prop :=
  IsCPDerivation F π ∧ ((0 : V → ℤ), (1 : ℤ)) ∈ π

/-! ## Triangle dags -/

/-- `S` is a triangle for the split `side`: `S = {x | a x < b x}` where `a` reads only the
coordinates with `side v = true` and `b` only the others. -/
def IsTri {V : Type} (side : V → Bool) (S : Set (V → Bool)) : Prop :=
  ∃ a b : (V → Bool) → ℤ, (∀ x y, a (mix side x y) = a x) ∧ (∀ x y, b (mix side x y) = b y) ∧
    ∀ x, x ∈ S ↔ a x < b x

/-- `IsTriDag side F ρ`: `IsRectDag` with triangles in place of rectangles. -/
inductive IsTriDag {V : Type} (side : V → Bool) (F : Set (PEqualNP.ProofComplexity.Clause V)) :
    List (Set (V → Bool)) → Prop
  | nil : IsTriDag side F []
  | sink {ρ : List (Set (V → Bool))} {R : Set (V → Bool)} :
      IsTriDag side F ρ → IsTri side R →
      (∃ C ∈ F, ∀ a ∈ R, ¬ PEqualNP.ProofComplexity.ClauseSat a C) → IsTriDag side F (R :: ρ)
  | split {ρ : List (Set (V → Bool))} {R R₁ R₂ : Set (V → Bool)} :
      IsTriDag side F ρ → IsTri side R → R₁ ∈ ρ → R₂ ∈ ρ → R ⊆ R₁ ∪ R₂ →
      IsTriDag side F (R :: ρ)

/-- A triangle dag that solves the search problem of `F`. Its size is its length. -/
def IsTriDagFor {V : Type} (side : V → Bool) (F : Set (PEqualNP.ProofComplexity.Clause V))
    (ρ : List (Set (V → Bool))) : Prop :=
  IsTriDag side F ρ ∧ Set.univ ∈ ρ

end PEqualNP.Search
