import PEqualNP.Defs.ProofComplexity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Size

/-!
# Definitions of the P = NP algorithm search: resolution over rational linear equations

Res(lin) over the integers, the system R(lin) of Raz and Tzameret (Ann. Pure Appl. Logic 155,
2008), in which the unsatisfiable runs of integer linear arithmetic solvers with branching
live. A line is a disjunction of linear equations with integer coefficients over 0/1
variables. Integer and rational coefficients give the same system up to clearing
denominators. Coefficients are unbounded; the size of a refutation counts their bits.

Rules: an axiom (a clause of the formula, each literal `(v, b)` read as the equation `v = 1`
when `b` is true and `v = 0` when it is false); resolution as an integer linear combination
of the first equations of two earlier lines; semantic weakening (from one earlier line, any
line it implies on every 0/1 point). Semantic weakening contains syntactic weakening,
simplification and the Boolean axioms, so a lower bound for this system is at least as strong
as one for R(lin).
-/

namespace PEqualNP.Search

/-- A linear equation with integer coefficients over the variables `V`: the coefficient
vector and the right-hand side. -/
abbrev QEq (V : Type) : Type := (V → ℤ) × ℤ

/-- The 0/1 point `a` satisfies the equation `e`: the sum of the coefficients of the true
variables equals the right-hand side. -/
def QEq.Holds {V : Type} [Fintype V] (a : V → Bool) (e : QEq V) : Prop :=
  (∑ v, e.1 v * (if a v then 1 else 0)) = e.2

/-- A line: the disjunction of its equations. The empty line is false. -/
abbrev QLine (V : Type) : Type := List (QEq V)

/-- The 0/1 point `a` satisfies the line `L`: it satisfies some equation of `L`. -/
def QLine.Holds {V : Type} [Fintype V] (a : V → Bool) (L : QLine V) : Prop :=
  ∃ e ∈ L, QEq.Holds a e

/-- The equation of a literal: `(v, true)` is `v = 1`, `(v, false)` is `v = 0`. -/
def litQEq {V : Type} [DecidableEq V] (l : V × Bool) : QEq V :=
  (fun u => if u = l.1 then 1 else 0, if l.2 then 1 else 0)

/-- `IsResLinQDerivation F π`: the list `π` of lines is a derivation from the clauses `F`,
written NEWEST LINE FIRST. Each line is an axiom (exactly the equations of the literals of a
clause of `F`), or the combination `α e + β e'` of the first equations of two earlier lines
`e :: C` and `e' :: D` followed by `C ++ D`, or implied on every 0/1 point by one earlier
line. -/
inductive IsResLinQDerivation {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : List (QLine V) → Prop
  | nil : IsResLinQDerivation F []
  | ax {π : List (QLine V)} {L : QLine V} (C : PEqualNP.ProofComplexity.Clause V) :
      IsResLinQDerivation F π → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) →
      IsResLinQDerivation F (L :: π)
  | res {π : List (QLine V)} {e e' : QEq V} {C D : QLine V} (α β : ℤ) :
      IsResLinQDerivation F π → (e :: C) ∈ π → (e' :: D) ∈ π →
      IsResLinQDerivation F (((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) :: π)
  | weaken {π : List (QLine V)} {C D : QLine V} :
      IsResLinQDerivation F π → C ∈ π →
      (∀ a : V → Bool, QLine.Holds a C → QLine.Holds a D) →
      IsResLinQDerivation F (D :: π)

/-- A refutation: a derivation containing the empty line. -/
def IsResLinQRefutation {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (QLine V)) : Prop :=
  IsResLinQDerivation F π ∧ ([] : QLine V) ∈ π

/-- The size of an equation: one, plus the binary length of every coefficient and of the
right-hand side (`Nat.size` of the absolute value). -/
def QEq.size {V : Type} [Fintype V] (e : QEq V) : ℕ :=
  1 + (∑ v, Nat.size (e.1 v).natAbs) + Nat.size e.2.natAbs

/-- The size of a refutation: one per line plus the sizes of all its equations. -/
def resLinQSize {V : Type} [Fintype V] (π : List (QLine V)) : ℕ :=
  (π.map fun L => 1 + (L.map QEq.size).sum).sum

/-! ## Rectangle dags (dag-like Boolean communication protocols)

The variables are split between two players by `side` (`true` for the first). A set of 0/1
points is a combinatorial rectangle when it is closed under mixing: taking the first player's
part from one member and the second player's part from another stays inside the set. A
rectangle dag for a formula solves its search problem (given a point, name a clause it
falsifies): the whole cube is a node, every node is a rectangle contained in the union of at
most two earlier nodes or in the falsified set of one clause. This is the dag-like
communication model of Sokolov (STOC 2017) and Beame and Whitmeyer (ICALP 2025), with
rectangles in place of triangles. -/

/-- The point that takes the first player's variables from `a` and the others from `b`. -/
def mix {V : Type} (side : V → Bool) (a b : V → Bool) : V → Bool :=
  fun v => if side v then a v else b v

/-- `R` is a combinatorial rectangle for the split `side`. -/
def IsRect {V : Type} (side : V → Bool) (R : Set (V → Bool)) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, mix side a b ∈ R

/-- `IsRectDag side F ρ`: the list `ρ` of rectangles, NEWEST FIRST, is a rectangle dag for
the clauses `F`: each node is contained in the falsified set of a clause of `F`, or in the
union of two earlier nodes. -/
inductive IsRectDag {V : Type} (side : V → Bool) (F : Set (PEqualNP.ProofComplexity.Clause V)) :
    List (Set (V → Bool)) → Prop
  | nil : IsRectDag side F []
  | sink {ρ : List (Set (V → Bool))} {R : Set (V → Bool)} :
      IsRectDag side F ρ → IsRect side R →
      (∃ C ∈ F, ∀ a ∈ R, ¬ PEqualNP.ProofComplexity.ClauseSat a C) → IsRectDag side F (R :: ρ)
  | split {ρ : List (Set (V → Bool))} {R R₁ R₂ : Set (V → Bool)} :
      IsRectDag side F ρ → IsRect side R → R₁ ∈ ρ → R₂ ∈ ρ → R ⊆ R₁ ∪ R₂ →
      IsRectDag side F (R :: ρ)

/-- A rectangle dag that solves the search problem of `F`: it has the whole cube as a node.
Its size is its length. -/
def IsRectDagFor {V : Type} (side : V → Bool) (F : Set (PEqualNP.ProofComplexity.Clause V))
    (ρ : List (Set (V → Bool))) : Prop :=
  IsRectDag side F ρ ∧ Set.univ ∈ ρ

end PEqualNP.Search
