import PEqualNP.Defs.ProofComplexityPC
import PEqualNP.Defs.ProofComplexity

/-!
# Definitions of the proof complexity program: a CNF formula as a polynomial system

The standard translation of clauses to polynomials over the two-element field, used to state
the general link between resolution over linear equations and polynomial calculus degree.
The ruling is in `ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

open MvPolynomial

/-- The polynomial of a clause: the product, over its literals, of `1 + X v` for a positive
literal `(v, true)` and of `X v` for a negative literal `(v, false)`. At a point of the cube
it is `1` exactly when the clause is false, so the equation "polynomial = 0" says the clause
holds. The empty clause has polynomial `1`. Its degree is at most the number of literals. -/
noncomputable def clausePoly {V : Type} (C : Clause V) : MvPolynomial V (ZMod 2) :=
  ∏ l ∈ C, (if l.2 = true then 1 + X l.1 else X l.1)

/-- The polynomial system of a set of clauses: the Boolean axiom `X v * X v + X v` for every
variable `v`, and the polynomial of every clause. A point is a common zero exactly when it is
a satisfying assignment. -/
def cnfSystem {V : Type} (F : Set (Clause V)) : Set (MvPolynomial V (ZMod 2)) :=
  {p | (∃ v : V, p = X v * X v + X v) ∨ ∃ C ∈ F, p = clausePoly C}

end PEqualNP.ProofComplexity
