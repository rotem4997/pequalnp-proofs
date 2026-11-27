import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.SymmDiff
import PEqualNP.Defs.ProofComplexityLin

/-!
# Definitions of the P = NP algorithm search: sum of squares on parity systems

A parity system is a set of equations `(S, b)`: the sum of the variables of `S` is `b` modulo
two. Two ways to refute one:

* by adding equations, every line on at most `d` variables (`XorRefutable`);
* by a sum-of-squares refutation of its polynomial system in sign variables over the reals
  (`SoSRefutable`), where `true` is the sign `-1` and each variable satisfies `x * x = 1`.

In `SoSRefutable P D` the number `D` is HALF the degree of the refutation.
-/

namespace PEqualNP.Search

open MvPolynomial

variable {V : Type}

/-- `XorDerivable F d e`: the equation `e` is obtained from the parity system `F` by adding
equations, every line having at most `d` variables. `ax`: an equation of `F` on at most `d`
variables; `zero`: the trivial equation `0 = 0`; `add`: the sum of two derived lines (symmetric
difference of the variable sets, exclusive or of the right-hand sides), when the sum has at
most `d` variables. -/
inductive XorDerivable [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) :
    PEqualNP.ProofComplexity.LinEq V → Prop
  | ax {e : PEqualNP.ProofComplexity.LinEq V} (he : e ∈ F) (hw : e.1.card ≤ d) :
      XorDerivable F d e
  | zero : XorDerivable F d (∅, false)
  | add {e e' : PEqualNP.ProofComplexity.LinEq V} (h : XorDerivable F d e)
      (h' : XorDerivable F d e')
      (hw : (symmDiff e.1 e'.1).card ≤ d) :
      XorDerivable F d (symmDiff e.1 e'.1, xor e.2 e'.2)

/-- A refutation of width `d` by adding equations: a derivation of `0 = 1` with every line on
at most `d` variables. -/
def XorRefutable [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) : Prop :=
  XorDerivable F d (∅, true)

/-- The parity equation `(S, b)` as a real polynomial in sign variables: the product of the
variables of `S`, minus `-1` when `b = true` and minus `1` when `b = false`. It stands for the
equation "this polynomial is zero". -/
noncomputable def xorPoly (e : PEqualNP.ProofComplexity.LinEq V) : MvPolynomial V ℝ :=
  (∏ v ∈ e.1, X v) - C (if e.2 = true then -1 else 1)

/-- The polynomial system of a parity system: `X v * X v - 1` for every variable (each variable
is a sign), and the polynomial of every equation. -/
noncomputable def xorSystem (F : Set (PEqualNP.ProofComplexity.LinEq V)) :
    Set (MvPolynomial V ℝ) :=
  {p | ∃ v : V, p = X v * X v - 1} ∪ xorPoly '' F

/-- A sum-of-squares refutation of degree `2 * D` (so `D` is half the degree) of the equations
`p = 0`, `p ∈ P`: polynomials `q_i`, members `p_i` of `P` and polynomials `r_j` with
`∑ q_i * p_i + ∑ r_j * r_j = -1`, every `q_i * p_i` of total degree at most `2 * D` and every
`r_j` of total degree at most `D`. The first sum is a member of the real span of the allowed
products; the second sum is a member of the additive closure of the allowed squares. -/
def SoSRefutable (P : Set (MvPolynomial V ℝ)) (D : ℕ) : Prop :=
  ∃ g ∈ Submodule.span ℝ
      {t : MvPolynomial V ℝ | ∃ p ∈ P, ∃ q : MvPolynomial V ℝ, t = q * p ∧ t.totalDegree ≤ 2 * D},
    ∃ s ∈ AddSubmonoid.closure
      {t : MvPolynomial V ℝ | ∃ r : MvPolynomial V ℝ, r.totalDegree ≤ D ∧ t = r * r},
    g + s = -1

end PEqualNP.Search
