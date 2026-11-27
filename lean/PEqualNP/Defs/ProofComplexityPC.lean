import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

/-!
# Definitions of the proof complexity program: polynomial calculus over the two-element field

* `PCDerivable F B p`: the polynomial `p` has a polynomial calculus derivation from the set
  `F` of polynomials over `ZMod 2` in which every line has total degree at most `B`.
* `PCRefutable F B`: the constant `1` is derivable from `F` in degree `B`.
* `bitPHPSystem m l`: the bit pigeonhole principle with `m` pigeons and `2 ^ l` holes as a
  system of polynomial equations over `ZMod 2`.
* `funPHPSystem m N`: the functional pigeonhole principle with `m` pigeons and `N` holes on
  one-hot variables, as a system of polynomial equations over `ZMod 2`.

A polynomial `p` stands for the equation `p = 0`.
-/

namespace PEqualNP.ProofComplexity

open MvPolynomial

/-- Polynomial calculus over the field with two elements, with a bound `B` on the total
degree of every line. The lines are polynomials over `ZMod 2` in the variables `σ`, and a
line `p` stands for the equation `p = 0`. The rules:

* `ax`: a polynomial of `F` of total degree at most `B`;
* `zero`: the zero polynomial;
* `add`: the sum of two derived lines (over `ZMod 2` every linear combination is a sum);
* `mulX`: the product of a variable and a derived line, when the product has total degree
  at most `B`.

The `zero` constructor is a convenience. Since `p + p = 0` over `ZMod 2`, the zero polynomial
is derivable without it as soon as any line is, so the constructor only matters when no
polynomial of `F` has degree at most `B`; with it, the derivable polynomials always form an
additive subgroup, and it never affects the derivability of `1`. -/
inductive PCDerivable {σ : Type} (F : Set (MvPolynomial σ (ZMod 2))) (B : ℕ) :
    MvPolynomial σ (ZMod 2) → Prop
  | ax {p : MvPolynomial σ (ZMod 2)} (hp : p ∈ F) (hdeg : p.totalDegree ≤ B) :
      PCDerivable F B p
  | zero : PCDerivable F B 0
  | add {p q : MvPolynomial σ (ZMod 2)} (hp : PCDerivable F B p) (hq : PCDerivable F B q) :
      PCDerivable F B (p + q)
  | mulX (j : σ) {p : MvPolynomial σ (ZMod 2)} (hp : PCDerivable F B p)
      (hdeg : (X j * p).totalDegree ≤ B) : PCDerivable F B (X j * p)

/-- A polynomial calculus refutation of `F` in degree `B`: a derivation of the constant `1`,
that is, of the contradictory equation `1 = 0`. -/
def PCRefutable {σ : Type} (F : Set (MvPolynomial σ (ZMod 2))) (B : ℕ) : Prop :=
  PCDerivable F B 1

/-- The bit pigeonhole principle with `m` pigeons and `2 ^ l` holes as a polynomial system
over `ZMod 2`. The variable `(i, t)` is bit `t` of the hole of pigeon `i`. The system has

* the Boolean axiom `X v * X v + X v` for every variable `v`;
* for every two different pigeons `i`, `i'`, the product over the bits `t` of
  `1 + X (i, t) + X (i', t)`. At a point this product is `1` exactly when the two pigeons
  have the same hole, so the equation says that they do not.

The system has no common zero exactly when `m > 2 ^ l`. -/
def bitPHPSystem (m l : ℕ) : Set (MvPolynomial (Fin m × Fin l) (ZMod 2)) :=
  {p | (∃ v : Fin m × Fin l, p = X v * X v + X v) ∨
    ∃ i i' : Fin m, i ≠ i' ∧ p = ∏ t : Fin l, (1 + X (i, t) + X (i', t))}

/-- The functional pigeonhole principle with `m` pigeons and `N` holes as a polynomial system
over `ZMod 2`. The variable `(i, j)` says that pigeon `i` goes to hole `j`. The system has

* the Boolean axiom `X v * X v + X v` for every variable `v`;
* `X (i, j) * X (i, j')` for every pigeon `i` and holes `j ≠ j'`: no pigeon has two holes;
* `X (i, j) * X (i', j)` for every hole `j` and pigeons `i ≠ i'`: no hole has two pigeons;
* `(∑ j, X (i, j)) + 1` for every pigeon `i`: with the second item, every pigeon has a hole.

The system has no common zero exactly when `m > N`. -/
def funPHPSystem (m N : ℕ) : Set (MvPolynomial (Fin m × Fin N) (ZMod 2)) :=
  {p | (∃ v : Fin m × Fin N, p = X v * X v + X v) ∨
    (∃ (i : Fin m) (j j' : Fin N), j ≠ j' ∧ p = X (i, j) * X (i, j')) ∨
    (∃ (i i' : Fin m) (j : Fin N), i ≠ i' ∧ p = X (i, j) * X (i', j)) ∨
    ∃ i : Fin m, p = (∑ j : Fin N, X (i, j)) + 1}

end PEqualNP.ProofComplexity
