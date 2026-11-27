import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Definitions for geometric complexity theory

The ruling behind this file is `Gct/README.md`. GCT studies the permanent versus the
determinant as polynomials. Mathlib has the determinant and the permanent of a matrix
(`Matrix.det`, `Matrix.permanent`) and the matrix of variables (`Matrix.mvPolynomialX`), and
nothing about determinantal expressions or orbit closures. This file adds the thin layer:

* `detPoly R n`, `permPoly R n`: the determinant and permanent of the `n × n` matrix of
  variables, polynomials in `n²` variables.
* `HasDetExpression p n`: `p` is the determinant of an `n × n` matrix whose entries are affine
  linear polynomials (Valiant's determinantal expression of size `n`). The determinantal
  complexity `dc(p)` is the least such `n`; statements use this predicate directly.
* `HasBorderDetExpression p n`: `p` is a limit (coefficientwise, over `ℂ`) of polynomials with
  a determinantal expression of size `n`. The border determinantal complexity is the least such
  `n`.
* `linSubst g f`: the polynomial `x ↦ f (g x)` for a square matrix `g`.
* `orbitClosure f`: the closure of `{x ↦ f (g x) | g invertible}` over `ℂ`.
* `paddedPerm R m n`: `x₀₀^(n+1-m) · perm_m` placed in the `(n+1) × (n+1)` grid of variables,
  the polynomial Mulmuley and Sohoni compare with `det_{n+1}`.
-/

namespace PEqualNP.Gct

open MvPolynomial

/-- The determinant of the `n × n` matrix of variables `X (i, j)`. -/
noncomputable def detPoly (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

/-- The permanent of the `n × n` matrix of variables `X (i, j)`. -/
noncomputable def permPoly (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).permanent

/-- `p` is the determinant of an `n × n` matrix whose entries are affine linear polynomials
(total degree at most one) in the variables of `p`. -/
def HasDetExpression {σ R : Type} [CommRing R] (p : MvPolynomial σ R) (n : ℕ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) (MvPolynomial σ R),
    (∀ i j, (A i j).totalDegree ≤ 1) ∧ A.det = p

/-- `p` is a coefficientwise limit of complex polynomials that have a determinantal expression
of size `n`. For finitely many variables the polynomials involved have degree at most `n`, so
this is the limit in the usual topology of a finite-dimensional complex vector space. -/
def HasBorderDetExpression {σ : Type} (p : MvPolynomial σ ℂ) (n : ℕ) : Prop :=
  ∃ q : ℕ → MvPolynomial σ ℂ, (∀ k, HasDetExpression (q k) n) ∧
    ∀ s, Filter.Tendsto (fun k => (q k).coeff s) Filter.atTop (nhds (p.coeff s))

/-- Linear change of variables: the polynomial `x ↦ f (g x)`, which replaces each variable
`X i` by `∑ j, g i j * X j`. -/
noncomputable def linSubst {ι R : Type} [Fintype ι] [CommRing R] (g : Matrix ι ι R)
    (f : MvPolynomial ι R) : MvPolynomial ι R :=
  MvPolynomial.bind₁ (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) f

/-- The orbit closure of a complex polynomial under invertible linear changes of variables: the
coefficientwise limits of sequences `linSubst (g k) f` with every `g k` invertible. The orbit
lies in the finite-dimensional space of forms of the degree of `f` (when `f` is homogeneous),
where this is the closure in the usual topology, which for orbits of `GL` equals the Zariski
closure used in GCT. -/
def orbitClosure {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) :
    Set (MvPolynomial ι ℂ) :=
  {h | ∃ g : ℕ → Matrix.GeneralLinearGroup ι ℂ,
    ∀ s, Filter.Tendsto (fun k => (linSubst (g k : Matrix ι ι ℂ) f).coeff s) Filter.atTop
      (nhds (h.coeff s))}

/-- Where variable `(i, j)` of `perm_m` sits in the `(n + 1) × (n + 1)` grid: at
`(i + 1, j + 1)`. This is injective and avoids `(0, 0)` exactly when `m ≤ n`. -/
def padIndex (m n : ℕ) (p : Fin m × Fin m) : Fin (n + 1) × Fin (n + 1) :=
  (Fin.ofNat (n + 1) (p.1.val + 1), Fin.ofNat (n + 1) (p.2.val + 1))

/-- The padded permanent `x₀₀^(n+1-m) · perm_m`, homogeneous of degree `n + 1` in the
`(n + 1)²` variables of `det_{n+1}`. Meaningful when `m ≤ n`; statements assume it. -/
noncomputable def paddedPerm (R : Type) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
  MvPolynomial.X (0, 0) ^ (n + 1 - m) * MvPolynomial.rename (padIndex m n) (permPoly R m)

end PEqualNP.Gct
