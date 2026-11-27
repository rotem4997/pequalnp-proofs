import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.SymmDiff
import PEqualNP.Defs.ProofComplexityLin
import PEqualNP.Search.Helpers.Graph

/-!
# DRAFT: a sum-of-squares wall for parity systems (definitions and statements only)

A design draft of seat-lib-1's pricing leg. NOTHING here is a result of the fleet. The
statements are `def ... : Prop`, to be falsified and priced, not proved. The two theorems at
the end of the first section are routine soundness facts, proved in full, kept only as a
check that the definitions can be worked with. The pricing is in `notes/sa-sos-wall-pricing.md`.

Conventions.

* A parity system is a set of `PEqualNP.ProofComplexity.LinEq V`: the pair `(S, b)` says that
  the number of true variables of `S` is odd exactly when `b = true`.
* The algebraic side uses sign variables over the reals: the truth value `true` is the real
  number `-1`, `false` is `1`. The equation `(S, b)` becomes `∏ v ∈ S, X v = (-1) ^ b`.
* `SoSRefutable P D` is a sum-of-squares (Positivstellensatz) refutation of degree `2 * D` of
  the system of polynomial EQUATIONS `p = 0`, `p ∈ P`.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft

open MvPolynomial PEqualNP.ProofComplexity

section Definitions

variable {V : Type}

/-- Gaussian derivations of bounded width. `XorDerivable F d e`: the equation `e` is obtained
from the parity system `F` by adding equations, every line having at most `d` variables.

* `ax`: an equation of `F` on at most `d` variables;
* `zero`: the trivial equation `0 = 0` (a convenience: it is the sum of any line with itself,
  so it only matters when `F` has no equation on at most `d` variables);
* `add`: the sum of two derived lines (symmetric difference of the variable sets, exclusive
  or of the right-hand sides), when the sum has at most `d` variables. -/
inductive XorDerivable [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) :
    PEqualNP.ProofComplexity.LinEq V → Prop
  | ax {e : PEqualNP.ProofComplexity.LinEq V} (he : e ∈ F) (hw : e.1.card ≤ d) :
      XorDerivable F d e
  | zero : XorDerivable F d (∅, false)
  | add {e e' : PEqualNP.ProofComplexity.LinEq V} (h : XorDerivable F d e)
      (h' : XorDerivable F d e')
      (hw : (symmDiff e.1 e'.1).card ≤ d) :
      XorDerivable F d (symmDiff e.1 e'.1, xor e.2 e'.2)

/-- A Gaussian refutation of width `d`: a derivation of `0 = 1` with every line on at most `d`
variables. -/
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

/-- A sum-of-squares refutation of degree `2 * D` of the equations `p = 0`, `p ∈ P`:
polynomials `q_i`, members `p_i` of `P` and polynomials `r_j` with
`∑ q_i * p_i + ∑ r_j * r_j = -1`, every `q_i * p_i` of total degree at most `2 * D` and every
`r_j` of total degree at most `D`.

The first sum is a member of the real span of the allowed products (a real multiple of an
allowed product is an allowed product, so the span adds nothing but sums); the second sum is
a member of the additive closure of the allowed squares. Over the reals the total degree of
`q * p` is the sum of the two degrees when neither is zero, so bounding the product is the
usual convention. -/
def SoSRefutable (P : Set (MvPolynomial V ℝ)) (D : ℕ) : Prop :=
  ∃ g ∈ Submodule.span ℝ
      {t : MvPolynomial V ℝ | ∃ p ∈ P, ∃ q : MvPolynomial V ℝ, t = q * p ∧ t.totalDegree ≤ 2 * D},
    ∃ s ∈ AddSubmonoid.closure
      {t : MvPolynomial V ℝ | ∃ r : MvPolynomial V ℝ, r.totalDegree ≤ D ∧ t = r * r},
    g + s = -1

/-- The dual object, a pseudo-expectation of degree `2 * D` for the equations `P`: a real
linear functional with value `1` at `1`, vanishing on every allowed product `q * p`, and
nonnegative on every allowed square. -/
def IsPseudoExpectation (P : Set (MvPolynomial V ℝ)) (D : ℕ)
    (E : MvPolynomial V ℝ →ₗ[ℝ] ℝ) : Prop :=
  E 1 = 1 ∧
  (∀ p ∈ P, ∀ q : MvPolynomial V ℝ, (q * p).totalDegree ≤ 2 * D → E (q * p) = 0) ∧
  ∀ r : MvPolynomial V ℝ, r.totalDegree ≤ D → 0 ≤ E (r * r)

/-- A Sherali-Adams refutation of degree `D` in sign variables:
`∑ q_i * p_i + ∑ c_j * J_j = -1` with every `q_i * p_i` of total degree at most `D`, every
`c_j ≥ 0`, and every `J_j` a product `∏ v ∈ A, (1 + X v) * ∏ v ∈ B, (1 - X v)` with
`A.card + B.card ≤ D`. Up to the positive factor `2 ^ (A.card + B.card)` such a product is
the indicator of "the variables of `A` are false and those of `B` are true", which is the
usual Sherali-Adams generator after the affine change between 0/1 and sign variables. -/
def SARefutable (P : Set (MvPolynomial V ℝ)) (D : ℕ) : Prop :=
  ∃ g ∈ Submodule.span ℝ
      {t : MvPolynomial V ℝ | ∃ p ∈ P, ∃ q : MvPolynomial V ℝ, t = q * p ∧ t.totalDegree ≤ D},
    ∃ s ∈ AddSubmonoid.closure
      {t : MvPolynomial V ℝ | ∃ (c : ℝ) (A B : Finset V), 0 ≤ c ∧ A.card + B.card ≤ D ∧
        t = C c * ((∏ v ∈ A, (1 + X v)) * ∏ v ∈ B, (1 - X v))},
    g + s = -1

/-- Soundness of the dual (proved, routine): a pseudo-expectation rules out a refutation. -/
theorem not_sosRefutable_of_pseudoExpectation {P : Set (MvPolynomial V ℝ)} {D : ℕ}
    {E : MvPolynomial V ℝ →ₗ[ℝ] ℝ} (hE : IsPseudoExpectation P D E) : ¬ SoSRefutable P D := by
  rintro ⟨g, hg, s, hs, hgs⟩
  obtain ⟨h1, h2, h3⟩ := hE
  have hg0 : E g = 0 := by
    refine Submodule.span_induction (p := fun x _ => E x = 0) ?_ ?_ ?_ ?_ hg
    · rintro x ⟨p, hp, q, rfl, hdeg⟩
      exact h2 p hp q hdeg
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro a x _ hx
      simp [hx]
  have hs0 : 0 ≤ E s := by
    refine AddSubmonoid.closure_induction (motive := fun x _ => 0 ≤ E x) ?_ ?_ ?_ hs
    · rintro x ⟨r, hr, rfl⟩
      exact h3 r hr
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_nonneg hx hy
  have h := congrArg E hgs
  rw [map_add, hg0, map_neg, h1] at h
  linarith

/-- Soundness of the system (proved, routine): a refutable system of equations has no common
real zero. -/
theorem not_exists_zero_of_sosRefutable {P : Set (MvPolynomial V ℝ)} {D : ℕ}
    (h : SoSRefutable P D) : ¬ ∃ x : V → ℝ, ∀ p ∈ P, eval x p = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, s, hs, hgs⟩ := h
  have hg0 : eval x g = 0 := by
    refine Submodule.span_induction (p := fun y _ => eval x y = 0) ?_ ?_ ?_ ?_ hg
    · rintro y ⟨p, hp, q, rfl, -⟩
      simp [hx p hp]
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro a y _ hy
      simp [hy]
  have hs0 : 0 ≤ eval x s := by
    refine AddSubmonoid.closure_induction (motive := fun y _ => 0 ≤ eval x y) ?_ ?_ ?_ hs
    · rintro y ⟨r, -, rfl⟩
      rw [map_mul]
      exact mul_self_nonneg _
    · simp
    · intro y z _ _ hy hz
      rw [map_add]
      exact add_nonneg hy hz
  have h := congrArg (eval x) hgs
  rw [map_add, hg0, map_neg, map_one] at h
  linarith

end Definitions

/-! ## The statements (conjectures until checked) -/

/-- THE TARGET (the wall). If a parity system has no Gaussian refutation of width `d`, then
its sign-variable polynomial system has no sum-of-squares refutation of degree `2 * D` for
any `D` with `2 * D ≤ d`. -/
def SoSWall : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d D : ℕ),
    2 * D ≤ d → ¬ XorRefutable F d → ¬ SoSRefutable (xorSystem F) D

/-- The dual form, which is what the proof builds: under the same hypotheses a
pseudo-expectation exists. With `not_sosRefutable_of_pseudoExpectation` it gives `SoSWall`. -/
def SoSWallDual : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d D : ℕ),
    2 * D ≤ d → ¬ XorRefutable F d →
      ∃ E : MvPolynomial V ℝ →ₗ[ℝ] ℝ, IsPseudoExpectation (xorSystem F) D E

/-- Faithfulness of the encoding: the polynomial system has a common real zero exactly when
the parity system has a satisfying assignment. -/
def XorSystemFaithful : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)),
    (∃ x : V → ℝ, ∀ p ∈ xorSystem F, eval x p = 0) ↔ ∃ a : V → Bool, ∀ e ∈ F, LinEqSat a e

/-- Sherali-Adams is no stronger than sum of squares at the same parameter, on systems that
contain the sign axioms. With `SoSWall` this gives the Sherali-Adams wall at `2 * D ≤ d`. -/
def SALeSoS : Prop :=
  ∀ (V : Type) [DecidableEq V] (P : Set (MvPolynomial V ℝ)) (D : ℕ),
    (∀ v : V, X v * X v - 1 ∈ P) → SARefutable P D → SoSRefutable P D

/-- The sharper Sherali-Adams wall (degree `D ≤ d`, not `2 * D ≤ d`); a separate, dearer step. -/
def SAWall : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d D : ℕ),
    D ≤ d → ¬ XorRefutable F d → ¬ SARefutable (xorSystem F) D

/-! ## An explicit family from what is checked: Tseitin parities on split grids -/

/-- The Tseitin parity system of `G` with charge at `v0`: at each vertex the number of true
edges is odd exactly at `v0`. -/
def tseitinXor {m n : ℕ} (G : EdgeGraph m n) (v0 : Fin m) :
    Set (PEqualNP.ProofComplexity.LinEq (Fin n)) :=
  {e | ∃ v : Fin m, e = (G.incident v, decide (v = v0))}

/-- The width input, from the hypothesis already checked for split grids
(`splitGrid_exists`): if deleting any `2 * k` edges leaves a component with more than half of
the vertices, the Tseitin parity system has no Gaussian refutation of width `k`. -/
def TseitinXorWidth : Prop :=
  ∀ (m n : ℕ) (G : EdgeGraph m n) (v0 : Fin m) (k : ℕ), 2 ≤ m →
    (∀ S : Finset (Fin n), S.card ≤ 2 * k → ∃ v, G.BigComp S v) → G.BigComp ∅ v0 →
    ¬ XorRefutable (tseitinXor G v0) k

/-- The explicit wall: for every `D` there is an unsatisfiable parity system with at most 3
variables in every equation and no sum-of-squares refutation of degree `2 * D`. -/
def TseitinSoSWall : Prop :=
  ∀ D : ℕ, ∃ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.LinEq (Fin n))),
    (∀ e ∈ F, e.1.card ≤ 3) ∧ (¬ ∃ a : Fin n → Bool, ∀ e ∈ F, LinEqSat a e) ∧
    ¬ SoSRefutable (xorSystem F) D

end PEqualNP.Search.Helpers.HierarchyDraft
