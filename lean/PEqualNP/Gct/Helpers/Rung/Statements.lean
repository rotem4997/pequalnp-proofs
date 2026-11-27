import Mathlib
import PEqualNP.Defs

/-!
# The superquadratic rung: shared definitions and step statements

STATUS: statements only. Nothing in this file is proved; every `def ... : Prop` below is a
CONJECTURE until some module proves `theorem ... : <Name>` and the checker accepts the lemma
that rests on it. The chain is ours (notes: `Gct/Gadget025/dim.md`, `rung-notes.md`).

Target: L-gct-057 (the permanent restricts to smooth forms with `(r-1)(d-1)/m^2` unbounded) and
from it L-gct-056 (border determinantal complexity of the permanent is not `O(m^2)`).

The gadget is `G_r(X)`, the sum of all `r × r` subpermanents of an `a × b` matrix, and the block
sum of `N` copies of it in disjoint variables. The chain:

* `LemmaE`: a singular point of the elementary symmetric polynomial `e_r` takes at most `r - 1`
  distinct coordinate values.
* `Avoidance`: finitely many subspaces of dimension at most `q` are all missed (off `0`) by one
  subspace of codimension `q`.
* `RowSpaceExists` (from the two above): a subspace of `ℂ^b` of dimension `b + 1 - r` on which
  the gradient of `e_r` has no nonzero zero.
* `RowSystem` (identity I2): at a singular point of `G_r` all rows are common zeros of one
  system of `b` polynomials whose top forms are the partials of `e_r`.
* `BoundedZeros` (Fact Z): a system whose top forms have no common nonzero zero has boundedly
  many zeros, uniformly in the lower order terms.
* `FewRows` (from the two above): singular points of `G_r` with rows in a good row space have
  boundedly many distinct rows, uniformly in the number of rows.
* `GoodSubspace` (from `FewRows` and `Avoidance`): a subspace of dimension
  `N (a - M) l` on which the gradient of the block sum has no nonzero zero.
* `BlockPerm` (Theorem C): the block sum is an affine restriction of a permanent of size
  `a + N (b + r) - r`, up to a nonzero constant.
* `Arith`: the choice of parameters.
* `AssemblyRestriction`, `AssemblyBound`: the assemblies, with L-gct-053, L-gct-024 and
  L-gct-023 taken as hypotheses in the exact form of their recorded statements.

Convention (the one of L-gct-053): a linear map into `ℂ^σ` is a family `L : σ → Fin d → ℂ` and
the image of `y` is the point `fun n => ∑ s, L n s * y s`.
-/

namespace PEqualNP.Gct.Rung

open MvPolynomial

/-- The sum of the permanents of all `r × r` submatrices of an `a × b` matrix. The rows and
columns of a submatrix are listed in increasing order (the permanent does not depend on it). -/
noncomputable def sumSubperm {R : Type} [CommRing R] {a b : ℕ} (r : ℕ)
    (X : Matrix (Fin a) (Fin b) R) : R :=
  ∑ S : {S : Finset (Fin a) // S.card = r}, ∑ T : {T : Finset (Fin b) // T.card = r},
    Matrix.permanent
      (Matrix.of fun i j : Fin r => X (S.1.orderEmbOfFin S.2 i) (T.1.orderEmbOfFin T.2 j))

/-- The gadget as a polynomial in the `a b` variables `X (i, j)`: homogeneous of degree `r`
(zero when `r` exceeds `a` or `b`, the constant one when `r = 0`). -/
noncomputable def gadgetPoly (a b r : ℕ) : MvPolynomial (Fin a × Fin b) ℂ :=
  sumSubperm r (Matrix.mvPolynomialX (Fin a) (Fin b) ℂ)

/-- The block sum: `N` copies of the gadget in disjoint sets of variables `X (h, i, j)`. -/
noncomputable def blockPoly (N a b r : ℕ) : MvPolynomial (Fin N × Fin a × Fin b) ℂ :=
  ∑ h : Fin N, rename (fun p : Fin a × Fin b => (h, p)) (gadgetPoly a b r)

/-- All first partial derivatives of `G` vanish at the point `x`. -/
def GradZero {σ : Type} (G : MvPolynomial σ ℂ) (x : σ → ℂ) : Prop :=
  ∀ i, eval x (pderiv i G) = 0

/-- The column space of `P` (a subspace of `ℂ^b`, parametrized by `ℂ^l`) is a good row space
for degree `r`: the gradient of the elementary symmetric polynomial `e_r` in `b` variables
vanishes at `P y` only for `y = 0`. For `r ≥ 2` this forces `P` to be injective. -/
def RowSpaceGood (b r l : ℕ) (P : Fin b → Fin l → ℂ) : Prop :=
  ∀ y : Fin l → ℂ, GradZero (esymm (Fin b) ℂ r) (fun n => ∑ s, P n s * y s) → y = 0

/-- The conclusion of `FewRows` for one bound `M`: for every number of rows `a`, a point of
`ℂ^(a × b)` whose rows all lie in the column space of `P` and at which the gradient of the
gadget vanishes has at most `M` distinct rows. -/
def RowsBounded (b r l : ℕ) (P : Fin b → Fin l → ℂ) (M : ℕ) : Prop :=
  ∀ (a : ℕ) (X : Fin a × Fin b → ℂ),
    (∀ i, ∃ y : Fin l → ℂ, ∀ j, X (i, j) = ∑ s, P j s * y s) →
    GradZero (gadgetPoly a b r) X →
    (Finset.univ.image fun i : Fin a => fun j : Fin b => X (i, j)).card ≤ M

/-! ## Block one: the row space -/

/-- Lemma E. If all partials of `e_r` (`r ≥ 2`) vanish at `z`, then `z` takes at most `r - 1`
distinct coordinate values: each `z_i` is a root of one polynomial of degree `r - 1`. -/
def LemmaE : Prop :=
  ∀ (b r : ℕ) (z : Fin b → ℂ), 2 ≤ r → GradZero (esymm (Fin b) ℂ r) z →
    (Finset.univ.image z).card ≤ r - 1

/-- Avoidance, pure linear algebra over an infinite field: finitely many subspaces, each of
dimension at most `q`, are met only in `0` by one subspace of dimension `dim V - q`. -/
def Avoidance : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Finite ι]
    (W : ι → Submodule ℂ V) (q : ℕ), (∀ i, Module.finrank ℂ (W i) ≤ q) →
    ∃ U : Submodule ℂ V, Module.finrank ℂ U = Module.finrank ℂ V - q ∧ ∀ i, U ⊓ W i = ⊥

/-- A good row space of dimension `l = b + 1 - r` exists (from `LemmaE` and `Avoidance`: the
vectors with at most `r - 1` distinct values form finitely many subspaces of dimension at
most `r - 1`). -/
def RowSpaceExists : Prop :=
  ∀ b r l : ℕ, 2 ≤ r → l + r = b + 1 → ∃ P : Fin b → Fin l → ℂ, RowSpaceGood b r l P

/-! ## Block two: few distinct rows -/

/-- The row system (identity I2 of the notes, divided by its leading constant). At a point `X`
where the gradient of the gadget vanishes there are `b` polynomials in `b` variables, the same
for every row, such that `f j` differs from the partial of `e_r` in direction `j` by terms of
degree below `r - 1`, and every row of `X` is a common zero of them. -/
def RowSystem : Prop :=
  ∀ (a b r : ℕ) (X : Fin a × Fin b → ℂ), 2 ≤ r → GradZero (gadgetPoly a b r) X →
    ∃ f : Fin b → MvPolynomial (Fin b) ℂ,
      (∀ j, (f j - pderiv j (esymm (Fin b) ℂ r)).totalDegree < r - 1) ∧
      ∀ i j, eval (fun j' => X (i, j')) (f j) = 0

/-- Fact Z. Forms `g_1, ..., g_k` of one degree `t` in `l` variables with no common nonzero zero
come with a bound `M`: any system `f_j = g_j + (terms of degree below t)` has at most `M`
common zeros. (By the Nullstellensatz a power of the maximal ideal lies in the ideal of the
`g_j`, so the quotient by the `f_j` is spanned by monomials of bounded degree.) -/
def BoundedZeros : Prop :=
  ∀ (l k t : ℕ) (g : Fin k → MvPolynomial (Fin l) ℂ), (∀ j, (g j).IsHomogeneous t) →
    (∀ y : Fin l → ℂ, (∀ j, eval y (g j) = 0) → y = 0) →
    ∃ M : ℕ, ∀ f : Fin k → MvPolynomial (Fin l) ℂ, (∀ j, (f j - g j).totalDegree < t) →
      ∀ s : Finset (Fin l → ℂ), (∀ y ∈ s, ∀ j, eval y (f j) = 0) → s.card ≤ M

/-- Few rows (from `RowSystem` and `BoundedZeros`, restricting the row system to the row
space): a good row space has a bound `M`, independent of the number of rows, on the number of
distinct rows of a singular point of the gadget with rows in that space. -/
def FewRows : Prop :=
  ∀ (b r l : ℕ) (P : Fin b → Fin l → ℂ), 2 ≤ r → RowSpaceGood b r l P →
    ∃ M : ℕ, RowsBounded b r l P M

/-! ## Block three: the subspace, the permanent, the assembly -/

/-- The good subspace (from `Avoidance`): if singular points with rows in the row space have at
most `M` distinct rows, they lie in finitely many subspaces of dimension at most `M l` (rows
constant on the classes of a partition into at most `M` classes) of the `a l`-dimensional space
of matrices with rows in the row space; a subspace of dimension `(a - M) l` misses them, and
the product over the `N` blocks is a subspace of dimension `N (a - M) l` on which the gradient
of the block sum has no nonzero zero. -/
def GoodSubspace : Prop :=
  ∀ (b r l : ℕ) (P : Fin b → Fin l → ℂ) (M : ℕ), 2 ≤ r → RowSpaceGood b r l P →
    RowsBounded b r l P M →
    ∀ a N : ℕ, ∃ L : Fin N × Fin a × Fin b → Fin (N * ((a - M) * l)) → ℂ,
      ∀ y : Fin (N * ((a - M) * l)) → ℂ,
        GradZero (blockPoly N a b r) (fun v => ∑ s, L v s * y s) → y = 0

/-- Theorem C of the notes: the block sum is, up to a nonzero constant, the permanent of a
square matrix of size `a + N (b + r) - r` whose entries are variables, zeros, ones and `r`-th
roots of unity. Rows: `a` top rows, `b` rows per block, `(N - 1) r` extra rows. Columns: `b`
per block, `r` selector columns per block, `a - r` padding columns. -/
def BlockPerm : Prop :=
  ∀ N a b r : ℕ, 1 ≤ N → 1 ≤ r → r ≤ a → r ≤ b →
    ∃ (c : ℂ) (g : Fin (a + N * (b + r) - r) × Fin (a + N * (b + r) - r) →
        MvPolynomial (Fin N × Fin a × Fin b) ℂ),
      c ≠ 0 ∧ (∀ p, (g p).totalDegree ≤ 1) ∧
      bind₁ g (PEqualNP.Gct.permPoly ℂ (a + N * (b + r) - r)) = C c * blockPoly N a b r

/-- The choice of parameters: with `b = 2 r`, row space dimension `r + 1` and `a = 3 r N`, the
permanent has size `m = 6 r N - r` and the section has `d = N (3 r N - M) (r + 1)` variables;
for `r ≥ 48 R + 48` and `N` large, `(r - 1)(d - 1) ≥ R m^2`. -/
def Arith : Prop :=
  ∀ R M m0 r : ℕ, 48 * R + 48 ≤ r → ∃ N : ℕ, 1 ≤ N ∧ r ≤ 3 * r * N ∧
    m0 ≤ 3 * r * N + N * (2 * r + r) - r ∧ 1 ≤ 3 * r * N + N * (2 * r + r) - r ∧
    2 ≤ N * ((3 * r * N - M) * (r + 1)) ∧
    R * (3 * r * N + N * (2 * r + r) - r) ^ 2 ≤
      (r - 1) * (N * ((3 * r * N - M) * (r + 1)) - 1)

/-- The recorded statement of L-gct-053 (a subspace on which the full gradient has no nonzero
zero gives a smooth section of the same dimension), as a hypothesis. -/
def Stmt053 : Prop :=
  ∀ (N d r : ℕ) (G : MvPolynomial (Fin N) ℂ) (L : Fin N → Fin d → ℂ), G.IsHomogeneous r →
    (∀ y : Fin d → ℂ, (∀ i, MvPolynomial.eval (fun n => ∑ s, L n s * y s)
      (MvPolynomial.pderiv i G) = 0) → y = 0) →
    ∃ M : Fin N → Fin d → ℂ, ∀ y : Fin d → ℂ,
      (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s
        (MvPolynomial.bind₁ (fun n => ∑ t, MvPolynomial.C (M n t) * MvPolynomial.X t) G)) = 0) →
      y = 0

/-- The recorded statement of L-gct-024 (smooth forms need border determinantal size
`(r-1)(d-1)/11`). -/
def Stmt024 : Prop :=
  ∀ (d r n : ℕ) (G : MvPolynomial (Fin d) ℂ), 2 ≤ d → 2 ≤ r → G.IsHomogeneous r →
    (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) →
    PEqualNP.Gct.HasBorderDetExpression G n → (r - 1) * (d - 1) ≤ 11 * n

/-- The recorded statement of L-gct-023 (border expressions survive affine substitutions). -/
def Stmt023 : Prop :=
  ∀ (σ τ : Type) [Finite σ] (p : MvPolynomial σ ℂ) (g : σ → MvPolynomial τ ℂ) (n : ℕ),
    (∀ i, (g i).totalDegree ≤ 1) → PEqualNP.Gct.HasBorderDetExpression p n →
    PEqualNP.Gct.HasBorderDetExpression (MvPolynomial.bind₁ g p) n

/-- The recorded statement of L-gct-057. -/
def Stmt057 : Prop :=
  ∀ R m0 : ℕ, ∃ (m r d : ℕ) (G : MvPolynomial (Fin d) ℂ)
    (g : Fin m × Fin m → MvPolynomial (Fin d) ℂ), m0 ≤ m ∧ 1 ≤ m ∧ 2 ≤ r ∧ 2 ≤ d ∧
    R * m ^ 2 ≤ (r - 1) * (d - 1) ∧ G.IsHomogeneous r ∧
    (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) ∧
    (∀ i, (g i).totalDegree ≤ 1) ∧ MvPolynomial.bind₁ g (PEqualNP.Gct.permPoly ℂ m) = G

/-- The recorded statement of L-gct-056. -/
def Stmt056 : Prop :=
  ∀ R m0 : ℕ, ∃ m : ℕ, m0 ≤ m ∧ 1 ≤ m ∧ ∀ n : ℕ,
    PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → R * m ^ 2 ≤ n

/-- Assembly of L-gct-057. Take `r = 48 R + 48`, `b = 2 r`, `l = r + 1`, a good row space, its
bound `M`, then `N` from `Arith` and `a = 3 r N`; reindex the variables of the block sum by
`Fin (N * a * b)`, apply L-gct-053 to `C c * blockPoly` on the good subspace, and compose the
affine substitution of `BlockPerm` with the linear section. -/
def AssemblyRestriction : Prop :=
  RowSpaceExists → FewRows → GoodSubspace → BlockPerm → Arith → Stmt053 → Stmt057

/-- Assembly of L-gct-056: use L-gct-057 with `11 R`, carry a border expression of the
permanent to the smooth form by L-gct-023, and apply L-gct-024. -/
def AssemblyBound : Prop :=
  Stmt057 → Stmt024 → Stmt023 → Stmt056

end PEqualNP.Gct.Rung
