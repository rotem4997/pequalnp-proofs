import Mathlib

/-!
Plan module for the elementary proof of the two-row case of conjecture S (hub row L-gct-143),
after the paper proof in `notes/gct-086-S-p2-elementary.md`. It holds the shared definitions and
the statements of the pieces as `Prop`s; each piece is proved in its own file.
-/

namespace PEqualNP.Gct.Helpers.S2Elem

/-- The columnwise symmetric product of two `2 × q` matrices. -/
def colperm {q : ℕ} (v w : Fin 2 × Fin q → ℂ) : Fin q → ℂ :=
  fun j => v (0, j) * w (1, j) + w (0, j) * v (1, j)

/-- The columnwise sum of the two rows. -/
def phi {q : ℕ} (w : Fin 2 × Fin q → ℂ) : Fin q → ℂ :=
  fun j => w (0, j) + w (1, j)

/-- Admissible: all entry sums vanish and the space is isotropic for the sum of `colperm`. -/
def Admissible {q : ℕ} (R : Submodule ℂ (Fin 2 × Fin q → ℂ)) : Prop :=
  (∀ w ∈ R, ∑ j, phi w j = 0) ∧ ∀ w ∈ R, ∀ w' ∈ R, ∑ j, colperm w w' j = 0

/-- The span of the columnwise sums and columnwise products of `R`. -/
def T {q : ℕ} (R : Submodule ℂ (Fin 2 × Fin q → ℂ)) : Submodule ℂ (Fin q → ℂ) :=
  Submodule.span ℂ ({t | ∃ w ∈ R, t = phi w} ∪ {t | ∃ w ∈ R, ∃ w' ∈ R, t = colperm w w'})

/-- Main claim: an admissible space has `dim T(R) ≥ dim R`. -/
def MainClaim : Prop :=
  ∀ (q : ℕ) (R : Submodule ℂ (Fin 2 × Fin q → ℂ)), Admissible R →
    Module.finrank ℂ R ≤ Module.finrank ℂ (T R)

/-- Circuit lemma: among the vectors of `Z` supported in `N` with nonzero sum, one of minimal
support spans every vector of `Z` supported inside its support. -/
def StmtCircuit : Prop :=
  ∀ (q : ℕ) (Z : Submodule ℂ (Fin q → ℂ)) (N : Finset (Fin q)),
    (∃ z ∈ Z, (∀ j, j ∉ N → z j = 0) ∧ ∑ j, z j ≠ 0) →
    ∃ y ∈ Z, (∀ j, j ∉ N → y j = 0) ∧ ∑ j, y j ≠ 0 ∧
      ∀ x ∈ Z, (∀ j, y j = 0 → x j = 0) → ∃ c : ℂ, x = c • y

/-- Isotropic bound with one extra vector. -/
def StmtIso : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (B : LinearMap.BilinForm ℂ W) (A : Submodule ℂ W) (v : W),
    B.Nondegenerate → B v v ≠ 0 → (∀ a ∈ A, B a v = 0) → (∀ a ∈ A, ∀ a' ∈ A, B a a' = 0) →
    2 * Module.finrank ℂ A + 1 ≤ Module.finrank ℂ W

end PEqualNP.Gct.Helpers.S2Elem
