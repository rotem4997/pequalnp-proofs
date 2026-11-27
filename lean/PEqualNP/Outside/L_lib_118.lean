import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_118 : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (W : Submodule K V), B.Nondegenerate → (∀ x ∈ W, ∀ y ∈ W, B x y = 0) → 2 * Module.finrank K W ≤ Module.finrank K V := by
  intro K V _ _ _ _ B W hB hW
  have hsub : W ≤ B.orthogonal W := by
    intro x hx y hy
    exact hW y hy x hx
  have h1 := Submodule.finrank_mono hsub
  have h2 := LinearMap.BilinForm.finrank_orthogonal hB W
  have h3 := Submodule.finrank_le W
  omega
