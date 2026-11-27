import PEqualNP.Defs
import PEqualNP.Gct.Helpers.CornerLemma

/-! L-gct-169, the corner lemma. A linear space of `4 × 4` complex matrices of dimension at least
seven on which the permanent vanishes contains, for any two rows and any two columns, a nonzero
member vanishing on both rows or a nonzero member vanishing on both columns. Proof: the members
vanishing on the corner block of the chosen rows and columns form a space of dimension at least
three, on which the permanent is the product of the `2 × 2` permanents of the two complementary
blocks; one factor vanishes on the whole space, and a space on which a `2 × 2` permanent
vanishes has dimension at most two, so a nonzero member also vanishes on that block. -/

theorem PEqualNP.Gct.L169 : ∀ W : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ w ∈ W, MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = 0) → 7 ≤ Module.finrank ℂ W → ∀ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ → j₁ ≠ j₂ → (∃ w ∈ W, w ≠ 0 ∧ ∀ j : Fin 4, w (i₁, j) = 0 ∧ w (i₂, j) = 0) ∨ (∃ w ∈ W, w ≠ 0 ∧ ∀ i : Fin 4, w (i, j₁) = 0 ∧ w (i, j₂) = 0) :=
  PEqualNP.Gct.Helpers.Corner.main
