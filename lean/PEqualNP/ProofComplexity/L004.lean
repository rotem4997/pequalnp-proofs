import PEqualNP.Defs
import Mathlib.Data.Fintype.Card

namespace PEqualNP.ProofComplexity

/-- L-pcx-004: the pigeonhole formula is unsatisfiable with more pigeons than holes. -/
theorem L004 : ∀ m n : ℕ, n < m → ¬ PEqualNP.ProofComplexity.Satisfiable (PEqualNP.ProofComplexity.PHP m n) := by
  rintro m n hnm ⟨a, ha⟩
  have h1 : ∀ i : Fin m, ∃ j : Fin n, a (i, j) = true := by
    intro i
    obtain ⟨l, hl, hal⟩ := ha _ (Or.inl ⟨i, rfl⟩)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨j, hal⟩
  choose f hf using h1
  have hinj : Function.Injective f := by
    intro i i' hfi
    by_contra hne
    obtain ⟨l, hl, hal⟩ := ha _ (Or.inr ⟨i, i', f i, hne, rfl⟩)
    rcases Finset.mem_insert.mp hl with rfl | hl
    · have := hf i
      simp_all
    · rw [Finset.mem_singleton] at hl
      subst hl
      have := hf i'
      rw [← hfi] at this
      simp_all
  have := Fintype.card_le_of_injective f hinj
  simp at this
  omega

end PEqualNP.ProofComplexity
