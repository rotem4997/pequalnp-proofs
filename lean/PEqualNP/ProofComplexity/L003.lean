import PEqualNP.Defs

namespace PEqualNP.ProofComplexity

/-- L-pcx-003: the pigeonhole formula is satisfiable when the pigeons fit. -/
theorem L003 : ∀ m n : ℕ, m ≤ n → PEqualNP.ProofComplexity.Satisfiable (PEqualNP.ProofComplexity.PHP m n) := by
  intro m n hmn
  refine ⟨fun p => decide (p.1.val = p.2.val), ?_⟩
  rintro C (⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩)
  · refine ⟨((i, ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩), true), ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · by_cases h : i.val = j.val
    · refine ⟨((i', j), false), by simp, ?_⟩
      have : i'.val ≠ j.val := fun h' => hii (Fin.ext (h.trans h'.symm))
      simp [this]
    · exact ⟨((i, j), false), by simp, by simp [h]⟩

end PEqualNP.ProofComplexity
