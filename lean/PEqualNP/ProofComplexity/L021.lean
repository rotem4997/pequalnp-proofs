import PEqualNP.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

namespace PEqualNP.ProofComplexity

/-- L-pcx-021: the bit pigeonhole formula is unsatisfiable with more pigeons than holes. -/
theorem L021 : ∀ m l : ℕ, 2 ^ l < m → ¬ PEqualNP.ProofComplexity.Satisfiable (PEqualNP.ProofComplexity.BPHP m l) := by
  rintro m l hlm ⟨a, ha⟩
  have hinj : Function.Injective (fun (i : Fin m) (b : Fin l) => a (i, b)) := by
    intro i i' h
    by_contra hne
    obtain ⟨lit, hl, hal⟩ := ha _ ⟨i, i', fun b => a (i, b), hne, rfl⟩
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hl
      simp at hal
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hl
      have hb : a (i, b) = a (i', b) := congrFun h b
      dsimp only at hal
      rw [← hb] at hal
      simp at hal
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

end PEqualNP.ProofComplexity
