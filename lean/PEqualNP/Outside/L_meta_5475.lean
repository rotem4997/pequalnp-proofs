import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5475 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  refine ⟨⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩], 8⟩, ?_, by decide, by decide⟩, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl <;> simp
  · rintro ⟨⟨gs, o⟩, _, hs, hR⟩
    have hgs : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
    subst hgs
    by_cases h : o < 8
    · interval_cases o <;>
        first
          | exact absurd (hR 0 0) (by decide)
          | exact absurd (hR 1 0) (by decide)
          | exact absurd (hR 0 1) (by decide)
    · have h1 := hR 0 0
      have h2 : (PEqualNP.Represents.oneEach (0 : Fin 4) (0 : Fin 4)).getD o false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [PEqualNP.Represents.oneEach]; omega)]
        rfl
      have h3 : (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[], o⟩
          (PEqualNP.Represents.oneEach (0 : Fin 4) (0 : Fin 4))) = false := h2
      rw [h3] at h1
      exact absurd h1 (by decide)
