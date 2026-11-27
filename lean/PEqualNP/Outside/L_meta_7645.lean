import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7645 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∀ (x2 : Fin (14 : ℕ) → Bool), x1 x2 → (∀ x4 ≤ x2, x1 x4 → x4 = x2) → ∃ x5 ∈ [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)], (fun (x6 : Fin (14 : ℕ)) => x5.testBit ↑x6) = x2 := by
  intro x1 x2 h1 hmin
  obtain ⟨a, b, hmem, ha, hb⟩ := h1
  have key : ∀ a b : Fin 14, 14 * (a : ℕ) + (b : ℕ) ∈ [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95] →
      ∃ x5 ∈ [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112],
        (fun (x6 : Fin 14) => x5.testBit ↑x6) = (fun i : Fin 14 => decide (i = a ∨ i = b)) := by
    decide +kernel
  have hle : (fun i : Fin 14 => decide (i = a ∨ i = b)) ≤ x2 := by
    intro i
    by_cases h : i = a
    · subst h; simp [ha]
    · by_cases h' : i = b
      · subst h'; simp [hb]
      · simp [h, h']
  have heq := hmin _ hle ⟨a, b, hmem, by simp, by simp⟩
  rw [← heq]
  exact key a b hmem
