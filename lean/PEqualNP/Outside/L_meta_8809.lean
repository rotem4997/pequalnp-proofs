import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8809

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8809

theorem PEqualNP.Outside.L_meta_8809 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1), x4 < x2 + x3 → (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x5 (x2 + x7) = x5 x9 ∪ x5 x10 ∨ x5 (x2 + x7) = x5 x9 ∨ x5 (x2 + x7) = ∅ ∨ x5 (x2 + x7) = x5 x9 ∩ x5 x10) → ∃ x8 ⊆ Finset.range x2, x8.card ≤ x3 + (1 : ℕ) ∧ ∀ (x9 x10 : x1), (∀ x11 ∈ x8, x9 ∈ x5 x11 → x10 ∈ x5 x11) → x9 ∈ x5 x4 → x10 ∈ x5 x4 := by
  intro T a m o V ho hV
  have key : ∀ k, k ≤ m → ∃ F ⊆ Finset.range (a + (m - k)), F.card ≤ k + 1 ∧ ∀ (x y : T), (∀ w ∈ F, x ∈ V w → y ∈ V w) → x ∈ V o → y ∈ V o := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨{o}, ?_, by simp, fun x y h hx => h o (by simp) hx⟩
      intro w hw
      rw [Finset.mem_singleton] at hw
      rw [Finset.mem_range]
      omega
    | succ k ih =>
      intro hk
      obtain ⟨F, hF, hc, hm⟩ := ih (by omega)
      by_cases hg : a + (m - (k + 1)) ∈ F
      · obtain ⟨p, hp, q, hq, e⟩ := hV (m - (k + 1)) (by omega)
        refine ⟨insert p (insert q (F.erase (a + (m - (k + 1))))), ?_, ?_, fun x y h => hm x y fun w hw hx => ?_⟩
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rw [Finset.mem_range]
          rcases hw with rfl | rfl | ⟨h1, h2⟩
          · exact hp
          · exact hq
          · have := Finset.mem_range.1 (hF h2)
            omega
        · have h1 := Finset.card_insert_le p (insert q (F.erase (a + (m - (k + 1)))))
          have h2 := Finset.card_insert_le q (F.erase (a + (m - (k + 1))))
          have h3 := Finset.card_erase_of_mem hg
          have h4 : 0 < F.card := Finset.card_pos.2 ⟨_, hg⟩
          omega
        · by_cases hwg : w = a + (m - (k + 1))
          · subst hwg
            have hp' := h p (by simp)
            have hq' := h q (by simp)
            rcases e with e | e | e | e
            · rw [e] at hx ⊢
              exact hx.imp hp' hq'
            · rw [e] at hx ⊢; exact hp' hx
            · rw [e] at hx; exact hx.elim
            · rw [e] at hx ⊢; exact ⟨hp' hx.1, hq' hx.2⟩
          · exact h w (by simp [hwg, hw]) hx
      · refine ⟨F, ?_, by omega, hm⟩
        intro w hw
        have := Finset.mem_range.1 (hF hw)
        rw [Finset.mem_range]
        have : w ≠ a + (m - (k + 1)) := fun e => hg (e ▸ hw)
        omega
  obtain ⟨F, h1, h2, h3⟩ := key m le_rfl
  refine ⟨F, ?_, h2, h3⟩
  simpa using h1
