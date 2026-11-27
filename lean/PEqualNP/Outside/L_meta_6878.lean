import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6878 : let x1 : Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x1 : Fin (42 : ℕ) × Fin (42 : ℕ)) => ↑x1.1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x1.2 ∧ (↑x1.2 + (21 : ℕ) - ↑x1.1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ)) := Finset.filter x1 Finset.univ; ∀ (x3 : Finset (Fin (42 : ℕ))), (∀ x4 ∈ x2, x4.1 ∈ x3 ∨ x4.2 ∈ x3) → (21 : ℕ) ≤ x3.card := by
  dsimp only
  intro S h
  have hpair : ∀ i : Fin 21, (⟨i.val, by omega⟩ : Fin 42) ∈ S ∨ (⟨21 + i.val, by omega⟩ : Fin 42) ∈ S := by
    intro i
    refine h (⟨i.val, by omega⟩, ⟨21 + i.val, by omega⟩) ?_
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, i.isLt, Nat.le_add_right _ _, ?_⟩
    have h0 : (21 + i.val + 21 - i.val) % 21 = 0 := by omega
    show (21 + i.val + 21 - i.val) % 21 ∈ [0, 5, 7, 17, 20]
    rw [h0]
    simp
  classical
  have hc : (Finset.univ : Finset (Fin 21)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn
      (fun i : Fin 21 => if (⟨i.val, by omega⟩ : Fin 42) ∈ S then (⟨i.val, by omega⟩ : Fin 42)
        else ⟨21 + i.val, by omega⟩)
    · intro i _
      dsimp only
      split_ifs with h1
      · exact h1
      · exact (hpair i).resolve_left h1
    · intro i _ j _ hij
      dsimp only at hij
      have hv := congrArg Fin.val hij
      apply Fin.ext
      split_ifs at hv <;> simp only [] at hv <;> omega
  simpa using hc
