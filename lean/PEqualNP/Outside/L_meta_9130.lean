import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9130 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x2 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x2), Fintype.card { x7 : Fin x2 // x4 x7 x6 } = x1 + (1 : ℕ)) → x2 ≤ x3 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x3 → ∃ (x9 : Fin x3 → Finset (Fin x2)) (x10 : Fin x3 → Finset (Fin x2)), (∀ (x11 : Fin x3), ∀ x12 ∈ x9 x11, ∀ x14 ∈ x10 x11, x4 x12 x14) ∧ (∀ (x11 x12 : Fin x2), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x9 x14 ∧ x12 ∈ x10 x14) ∧ ∑ x11 : Fin x3, ((x9 x11).card + (x10 x11).card) ≤ (100 : ℕ) * x3 + x2 := by
  intro q N M I _ hcard hle hbound
  refine ⟨fun k => if h : k.val < N then Finset.univ.filter (fun p => I p ⟨k.val, h⟩) else ∅,
    fun k => if h : k.val < N then {⟨k.val, h⟩} else ∅, ?_, ?_, ?_⟩
  · intro k p hp l hl
    by_cases h : k.val < N
    · simp only [dif_pos h] at hp hl
      rw [Finset.mem_singleton.1 hl]
      exact (Finset.mem_filter.1 hp).2
    · simp only [dif_neg h] at hp
      exact absurd hp (Finset.notMem_empty _)
  · intro p l hpl
    refine ⟨⟨l.val, lt_of_lt_of_le l.isLt hle⟩, ?_, ?_⟩
    · simp only [dif_pos l.isLt]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpl⟩
    · simp only [dif_pos l.isLt]
      exact Finset.mem_singleton.2 rfl
  · have hterm : ∀ k : Fin M,
        ((if h : k.val < N then Finset.univ.filter (fun p => I p ⟨k.val, h⟩) else ∅ : Finset (Fin N)).card
          + (if h : k.val < N then {⟨k.val, h⟩} else ∅ : Finset (Fin N)).card)
        = (fun i : ℕ => if i < N then q + 2 else 0) k.val := by
      intro k
      by_cases h : k.val < N
      · simp only [dif_pos h, if_pos h, Finset.card_singleton]
        have := hcard ⟨k.val, h⟩
        rw [Fintype.card_subtype] at this
        omega
      · simp only [dif_neg h, if_neg h, Finset.card_empty]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < N then q + 2 else 0) M,
      Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, add_zero]
    have hf : (Finset.range M).filter (fun i => i < N) = Finset.range N := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf, Finset.card_range, smul_eq_mul]
    have : N * (q + 2) = N * (q + 1) + N := by ring
    omega
