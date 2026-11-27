import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3000 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ x9 ∉ x7, ∃ (x11 : Fin x2), x3 x11 x9 ∧ ∀ x12 ∈ x7, ¬x3 x11 x12 := by
  intro x1 x2 x3 x4 h1 h2 S hS l hl
  by_contra hcon
  push_neg at hcon
  have hc := h1 l
  rw [Fintype.card_subtype] at hc
  have hsub : (Finset.univ.filter (fun p => x3 p l)) ⊆ S.biUnion (fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨m, hm, hpm⟩ := hcon p hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, hm, hp, hpm⟩
  have hone : ∀ m ∈ S, (Finset.univ.filter (fun p => x3 p l ∧ x3 p m)).card ≤ 1 := by
    intro m hm
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    obtain ⟨n, -, hu⟩ := h2 a b hab
    have e1 := hu l ⟨ha.1, hb.1⟩
    have e2 := hu m ⟨ha.2, hb.2⟩
    exact hl (by rw [e1, ← e2]; exact hm)
  have h3 := Finset.card_le_card hsub
  rw [hc] at h3
  have h4 := Finset.card_biUnion_le (s := S) (t := fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m))
  have h5 := Finset.sum_le_card_nsmul S _ 1 hone
  simp only [smul_eq_mul, mul_one] at h5
  omega
