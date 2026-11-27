import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5765

lemma main_proof :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : Finset (Fin x1 ⊕ Fin x2))
      (x6 : Fin x1 ⊕ Fin x2 → Finset (Fin x1 × Fin x2)) (x7 x8 : ℕ),
      x4 ⊆ x3 →
      (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →
      (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →
      (∀ x12 ∈ x3, ∃ x14 ∈ x5, x12 ∈ x6 x14) →
      (∀ x13 ∈ x5, ∀ x15 ∈ x6 x13, x13 = Sum.inl x15.1 ∨ x13 = Sum.inr x15.2) →
      ∑ x14 ∈ x5, (x6 x14).card ≤ x7 + x8 →
      x5.card ≤ x7 →
      x3.card + x4.card ≤ (2 : ℕ) * x7 + x8 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hsub hmatch1 hmatch2 hcov hinc hsum hx5
  have hx3_sub : x3 ⊆ x5.biUnion x6 := by
    intro e he
    rw [Finset.mem_biUnion]
    exact hcov e he
  have hx3_le : x3.card ≤ x7 + x8 :=
    (Finset.card_le_card hx3_sub).trans (Finset.card_biUnion_le.trans hsum)
  have hx4_le : x4.card ≤ x5.card := by
    have hmap : ∀ e ∈ x4, ∃ v ∈ x5, e ∈ x6 v := fun e he => hcov e (hsub he)
    let f : Fin x1 × Fin x2 → Fin x1 ⊕ Fin x2 := fun e =>
      if h : ∃ v ∈ x5, e ∈ x6 v then Classical.choose h else Sum.inl e.1
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro e he
      have h : ∃ v ∈ x5, e ∈ x6 v := hmap e he
      simp only [f, dif_pos h]
      exact (Classical.choose_spec h).1
    · intro e1 he1 e2 he2 hfeq
      have h1 : ∃ v ∈ x5, e1 ∈ x6 v := hmap e1 he1
      have h2 : ∃ v ∈ x5, e2 ∈ x6 v := hmap e2 he2
      have hf1 : f e1 = Classical.choose h1 := by simp only [f, dif_pos h1]
      have hf2 : f e2 = Classical.choose h2 := by simp only [f, dif_pos h2]
      set v := Classical.choose h1
      have hv5 : v ∈ x5 := (Classical.choose_spec h1).1
      have hv1 : e1 ∈ x6 v := (Classical.choose_spec h1).2
      have hv2 : e2 ∈ x6 v := by
        have hv_eq : Classical.choose h2 = v := by rw [← hf2, ← hfeq, hf1]
        rw [← hv_eq]
        exact (Classical.choose_spec h2).2
      rcases hinc v hv5 e1 hv1 with h1l | h1r <;> rcases hinc v hv5 e2 hv2 with h2l | h2r
      · exact hmatch1 e1 he1 e2 he2 (Sum.inl.inj (h1l.symm.trans h2l))
      · exact absurd (h1l.symm.trans h2r) (by simp)
      · exact absurd (h1r.symm.trans h2l) (by simp)
      · exact hmatch2 e1 he1 e2 he2 (Sum.inr.inj (h1r.symm.trans h2r))
  omega

end PEqualNP.Outside.L_meta_5765

theorem PEqualNP.Outside.L_meta_5765 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : Finset (Fin x1 ⊕ Fin x2)) (x6 : Fin x1 ⊕ Fin x2 → Finset (Fin x1 × Fin x2)) (x7 x8 : ℕ), x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → (∀ x12 ∈ x3, ∃ x14 ∈ x5, x12 ∈ x6 x14) → (∀ x13 ∈ x5, ∀ x15 ∈ x6 x13, x13 = Sum.inl x15.1 ∨ x13 = Sum.inr x15.2) → ∑ x14 ∈ x5, (x6 x14).card ≤ x7 + x8 → x5.card ≤ x7 → x3.card + x4.card ≤ (2 : ℕ) * x7 + x8 :=
  PEqualNP.Outside.L_meta_5765.main_proof
