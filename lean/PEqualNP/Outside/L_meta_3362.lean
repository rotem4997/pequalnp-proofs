import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro x1 x2 x3 R _ hcol huniq A B hin hcov
  have h1 : ∀ t, (A t).card * (B t).card ≤ (A t).card + (B t).card := by
    intro t
    have h : (A t).card ≤ 1 ∨ (B t).card ≤ 1 := by
      by_contra hc
      push_neg at hc
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc.1
      obtain ⟨c, hc1, d, hd, hcd⟩ := Finset.one_lt_card.mp hc.2
      exact hcd ((huniq a b hab).unique ⟨hin t a ha c hc1, hin t b hb c hc1⟩
        ⟨hin t a ha d hd, hin t b hb d hd⟩)
    rcases h with h | h
    · have := Nat.mul_le_mul_right (B t).card h
      omega
    · have := Nat.mul_le_mul_left (A t).card h
      omega
  have hS : (Finset.univ.filter (fun p : Fin x1 × Fin x1 => R p.1 p.2)).card = x1 * x2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    have hy : ∀ y : Fin x1, (∑ x : Fin x1, if R x y then 1 else 0) = x2 := by
      intro y
      rw [← Finset.card_filter, ← Fintype.card_subtype]
      convert hcol y
    simp [hy]
  have hsub : (Finset.univ.filter (fun p : Fin x1 × Fin x1 => R p.1 p.2)) ⊆
      Finset.univ.biUnion (fun t => A t ×ˢ B t) := by
    intro p hp
    obtain ⟨t, h1, h2⟩ := hcov p.1 p.2 (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, Finset.mem_product.mpr ⟨h1, h2⟩⟩
  calc x1 * x2 = _ := hS.symm
    _ ≤ (Finset.univ.biUnion (fun t => A t ×ˢ B t)).card := Finset.card_le_card hsub
    _ ≤ ∑ t, (A t ×ˢ B t).card := Finset.card_biUnion_le
    _ ≤ ∑ t, ((A t).card + (B t).card) :=
        Finset.sum_le_sum (fun t _ => by rw [Finset.card_product]; exact h1 t)
