import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7057 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2], (∀ (x4 x5 : Fin x1), x4 ≠ x5 → ∃! x7 : Fin x1, x2 x4 x7 ∧ x2 x5 x7) → ∀ (x5 : Fin x1) (x6 : Finset (Fin x1)), x5 ∉ x6 → Fintype.card { x8 : Fin x1 // x2 x8 x5 ∧ ∃ x9 ∈ x6, x2 x8 x9 } ≤ x6.card := by
  intro N R _ huniq l S hl
  classical
  rw [Fintype.card_subtype]
  have hch : ∀ p ∈ (Finset.univ.filter fun p => R p l ∧ ∃ m ∈ S, R p m), ∃ m ∈ S, R p m :=
    fun p hp => (Finset.mem_filter.1 hp).2.2
  apply Finset.card_le_card_of_injOn (fun p => if h : ∃ m ∈ S, R p m then h.choose else l)
  · intro p hp
    have h := hch p hp
    simp only [dif_pos h]
    exact h.choose_spec.1
  · intro p hp q hq hpq
    have hp' := Finset.mem_coe.1 hp
    have hq' := Finset.mem_coe.1 hq
    by_contra hne
    have h1 := hch p hp'
    have h2 := hch q hq'
    simp only [dif_pos h1, dif_pos h2] at hpq
    obtain ⟨m, _, hm⟩ := huniq p q hne
    have e1 : l = m := hm l ⟨(Finset.mem_filter.1 hp').2.1, (Finset.mem_filter.1 hq').2.1⟩
    have hq2 : R q h1.choose := by rw [hpq]; exact h2.choose_spec.2
    have e2 : h1.choose = m := hm h1.choose ⟨h1.choose_spec.2, hq2⟩
    have hS := h1.choose_spec.1
    rw [e2, ← e1] at hS
    exact hl hS
