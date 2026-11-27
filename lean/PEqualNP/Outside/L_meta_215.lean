import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Cover215

private theorem cardStep {α : Type*} [DecidableEq α] (U I C : Finset α) (hIU : I ⊆ U)
    (h : C.card ≤ ((C ∪ I) ∩ U).card) :
    (U ∪ C).card + (I ∩ C).card ≤ U.card + I.card := by
  have hsplit : (C ∪ I) ∩ U = (U ∩ C) ∪ I := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hc | hi, hu⟩
      · exact Or.inl ⟨hu, hc⟩
      · exact Or.inr hi
    · rintro (⟨hu, hc⟩ | hi)
      · exact ⟨Or.inl hc, hu⟩
      · exact ⟨Or.inr hi, hIU hi⟩
  have hinter : U ∩ C ∩ I = I ∩ C := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun ⟨⟨_, hc⟩, hi⟩ => ⟨hi, hc⟩, fun ⟨hi, hc⟩ => ⟨⟨hIU hi, hc⟩, hi⟩⟩
  rw [hsplit] at h
  have h1 := Finset.card_union_add_card_inter U C
  have h2 := Finset.card_union_add_card_inter (U ∩ C) I
  rw [hinter] at h2
  omega

end PEqualNP.Outside.Cover215

theorem PEqualNP.Outside.L_meta_215 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)), (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (∀ w : Fin n, ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t ∧ w ∈ S) → n ≤ 2 * t := by
  classical
  intro n t G hlower hvertex
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨C₀, hcover₀, hcard₀, _⟩ := hvertex 0
    -- U and I are the union and intersection of the minimum covers chosen so far.
    -- Every neighbour of a vertex outside U belongs to I.
    have accumulate (W : Finset (Fin (n + 1))) :
        ∃ U I : Finset (Fin (n + 1)), W ⊆ U ∧ I ⊆ U ∧
          (∀ u v, G.Adj u v → u ∉ U → v ∈ I) ∧ U.card + I.card ≤ 2 * t := by
      induction W using Finset.induction_on with
      | empty =>
        refine ⟨C₀, C₀, Finset.empty_subset _, fun _ h => h, ?_, by omega⟩
        intro u v huv hu
        exact (hcover₀ u v huv).resolve_left hu
      | insert w W _ ih =>
        obtain ⟨U, I, hWU, hIU, hedge, hsize⟩ := ih
        obtain ⟨C, hcover, hc, hw⟩ := hvertex w
        have covers : ∀ u v, G.Adj u v → u ∈ (C ∪ I) ∩ U ∨ v ∈ (C ∪ I) ∩ U := by
          intro u v huv
          by_cases hu : u ∈ U
          · by_cases hv : v ∈ U
            · rcases hcover u v huv with h | h
              · exact Or.inl (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, hu⟩)
              · exact Or.inr (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, hv⟩)
            · have hi := hedge v u huv.symm hv
              exact Or.inl (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hi, hu⟩)
          · have hi := hedge u v huv hu
            exact Or.inr (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hi, hIU hi⟩)
        have hmin := hlower ((C ∪ I) ∩ U) covers
        refine ⟨U ∪ C, I ∩ C, ?_, ?_, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_union_right _ hw
          · exact Finset.mem_union_left _ (hWU hi)
        · intro i hi
          exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2
        · intro u v huv hu
          have hU : u ∉ U := fun h => hu (Finset.mem_union_left _ h)
          have hC : u ∉ C := fun h => hu (Finset.mem_union_right _ h)
          exact Finset.mem_inter.mpr ⟨hedge u v huv hU, (hcover u v huv).resolve_left hC⟩
        · exact (PEqualNP.Outside.Cover215.cardStep U I C hIU (hc ▸ hmin)).trans hsize
    obtain ⟨U, I, hU, _, _, bound⟩ := accumulate Finset.univ
    have hcard := Finset.card_le_card hU
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
