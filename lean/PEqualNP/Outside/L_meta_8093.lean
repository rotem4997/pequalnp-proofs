import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8093

-- potential of a pair of sides: edges inside minus x3 per kept vertex
noncomputable def pot {x1 x2 : ℕ} (x3 : ℕ) (x4 : Finset (Fin x1 × Fin x2))
    (p : Finset (Fin x1) × Finset (Fin x2)) : ℤ := by
  classical
  exact ((x4.filter (fun q => q.1 ∈ p.1 ∧ q.2 ∈ p.2)).card : ℤ) - (x3 : ℤ) * ((p.1.card : ℤ) + p.2.card)

theorem pot_eq {x1 x2 : ℕ} (x3 : ℕ) (x4 : Finset (Fin x1 × Fin x2))
    (p : Finset (Fin x1) × Finset (Fin x2)) :
    pot x3 x4 p = ((x4.filter (fun q => q.1 ∈ p.1 ∧ q.2 ∈ p.2)).card : ℤ) - (x3 : ℤ) * ((p.1.card : ℤ) + p.2.card) := by
  unfold pot
  congr

end PEqualNP.Outside.L_meta_8093

theorem PEqualNP.Outside.L_meta_8093 : ∀ (x1 x2 x3 : ℕ) (x4 : Finset (Fin x1 × Fin x2)),   ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x2)),     have x7 : Finset (Fin x1 × Fin x2) := {x7 ∈ x4 | x7.1 ∈ x5 ∧ x7.2 ∈ x6};     x4.card + x3 * (x5.card + x6.card) ≤ x7.card + x3 * ((Finset.image Prod.fst x4).card + (Finset.image Prod.snd x4).card) ∧ ∀ x8 ⊆ x5, ∀ x10 ⊆ x6, {x12 ∈ x7 | x12.1 ∈ x8 ∧ x12.2 ∈ x10}.card + x3 * ((x5 \ x8).card + (x6 \ x10).card) ≤ x7.card := by
  intro x1 x2 x3 x4
  classical
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset (Fin x1) × Finset (Fin x2)))
    (PEqualNP.Outside.L_meta_8093.pot x3 x4) ⟨(∅, ∅), Finset.mem_univ _⟩
  refine ⟨p.1, p.2, ?_⟩
  dsimp only
  constructor
  · have h := hmax (Finset.image Prod.fst x4, Finset.image Prod.snd x4) (Finset.mem_univ _)
    rw [PEqualNP.Outside.L_meta_8093.pot_eq, PEqualNP.Outside.L_meta_8093.pot_eq] at h
    have hx4 : x4.filter (fun q => q.1 ∈ Finset.image Prod.fst x4 ∧ q.2 ∈ Finset.image Prod.snd x4) = x4 :=
      Finset.filter_true_of_mem (fun q hq => ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩)
    rw [hx4] at h
    dsimp only at h
    zify
    linarith
  · intro x8 h8 x10 h10
    have h := hmax (x8, x10) (Finset.mem_univ _)
    rw [PEqualNP.Outside.L_meta_8093.pot_eq, PEqualNP.Outside.L_meta_8093.pot_eq] at h
    dsimp only at h
    have hf : Finset.filter (fun x12 => x12.1 ∈ x8 ∧ x12.2 ∈ x10)
        (Finset.filter (fun x7 => x7.1 ∈ p.1 ∧ x7.2 ∈ p.2) x4)
        = x4.filter (fun q => q.1 ∈ x8 ∧ q.2 ∈ x10) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro q _
      constructor
      · intro hq
        exact hq.2
      · intro hq
        exact ⟨⟨h8 hq.1, h10 hq.2⟩, hq⟩
    rw [hf]
    have e1 := Finset.card_sdiff_add_card_eq_card h8
    have e2 := Finset.card_sdiff_add_card_eq_card h10
    have e1' : (p.1.card : ℤ) = ((p.1 \ x8).card : ℤ) + (x8.card : ℤ) := by exact_mod_cast e1.symm
    have e2' : (p.2.card : ℤ) = ((p.2 \ x10).card : ℤ) + (x10.card : ℤ) := by exact_mod_cast e2.symm
    rw [e1', e2'] at h
    zify
    linarith
