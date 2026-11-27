import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_728_aux

theorem extend (n : ℕ) (G : SimpleGraph (Fin n)) (K : Set (Fin n))
    (hK : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v) :
    ∃ I : Set (Fin n), K ⊆ I ∧ (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
      (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) := by
  classical
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun s : Finset (Fin n) =>
      (∀ x ∈ K, x ∈ s) ∧ ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v)) Finset.card
    ⟨Finset.univ.filter (fun x => x ∈ K), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun x hx => hx, fun u hu v hv => hK u hu v hv⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hmax
  refine ⟨{x | x ∈ s}, fun x hx => hs.1 x hx, fun u hu v hv => hs.2 u hu v hv, ?_⟩
  intro v hv
  by_contra hc
  push_neg at hc
  have h := hmax (insert v s) ⟨fun x hx => Finset.mem_insert_of_mem (hs.1 x hx), by
    intro a ha b hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact G.irrefl
    · exact hc b hb
    · exact fun h => hc a ha h.symm
    · exact hs.2 a ha b hb⟩
  rw [Finset.card_insert_of_notMem (show v ∉ s from hv)] at h
  omega

end PEqualNP.Outside.L_meta_728_aux

theorem PEqualNP.Outside.L_meta_728 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop),
  (∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
  ((∃ W K : Set (Fin n),
      (∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v) ∧ Disjoint K W ∧
      (∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v) ∧
      ∀ v, v ∉ W → v ∉ K → ∃ k ∈ K, D v k) ↔
   (∃ I : Set (Fin n),
      (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) ∧
      ∀ u v, u ∉ I → v ∉ I → (∀ w ∈ I, ¬ D u w) → (∀ w ∈ I, ¬ D v w) → ¬ G.Adj u v)) := by
  intro n G D hG hD
  constructor
  · rintro ⟨W, K, hW, hKW, hK, hcov⟩
    obtain ⟨I, hKI, hI, hmax⟩ := PEqualNP.Outside.L_meta_728_aux.extend n G K hK
    refine ⟨I, hI, hmax, ?_⟩
    intro u v hu hv hu2 hv2
    have hu3 : u ∈ W := by
      by_contra h
      obtain ⟨k, hk, hd⟩ := hcov u h (fun h' => hu (hKI h'))
      exact hu2 k (hKI hk) hd
    have hv3 : v ∈ W := by
      by_contra h
      obtain ⟨k, hk, hd⟩ := hcov v h (fun h' => hv (hKI h'))
      exact hv2 k (hKI hk) hd
    exact hW u hu3 v hv3
  · rintro ⟨I, hI, hmax, hS⟩
    refine ⟨{v | v ∉ I ∧ ∀ w ∈ I, ¬ D v w}, I, ?_, ?_, hI, ?_⟩
    · intro u hu v hv
      exact hS u v hu.1 hv.1 hu.2 hv.2
    · rw [Set.disjoint_left]
      intro a ha hb
      exact hb.1 ha
    · intro v hv hvI
      by_contra h
      push_neg at h
      exact hv ⟨hvI, h⟩
