import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2702_aux

open Finset

theorem aux (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (X : Finset (Fin 11))
    (M : Finset (Fin 11 × Fin 11))
    (hX : ∀ p ∈ M, p.1 ∉ X ∧ p.2 ∉ X)
    (hM : ∀ p ∈ M, ∀ q ∈ M, (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) → p = q) :
    (∀ a b : Fin 11, G.Adj a b → a ∈ X ∨ b ∈ X ∨ (a, b) ∈ M ∨ (b, a) ∈ M) →
    ∀ T : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      ∃ A ⊆ X, (∀ a ∈ X \ A, ∀ b ∈ X \ A, ¬ G.Adj a b) ∧
        T.card = A.card + ({v ∈ Finset.univ \ X | ∃ u ∈ X \ A, G.Adj u v} : Finset (Fin 11)).card
          + ({p ∈ M | G.Adj p.1 p.2 ∧
              p.1 ∉ ({v ∈ Finset.univ \ X | ∃ u ∈ X \ A, G.Adj u v} : Finset (Fin 11)) ∧
              p.2 ∉ ({v ∈ Finset.univ \ X | ∃ u ∈ X \ A, G.Adj u v} : Finset (Fin 11))}).card := by
  intro hE T hT
  obtain ⟨hc, hmin⟩ := hT
  have hc' : ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T := fun a b h => by simpa using hc h
  refine ⟨T ∩ X, inter_subset_right, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [mem_sdiff, mem_inter, not_and] at ha hb
    rcases hc' a b hab with h | h
    · exact ha.2 h ha.1
    · exact hb.2 h hb.1
  · generalize hN : ({v ∈ Finset.univ \ X | ∃ u ∈ X \ (T ∩ X), G.Adj u v} : Finset (Fin 11)) = N
    generalize hP : ({p ∈ M | G.Adj p.1 p.2 ∧ p.1 ∉ N ∧ p.2 ∉ N}) = P
    have hNmem : ∀ v, v ∈ N ↔ v ∉ X ∧ ∃ u, u ∈ X ∧ u ∉ T ∧ G.Adj u v := by
      intro v
      rw [← hN]
      simp only [mem_filter, mem_sdiff, mem_univ, true_and, mem_inter, not_and]
      constructor
      · rintro ⟨h1, u, ⟨h2, h3⟩, h4⟩
        exact ⟨h1, u, h2, fun h => h3 h h2, h4⟩
      · rintro ⟨h1, u, h2, h3, h4⟩
        exact ⟨h1, u, ⟨h2, fun h => absurd h h3⟩, h4⟩
    have hPmem : ∀ p, p ∈ P ↔ p ∈ M ∧ G.Adj p.1 p.2 ∧ p.1 ∉ N ∧ p.2 ∉ N := by
      intro p
      rw [← hP]
      simp only [mem_filter]
    have hNT : N ⊆ T := by
      intro v hv
      obtain ⟨_, u, hu, huT, huv⟩ := (hNmem v).1 hv
      rcases hc' u v huv with h | h
      · exact absurd h huT
      · exact h
    apply le_antisymm
    · have hS : G.IsVertexCover
          (((T ∩ X) ∪ N ∪ P.image Prod.fst : Finset (Fin 11)) : Set (Fin 11)) := by
        have key : ∀ a b, G.Adj a b → a ∈ X →
            a ∈ (T ∩ X) ∪ N ∪ P.image Prod.fst ∨ b ∈ (T ∩ X) ∪ N ∪ P.image Prod.fst := by
          intro a b hab haX
          by_cases haT : a ∈ T
          · left
            exact mem_union_left _ (mem_union_left _ (mem_inter.2 ⟨haT, haX⟩))
          · right
            by_cases hbX : b ∈ X
            · have hb : b ∈ T := (hc' a b hab).resolve_left haT
              exact mem_union_left _ (mem_union_left _ (mem_inter.2 ⟨hb, hbX⟩))
            · have hb : b ∈ N := (hNmem b).2 ⟨hbX, a, haX, haT, hab⟩
              exact mem_union_left _ (mem_union_right _ hb)
        intro a b hab
        simp only [mem_coe]
        rcases hE a b hab with h | h | h | h
        · exact key a b hab h
        · exact (key b a hab.symm h).symm
        · by_cases ha : a ∈ N
          · left
            exact mem_union_left _ (mem_union_right _ ha)
          · by_cases hb : b ∈ N
            · right
              exact mem_union_left _ (mem_union_right _ hb)
            · left
              have h1 : (a, b) ∈ P := (hPmem _).2 ⟨h, hab, ha, hb⟩
              exact mem_union_right _ (mem_image.2 ⟨(a, b), h1, rfl⟩)
        · by_cases ha : a ∈ N
          · left
            exact mem_union_left _ (mem_union_right _ ha)
          · by_cases hb : b ∈ N
            · right
              exact mem_union_left _ (mem_union_right _ hb)
            · right
              have h1 : (b, a) ∈ P := (hPmem _).2 ⟨h, hab.symm, hb, ha⟩
              exact mem_union_right _ (mem_image.2 ⟨(b, a), h1, rfl⟩)
      calc T.card ≤ ((T ∩ X) ∪ N ∪ P.image Prod.fst).card := hmin _ hS
        _ ≤ ((T ∩ X) ∪ N).card + (P.image Prod.fst).card := card_union_le _ _
        _ ≤ (T ∩ X).card + N.card + P.card := add_le_add (card_union_le _ _) card_image_le
    · obtain ⟨f, hf⟩ : ∃ f : Fin 11 × Fin 11 → Fin 11,
          ∀ p, f p = if p.1 ∈ T then p.1 else p.2 := ⟨_, fun _ => rfl⟩
      have hfT : ∀ p ∈ P, f p ∈ T := by
        intro p hp
        obtain ⟨_, hadj, _, _⟩ := (hPmem p).1 hp
        by_cases h : p.1 ∈ T
        · rw [hf, if_pos h]
          exact h
        · rw [hf, if_neg h]
          exact (hc' _ _ hadj).resolve_left h
      have hfe : ∀ p, f p = p.1 ∨ f p = p.2 := by
        intro p
        by_cases h : p.1 ∈ T
        · left
          rw [hf, if_pos h]
        · right
          rw [hf, if_neg h]
      have hinj : Set.InjOn f (P : Set (Fin 11 × Fin 11)) := by
        intro p hp q hq hpq
        have hp' := ((hPmem p).1 (mem_coe.1 hp)).1
        have hq' := ((hPmem q).1 (mem_coe.1 hq)).1
        apply hM p hp' q hq'
        rcases hfe p with h1 | h1 <;> rcases hfe q with h2 | h2 <;>
          rw [h1, h2] at hpq <;> tauto
      have hd1 : Disjoint (T ∩ X) N := by
        rw [disjoint_left]
        intro v hv hvN
        exact ((hNmem v).1 hvN).1 (mem_inter.1 hv).2
      have hd2 : Disjoint ((T ∩ X) ∪ N) (P.image f) := by
        rw [disjoint_left]
        intro v hv hvP
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hvP
        obtain ⟨hpM, _, h1, h2⟩ := (hPmem p).1 hp
        rcases mem_union.1 hv with h | h
        · have hx := (mem_inter.1 h).2
          rcases hfe p with e | e
          · rw [e] at hx
            exact (hX p hpM).1 hx
          · rw [e] at hx
            exact (hX p hpM).2 hx
        · rcases hfe p with e | e
          · rw [e] at h
            exact h1 h
          · rw [e] at h
            exact h2 h
      have hsub : (T ∩ X) ∪ N ∪ P.image f ⊆ T := by
        intro v hv
        rcases mem_union.1 hv with h | h
        · rcases mem_union.1 h with h | h
          · exact (mem_inter.1 h).1
          · exact hNT h
        · obtain ⟨p, hp, rfl⟩ := mem_image.1 h
          exact hfT p hp
      have hle := card_le_card hsub
      rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_image_of_injOn hinj] at hle
      exact hle

end PEqualNP.Outside.L_meta_2702_aux

theorem PEqualNP.Outside.L_meta_2702 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj],   have x3 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x4 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ (x5 x6 : Fin (11 : ℕ)), x1.Adj x5 x6 → x5 ∈ x3 ∨ x6 ∈ x3 ∨ (x5, x6) ∈ x4 ∨ (x6, x5) ∈ x4) →     ∀ (x6 : Finset (Fin (11 : ℕ))),       PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x6 →         ∃ x8 ⊆ x3,           (∀ x9 ∈ x3 \ x8, ∀ x11 ∈ x3 \ x8, ¬x1.Adj x9 x11) ∧             have x9 : Finset (Fin (11 : ℕ)) := {x9 ∈ Finset.univ \ x3 | ∃ x10 ∈ x3 \ x8, x1.Adj x10 x9};             have x10 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x10 ∈ x4 | x1.Adj x10.1 x10.2 ∧ x10.1 ∉ x9 ∧ x10.2 ∉ x9};             x6.card = x8.card + x9.card + x10.card := by
  intro x1 x2
  exact PEqualNP.Outside.L_meta_2702_aux.aux x1 _ _
    (by intro p hp; fin_cases hp <;> decide)
    (by intro p hp q hq; fin_cases hp <;> fin_cases hq <;> decide)
