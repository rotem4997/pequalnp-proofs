import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_533 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → ∃ (M : Finset (Sym2 (Fin n))) (T : Finset (Fin n)), (∀ e ∈ M, e ∈ G.edgeFinset) ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : Fin n, v ∈ e → v ∉ f) ∧ (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card = M.card := by
  intro n G _ ⟨c, hc⟩
  classical
  obtain ⟨T, hT, hmin⟩ : ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      ∀ T' : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T' ∨ v ∈ T') → T.card ≤ T'.card := by
    have hne : ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun T => ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T)).Nonempty :=
      ⟨Finset.univ, by simp⟩
    obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image _ Finset.card hne
    exact ⟨T, (Finset.mem_filter.mp hT).2, fun T' hT' =>
      hmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩
  let N : Fin n → Finset (Fin n) := fun v => Finset.univ.filter (fun w => G.Adj v w ∧ w ∉ T)
  have hNmem : ∀ v w, w ∈ N v ↔ (G.Adj v w ∧ w ∉ T) := fun v w => by simp [N]
  have key : ∀ (k : Bool) (S : Finset (Fin n)), S ⊆ T → (∀ v ∈ S, c v = k) →
      S.card ≤ (S.biUnion N).card := by
    intro k S hS hk
    have hcov : ∀ u v, G.Adj u v → u ∈ T →
        u ∈ (T \ S) ∪ S.biUnion N ∨ v ∈ (T \ S) ∪ S.biUnion N := by
      intro u v huv hu
      by_cases huS : u ∈ S
      · have hvS : v ∉ S := fun h => hc u v huv ((hk u huS).trans (hk v h).symm)
        right
        by_cases hvT : v ∈ T
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvT, hvS⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨u, huS, (hNmem u v).mpr ⟨huv, hvT⟩⟩)
      · left
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, huS⟩)
    have h1 := hmin _ (fun u v huv => by
      rcases hT u v huv with h | h
      · exact hcov u v huv h
      · exact (hcov v u huv.symm h).symm)
    have h2 := Finset.card_union_le (T \ S) (S.biUnion N)
    have h3 := Finset.card_sdiff_add_card_eq_card hS
    omega
  have hall : ∀ S : Finset (Fin n), S ⊆ T → S.card ≤ (S.biUnion N).card := by
    intro S hS
    have ha := key false (S.filter (fun v => c v = false))
      ((Finset.filter_subset _ _).trans hS) (by simp)
    have hb := key true (S.filter (fun v => ¬ c v = false))
      ((Finset.filter_subset _ _).trans hS) (by simp)
    have hd : Disjoint ((S.filter (fun v => c v = false)).biUnion N)
        ((S.filter (fun v => ¬ c v = false)).biUnion N) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨a, haS, haw⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨b, hbS, hbw⟩ := Finset.mem_biUnion.mp h2
      have h3 := hc a w ((hNmem a w).mp haw).1
      have h4 := hc b w ((hNmem b w).mp hbw).1
      have h5 := (Finset.mem_filter.mp haS).2
      have h6 := (Finset.mem_filter.mp hbS).2
      cases hw : c w <;> cases hca : c a <;> cases hcb : c b <;> simp_all
    have hsub : (S.filter (fun v => c v = false)).biUnion N ∪
        (S.filter (fun v => ¬ c v = false)).biUnion N ⊆ S.biUnion N :=
      Finset.union_subset
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd] at hcard
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun v => c v = false)
    omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun v : {v // v ∈ T} => N v.1)).mp (by
    intro s
    have h := hall (s.map (Function.Embedding.subtype _)) (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
      exact y.2)
    rw [Finset.card_map] at h
    refine h.trans (Finset.card_le_card ?_)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_biUnion.mpr ⟨z, hz, hxy⟩)
  have hf' : ∀ v : {v // v ∈ T}, G.Adj v.1 (f v) ∧ f v ∉ T := fun v => (hNmem _ _).mp (hf v)
  refine ⟨T.attach.image (fun v => s(v.1, f v)), T, ?_, ?_, hT, ?_⟩
  · intro e he
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hf' v).1
  · intro e he e' he' hne x hx hx'
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp he'
    have hvw : v ≠ w := fun h => hne (by rw [h])
    rw [Sym2.mem_iff] at hx hx'
    rcases hx with h1 | h1 <;> rcases hx' with h2 | h2
    · exact hvw (Subtype.ext (h1.symm.trans h2))
    · exact (hf' w).2 (by rw [← h2, h1]; exact v.2)
    · exact (hf' v).2 (by rw [← h1, h2]; exact w.2)
    · exact hvw (hinj (h1.symm.trans h2))
  · rw [Finset.card_image_of_injective, Finset.card_attach]
    intro v w h
    have h : s(v.1, f v) = s(w.1, f w) := h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Subtype.ext h1
    · exact absurd v.2 (by rw [h1]; exact (hf' w).2)
