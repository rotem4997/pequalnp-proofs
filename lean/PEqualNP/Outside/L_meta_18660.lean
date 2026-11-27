import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18660 :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)),   have x3 : Finset (Fin x1) → Prop := fun (x3 : Finset (Fin x1)) => ∀ (x4 x5 : Fin x1), x2.Adj x4 x5 → x4 ∈ x3 ∨ x5 ∈ x3;   ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → ∃ (x6 : Finset (Fin x1)), x3 x6 ∧ (∀ (x7 : Finset (Fin x1)), x3 x7 → x6.card ≤ x7.card) ∧ (∀ x7 ∈ x6, ∃ x9 ∉ x6, x2.Adj x7 x9) ∧ (∃ x7 ∈ x6, ∃ x8 ∈ x6, x2.Adj x7 x8) ∧ ∀ x7 ∈ x6, ∀ x9 ∈ x6, x2.Adj x7 x9 → (x2.edgeSet \ (x2.incidenceSet x7 ∪ x2.incidenceSet x9)).ncard + ((x6.erase x7).erase x9).card + (7 : ℕ) = x2.edgeSet.ncard + x6.card := by
  classical
  intro n G covers notColor cubic
  have existsCover : ∃ k : ℕ, ∃ S : Finset (Fin n), covers S ∧ S.card = k :=
    ⟨n, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _), Fintype.card_fin n⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec existsCover
  have minSize (T : Finset (Fin n)) (hT : covers T) : S.card ≤ T.card := by
    rw [hcard]
    exact Nat.find_min' existsCover ⟨T, hT, rfl⟩
  refine ⟨S, hS, minSize, ?_, ?_, ?_⟩
  · intro u hu
    by_contra! closed
    have erased : covers (S.erase u) := by
      intro a b ab
      rcases hS a b ab with ha | hb
      · by_cases r : a = u
        · subst a
          have hb : b ∈ S := by
            by_contra hb
            exact closed b hb ab
          exact Or.inr (Finset.mem_erase.mpr ⟨ab.ne.symm, hb⟩)
        · exact Or.inl (Finset.mem_erase.mpr ⟨r, ha⟩)
      · by_cases r : b = u
        · subst b
          have ha : a ∈ S := by
            by_contra ha
            exact closed a ha ab.symm
          exact Or.inl (Finset.mem_erase.mpr ⟨ab.ne, ha⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨r, hb⟩)
    have less := Finset.card_erase_lt_of_mem hu
    exact (not_le_of_gt less) (minSize _ erased)
  · by_contra! independent
    apply notColor
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ S then (0 : Fin 2) else 1) ?_⟩
    intro u v adj
    rcases hS u v adj with hu | hv
    · have hv : v ∉ S := fun hv => independent u hu v hv adj
      simp [hu, hv]
    · have hu : u ∉ S := fun hu => independent u hu v hv adj
      simp [hv, hu]
  · intro u hu v hv adj
    have du := cubic u ⟨v, adj⟩
    have dv := cubic v ⟨u, adj.symm⟩
    have iu : (G.incidenceSet u).ncard = 3 := by
      rwa [G.ncard_incidenceSet, ← G.ncard_neighborSet]
    have iv : (G.incidenceSet v).ncard = 3 := by
      rwa [G.ncard_incidenceSet, ← G.ncard_neighborSet]
    have unionCard := Set.ncard_union_add_ncard_inter (G.incidenceSet u) (G.incidenceSet v)
    rw [G.incidenceSet_inter_incidenceSet_of_adj adj, Set.ncard_singleton, iu, iv] at unionCard
    have removed := Set.ncard_sdiff_add_ncard_of_subset
      (Set.union_subset (G.incidenceSet_subset u) (G.incidenceSet_subset v))
    have eraseU := Finset.card_erase_add_one hu
    have eraseV := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨adj.ne.symm, hv⟩)
    omega
