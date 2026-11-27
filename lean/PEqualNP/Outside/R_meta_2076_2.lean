import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2076_2
    (large : ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (50 : ℕ) ≤ n →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
        IsLeastAO G C → TopForm G C →
        H ≤ G.deleteEdges ↑(starEdges G C : Set (Sym2 (Fin n))) →
        (∀ (v : Fin n), (H.neighborSet v).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (H.neighborSet v).ncard) →
        H.edgeSet.ncard ≤ c * (C.size + (1 : ℕ)))
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + (1 : ℕ)) :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ))) := by
  obtain ⟨cL, hL⟩ := large
  refine ⟨cL + 25, fun x2 x3 x4 hcyc _hne x7 x8 hleast _htop hsub _hdeg => ?_⟩
  rcases Nat.lt_or_ge x2 50 with hn | hn
  ·

    classical
    set S : Finset (Fin x2) := (Set.toFinite x3.support).toFinset with hSdef
    have hScard : S.card = x3.support.ncard := by
      rw [hSdef, Set.ncard_eq_toFinset_card x3.support (Set.toFinite x3.support)]

    have hSle : S.card ≤ 49 := by
      rw [hScard]
      have h1 : x3.support.ncard ≤ (Set.univ : Set (Fin x2)).ncard :=
        Set.ncard_le_ncard (fun v _ => Set.mem_univ v) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
      have hu : Fintype.card (Fin x2) = x2 := Fintype.card_fin x2
      omega

    have hSsup : S.card ≤ x7.size + 1 := by
      rw [hScard]
      exact support x2 x3 x7 hleast

    have hSubS : ∀ v ∈ S, x3.degree v ≤ S.card - 1 := by
      intro v hv
      have hsub : x3.neighborFinset v ⊆ S.erase v := by
        intro w hw
        have hadj := x3.mem_neighborFinset v w |>.mp hw
        rw [Finset.mem_erase, hSdef]
        exact ⟨(x3.ne_of_adj hadj).symm,
          (Set.toFinite x3.support).mem_toFinset.mpr hadj.mem_support_right⟩
      have hd : x3.degree v = (x3.neighborFinset v).card := rfl
      rw [hd]
      exact le_trans (Finset.card_le_card hsub) (by rw [Finset.card_erase_of_mem hv])
    have hZero : ∀ v : Fin x2, v ∉ S → x3.degree v = 0 := by
      intro v hv
      by_cases hp : 0 < x3.degree v
      · have hmemS : v ∈ S := by
          rw [hSdef]
          exact (Set.toFinite x3.support).mem_toFinset.mpr
            ((x3.degree_pos_iff_mem_support v).mp hp)
        exact absurd hmemS hv
      · omega
    have hSum : ∑ v : Fin x2, x3.degree v = ∑ v ∈ S, x3.degree v := by
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun v _ hmem => hZero v (by simpa using hmem))]

    have hChain : 2 * x3.edgeFinset.card ≤ 48 * (x7.size + 1) := by
      rw [x3.sum_degrees_eq_twice_card_edges.symm, hSum]
      calc ∑ v ∈ S, x3.degree v ≤ ∑ v ∈ S, (48 : ℕ) := Finset.sum_le_sum (fun v hv => by
          have := hSubS v hv
          omega)
        _ = S.card * 48 := by rw [Finset.sum_const, smul_eq_mul]
        _ = 48 * S.card := Nat.mul_comm _ _
      have h48 : 48 * S.card ≤ 48 * (x7.size + 1) := by omega
      omega

    have hFinal : x8.edgeSet.ncard ≤ 25 * (x7.size + 1) := by
      have hSub : x8.edgeSet.ncard ≤ x3.edgeFinset.card := by
        have h1 : x8.edgeSet.ncard ≤ x3.edgeSet.ncard :=
          Set.ncard_le_ncard
            (SimpleGraph.edgeSet_mono (le_trans hsub (x3.deleteEdges_le _))) (Set.toFinite _)
        exact le_trans h1 (by rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset])
      omega
    exact le_trans hFinal (Nat.mul_le_mul_right _ (by omega))
  · exact le_trans (hL x2 x3 hn hcyc _hne x7 x8 hleast _htop hsub _hdeg)
      (Nat.mul_le_mul_right _ (by omega))
