import Mathlib
import PEqualNP.Defs

-- Cut of the multi-junk open core by the size of a neighbourhood cover of U*.
-- hNear: in a graph with no cycle shorter than 5, the edges having an endpoint adjacent to a
-- vertex of S number at most S.card times (size + 1) for a least circuit (support bound).
-- hCore: the same core, where U* has no cover by the neighbourhoods of 16 vertices
-- up to 16 (size + 1) missed edges; a cover of size at most 4 is such a cover.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5246_381
    (hNear :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO G C →
        ∀ (S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))), E ⊆ G.edgeFinset →
        (∀ e ∈ E, ∃ (p : Fin n) (q : Fin n), e = s(p, q) ∧
          ((∃ z ∈ S, G.Adj p z) ∨ ∃ z ∈ S, G.Adj q z)) →
        E.card ≤ S.card * (C.size + (1 : ℕ)))
    (hCore :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
          (¬∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
          (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
            x12.card ≤ (16 : ℕ) ∧ x13.card ≤ (16 : ℕ) * (x7.size + (1 : ℕ)) ∧
            ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
              ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
                ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
          (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (¬∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, hc⟩ := hCore
  refine ⟨max 32 c, ?_⟩
  intro x2 x3 x4 hg he x7 hL hT hj hdom _hno
  by_cases hcov : ∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
      x12.card ≤ (16 : ℕ) ∧ x13.card ≤ (16 : ℕ) * (x7.size + (1 : ℕ)) ∧
      ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
        ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
          ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)
  · obtain ⟨S, missed, hS, hm, hcv⟩ := hcov
    have hKnownSub : PEqualNP.TopForm.Ustar x3 x7 \ missed ⊆ x3.edgeFinset := fun _ hk =>
      Finset.sdiff_subset ((Finset.mem_sdiff.mp hk).1)
    have hk := hNear x2 x3 hg x7 hL S (PEqualNP.TopForm.Ustar x3 x7 \ missed) hKnownSub (by
      intro e hk
      obtain ⟨hu, hnm⟩ := Finset.mem_sdiff.mp hk
      exact (hcv e hu).resolve_left hnm)
    have hsub : PEqualNP.TopForm.Ustar x3 x7 ⊆
        (PEqualNP.TopForm.Ustar x3 x7 \ missed) ∪ missed := by
      intro e hu
      by_cases hem : e ∈ missed
      · exact Finset.mem_union_right _ hem
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, hem⟩)
    calc (PEqualNP.TopForm.Ustar x3 x7).card
        ≤ (PEqualNP.TopForm.Ustar x3 x7 \ missed).card + missed.card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ 16 * (x7.size + 1) + 16 * (x7.size + 1) :=
          Nat.add_le_add (hk.trans (Nat.mul_le_mul_right _ hS)) hm
      _ = 32 * (x7.size + 1) := by omega
      _ ≤ max 32 c * (x7.size + 1) := Nat.mul_le_mul_right _ (le_max_left _ _)
  · exact (hc x2 x3 hg he x7 hL hT hj hdom hcov).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))
