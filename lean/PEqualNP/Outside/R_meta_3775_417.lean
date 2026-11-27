import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- If only a bounded number of independent edge pairs can be packed, their endpoints
-- cover the exceptional edges by a bounded family of neighborhoods.
theorem PEqualNP.Outside.R_meta_3775_417
    (packing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (k : ℕ),
      (∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) → IsLeastAO G C →
      (Ustar G C).card ≤ 2*k*(C.size+1) ∨
        ∃ M : Finset (Sym2 (Fin n)), M ⊆ Ustar G C ∧ k < M.card ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ u ∈ e, ∀ v ∈ f, ¬ G.Adj u v)
    (largePacking : ∃ (k x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
      (∃ M : Finset (Sym2 (Fin x2)), M ⊆ Ustar x3 x7 ∧ k < M.card ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ u ∈ e, ∀ v ∈ f, ¬ x3.Adj u v) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k,c,hc⟩ := largePacking
  refine ⟨max (2*k) c, ?_⟩
  intro n G _ hg he C hL hT hJ hNest hNo
  rcases packing n G C k hg hL with hSmall | hPack
  · exact hSmall.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · exact (hc n G hg he C hL hT hJ hNest hNo hPack).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))
