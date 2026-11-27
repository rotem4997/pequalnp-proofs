import Mathlib
import PEqualNP.Defs
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_7866_1
    (h_edgecard : ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) (x6 : Finset (Sym2 (Fin x2))), (∀ e ∈ x6, e ∈ x3.edgeSet) → (∀ e ∈ x6, ∀ f ∈ x6, ∀ v ∈ e, v ∈ f → e = f) → x6.card ≤ x3.edgeSet.ncard)
    (h_bound : ∃ (c : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ a b, x3.Adj a b) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → x3.edgeSet.ncard + x3.edgeSet.ncard ≤ x5.size + (1 : ℕ) + c * (x2 + (1 : ℕ)).sqrt)
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt :=
by
  classical
  obtain ⟨c, hc⟩ := h_bound
  refine ⟨c, ?_⟩
  intro x2 x3 inst x5 x6 he hnon hleast htop hjunk hx6 hdisj
  have hx6le := h_edgecard x2 x3 x6 hx6 hdisj
  have hcval := hc x2 x3 x5 hnon hleast htop hjunk
  omega

