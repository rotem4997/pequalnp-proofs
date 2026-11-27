import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_11092 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Sym2 (Fin x1))), (∀ x4 ∈ x3, x4 ∈ x2.edgeSet) → (∀ x5 ∈ x3, ∀ x7 ∈ x3, ∀ x9 ∈ x5, x9 ∈ x7 → x5 = x7) → x3.card ≤ x2.edgeSet.ncard := by
  intro x1 x2 x3 h _
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => h x hx) (Set.toFinite _)
