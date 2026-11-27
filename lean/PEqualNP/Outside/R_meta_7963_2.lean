import Mathlib
import PEqualNP.Defs
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_7963_2
    (h_exists : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)), (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → (∃ (v : Fin (x1 + x2)), (Finset.filter (fun (e : Fin x1 × Fin x2) => Fin.castAdd x2 e.1 = v ∨ Fin.natAdd x1 e.2 = v) x3).card = (1 : ℕ)) → ∃ (v : Fin (x1 + x2)), (Finset.filter (fun (e : Fin x1 × Fin x2) => Fin.castAdd x2 e.1 = v ∨ Fin.natAdd x1 e.2 = v) x3).Nonempty ∧ (Finset.filter (fun (e : Fin x1 × Fin x2) => Fin.castAdd x2 e.1 = v ∨ Fin.natAdd x1 e.2 = v) x3).card = (1 : ℕ))
    (h_shrink : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (x1 + x2)), (Finset.filter (fun (e : Fin x1 × Fin x2) => Fin.castAdd x2 e.1 = v ∨ Fin.natAdd x1 e.2 = v) x3).card = (1 : ℕ) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = (fun (z : Fin (x1 + x2) → Bool) => Decidable.decide (∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true))) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ (PEqualNP.MetaComplexity.circuitFun (x1 + x2) x14 = (fun (z : Fin (x1 + x2) → Bool) => Decidable.decide (∃ e ∈ {e ∈ x3 | ¬ ((fun (e : Fin x1 × Fin x2) => Fin.castAdd x2 e.1 = v ∨ Fin.natAdd x1 e.2 = v) e)}, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true))) ∧ x14.size + (2 : ℕ) ≤ x4.size)
    : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → (Fin (x1 + x2) → Bool) → Bool := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ x8 ∈ x6, x7 (Fin.castAdd x2 x8.1) = Bool.true ∧ x7 (Fin.natAdd x1 x8.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = x6 x3 → (∃ (x10 : Fin (x1 + x2)), (Finset.filter (x5 x10) x3).card = (1 : ℕ)) → (∀ (x11 x12 : Fin (x1 + x2)), x11 ≠ x12 → (Finset.filter (x5 x11) x3).card = (1 : ℕ) → (∃ x15 ∈ x3, x5 x11 x15 ∧ x5 x12 x15) → (3 : ℕ) ≤ (Finset.filter (x5 x12) x3).card) → (∀ (x12 : Fin (x1 + x2)), {x13 ∈ x3 | ¬x5 x12 x13}.Nonempty) → ∃ (x13 : Fin (x1 + x2)), (Finset.filter (x5 x13) x3).Nonempty ∧ ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x14 = x6 ({x15 ∈ x3 | ¬x5 x13 x15}) ∧ x14.size + (Finset.filter (x5 x13) x3).card + (1 : ℕ) ≤ x4.size :=
by
  classical
  intro x1 x2 x3 x4 x5 x6 h4 hAO hcomp hdeg1 hbig hnonempty
  obtain ⟨v, hvne, hvcard⟩ := h_exists x1 x2 x3 h4 hdeg1
  have hcomp' : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = (fun (z : Fin (x1 + x2) → Bool) => Decidable.decide (∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true)) := by
    simpa [x6] using hcomp
  obtain ⟨D, hDmono, hDcomp, hDsize⟩ := h_shrink x1 x2 x3 x4 v hvcard hAO hcomp'
  refine ⟨v, ?_, D, hDmono, ?_, ?_⟩
  · simpa [x5] using hvne
  · simpa [x5, x6] using hDcomp
  · have hc : (Finset.filter (x5 v) x3).card = (1 : ℕ) := by simpa [x5] using hvcard
    have hs : D.size + (2 : ℕ) ≤ x4.size := by simpa [x5, x6] using hDsize
    omega

