import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3241_436
    (cover : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ))
    (stars : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (Finset (Fin x1) × Finset (Fin x2))), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → (∀ x7 ∈ x5, x7.1.Nonempty ∧ x7.2.Nonempty ∧ ∀ x9 ∈ x7.1, ∀ x11 ∈ x7.2, x3 x9 x11) → (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x8 ∈ x10.1 ∧ x9 ∈ x10.2) → ∃ (x9 : List (ℕ × List ℕ)), (∀ x10 ∈ x9, x10.2 ≠ [] ∧ ((x10.1 < x1 ∧ ∀ x12 ∈ x10.2, x1 ≤ x12 ∧ x12 < x1 + x2) ∨ x1 ≤ x10.1 ∧ x10.1 < x1 + x2 ∧ ∀ x12 ∈ x10.2, x12 < x1)) ∧ (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ↔ ∃ x12 ∈ x9, x12.1 = ↑x10 ∧ x1 + ↑x11 ∈ x12.2 ∨ x12.1 = x1 + ↑x11 ∧ ↑x10 ∈ x12.2) ∧ (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x9).sum + x9.length - (1 : ℕ) ≤ (List.map (fun (x10 : Finset (Fin x1) × Finset (Fin x2)) => x10.1.card + x10.2.card) x5).sum - (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
  intro x1 x2 x3 x4 x5 x6 hC hA hF
  obtain ⟨k, A, B, hne, hin, hcov, hcost⟩ := cover x1 x2 x3 x5 hC hA hF
  obtain ⟨L, hL1, hL2, hL3⟩ := stars x1 x2 x3 (List.ofFn (fun i => (A i, B i))) hC
    (by
      intro p hp
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
      subst hi
      exact ⟨(hne i).1, (hne i).2, hin i⟩)
    (by
      intro a b
      constructor
      · intro h
        obtain ⟨i, ha, hb⟩ := hcov a b h
        exact ⟨(A i, B i), List.mem_ofFn.mpr ⟨i, rfl⟩, ha, hb⟩
      · rintro ⟨p, hp, ha, hb⟩
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
        subst hi
        exact hin i a ha b hb)
  have hsum : (List.map (fun (x10 : Finset (Fin x1) × Finset (Fin x2)) => x10.1.card + x10.2.card) (List.ofFn (fun i => (A i, B i)))).sum = ∑ i : Fin k, ((A i).card + (B i).card) := by
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hsum] at hL3
  refine ⟨L, hL1, hL2, ?_⟩
  omega
