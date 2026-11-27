import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4480_1
    (h1 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (i0 : Fin (x1 + x2)) (x11 : Finset (Fin x1 × Fin x2)), x11 = {x9 ∈ x3 | ¬(Fin.castAdd x2 x9.1 = i0 ∨ Fin.natAdd x1 x9.2 = i0)} → (Finset.filter (fun x9 : Fin x1 × Fin x2 => Fin.castAdd x2 x9.1 = i0 ∨ Fin.natAdd x1 x9.2 = i0) x3).card = 1 → x11.card < x3.card)
    (h2 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (i0 : Fin (x1 + x2)) (x11 : Finset (Fin x1 × Fin x2)), x11 = {x9 ∈ x3 | ¬(Fin.castAdd x2 x9.1 = i0 ∨ Fin.natAdd x1 x9.2 = i0)} → (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (Finset.filter (fun x9 : Fin x1 × Fin x2 => Fin.castAdd x2 x9.1 = i0 ∨ Fin.natAdd x1 x9.2 = i0) x3).card = 1 → (x11 = ∅ ∨ ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.TopForm.IsAO2 (x1 + x2) x12 ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x12 x8 = Decidable.decide (∃ x9 ∈ x11, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true))) ∧ x12.size + (x3.card - x11.card) + (1 : ℕ) ≤ x4.size)) :
∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →     x6 x3 x4 →       (∃ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card = (1 : ℕ)) →         ∃ (x10 : Fin (x1 + x2)),           have x11 : Finset (Fin x1 × Fin x2) := {x11 ∈ x3 | ¬x5 x10 x11};           x11.card < x3.card ∧ (x11 = ∅ ∨ ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), x6 x11 x12 ∧ x12.size + (x3.card - x11.card) + (1 : ℕ) ≤ x4.size) :=
  by
    intro x1 x2 x3 x4 x5 x6 hno hx6 hline
    classical
    obtain ⟨i0, hi0⟩ := hline
    refine ⟨i0, ?_, ?_⟩
    · exact h1 x1 x2 x3 i0 _ rfl hi0
    · exact h2 x1 x2 x3 x4 i0 _ rfl hno hx6 hi0
