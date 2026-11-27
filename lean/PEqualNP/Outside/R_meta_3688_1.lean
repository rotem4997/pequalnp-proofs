import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3688_1
    (h1 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2.card →
      (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      ((∃ u : Fin x1, ∀ v : Fin x1, (u, v) ∈ x2 → v = x3 u) ∨ (∃ v : Fin x1, ∀ u : Fin x1, (u, v) ∈ x2 → x3 u = v)) →
      x2.card + x1 ≤ x4.size + (1 : ℕ))
    (h2 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2.card →
      (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      ((∀ u : Fin x1, ∃ v : Fin x1, v ≠ x3 u ∧ (u, v) ∈ x2) ∧ (∀ v : Fin x1, ∃ u : Fin x1, x3 u ≠ v ∧ (u, v) ∈ x2)) →
      x2.card + x1 ≤ x4.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro x1 x2 x3 x4 hcard h2n hc4 hmatch hao hfun
  by_cases hp : (∃ u : Fin x1, ∀ v : Fin x1, (u, v) ∈ x2 → v = x3 u) ∨ (∃ v : Fin x1, ∀ u : Fin x1, (u, v) ∈ x2 → x3 u = v)
  · exact h1 x1 x2 x3 x4 hcard h2n hc4 hmatch hao hfun hp
  · push Not at hp
    exact h2 x1 x2 x3 x4 hcard h2n hc4 hmatch hao hfun
      ⟨fun u => Exists.elim (hp.1 u) (fun v h => ⟨v, h.2, h.1⟩),
       fun v => Exists.elim (hp.2 v) (fun u h => ⟨u, h.2, h.1⟩)⟩
