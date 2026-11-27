import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3696_509
    (exposed : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) →       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : Fin x2 × Fin x2 | x3 x8.1 x8.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 fun (x9 : Fin (x2 + x2)) => Decidable.decide (x9 = Fin.castAdd x2 x8.1 ∨ x9 = Fin.natAdd x2 x8.2)) = Bool.true};       have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x8 x9 = Bool.false;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x10 ∈ x9.gates, x10.inputs.length ≤ (2 : ℕ)) → x8 x9 → x9.size ≤ (4512 : ℕ) →
        let m := (x7 x9).card
        ∃ a b : ℕ, a + b ≤ x9.size + 1 ∧ m ≤ a * b ∧
          m * m ≤ b * (a * (a - 1) + m) ∧ m * m ≤ a * (b * (b - 1) + m))
    (numerical : ∀ g a b m : ℕ, g ≤ 4512 → a + b ≤ g + 1 → m ≤ a * b →
      m * m ≤ b * (a * (a - 1) + m) → m * m ≤ a * (b * (b - 1) + m) →
      m ≤ 24 * g) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) →       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : Fin x2 × Fin x2 | x3 x8.1 x8.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 fun (x9 : Fin (x2 + x2)) => Decidable.decide (x9 = Fin.castAdd x2 x8.1 ∨ x9 = Fin.natAdd x2 x8.2)) = Bool.true};       have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x8 x9 = Bool.false;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x10 ∈ x9.gates, x10.inputs.length ≤ (2 : ℕ)) → x8 x9 → x9.size ≤ (4512 : ℕ) → (x7 x9).card ≤ (24 : ℕ) * x9.size := by
  intro q N I _ hq hI
  dsimp only
  intro C hfan hsound hsize
  obtain ⟨a, b, hab, hm, hb, ha⟩ := exposed q N I hq hI C hfan hsound hsize
  exact numerical C.size a b _ hsize hab hm hb ha
