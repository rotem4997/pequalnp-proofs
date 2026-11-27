import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4297_436
    (bound : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ))
    (stars : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → x5.output < x1 + x2 + x5.gates.length → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → (∀ x10 < x5.gates.length, ∀ (x12 x13 : ℕ), x5.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x12, x13] : PEqualNP.CircuitLowerBounds.Gate } → (x1 + x2 ≤ x13 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x12) ∧ (x1 + x2 ≤ x12 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x12 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13)) → ∃ (x11 : List (ℕ × List ℕ)), (∀ x12 ∈ x11, x12.2 ≠ [] ∧ ((x12.1 < x1 ∧ ∀ x14 ∈ x12.2, x1 ≤ x14 ∧ x14 < x1 + x2) ∨ x1 ≤ x12.1 ∧ x12.1 < x1 + x2 ∧ ∀ x14 ∈ x12.2, x14 < x1)) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 ↔ ∃ x14 ∈ x11, x14.1 = ↑x12 ∧ x1 + ↑x13 ∈ x14.2 ∨ x14.1 = x1 + ↑x13 ∧ ↑x12 ∈ x14.2) ∧ (List.map (fun (x12 : ℕ × List ℕ) => x12.2.length) x11).sum + x11.length - (1 : ℕ) ≤ x5.size := by
  classical
  intro x1 x2 x3 x4 x5 hC hA hout hF hNF
  let E : Finset (Fin x1 × Fin x2) := Finset.univ.filter (fun e => x3 e.1 e.2)
  have memE : ∀ p l, (p, l) ∈ E ↔ x3 p l := by
    intro p l
    simp [E]
  obtain ⟨A, B, hcov, hbd⟩ := bound x1 x2 E x5
    (by
      rintro p q l s hpq hls ⟨e1, e2, e3, e4⟩
      exact hC p q l s hpq hls ⟨(memE _ _).mp e1, (memE _ _).mp e2, (memE _ _).mp e3, (memE _ _).mp e4⟩)
    hA
    (by
      intro z
      rw [hF z]
      simp only [memE])
  obtain ⟨L, hL1, hL2, hL3⟩ := stars x1 x2 E A B hcov
  refine ⟨L, hL1, fun p l => ?_, by omega⟩
  rw [← memE p l]
  exact hL2 p l
