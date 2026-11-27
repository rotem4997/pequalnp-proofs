import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5176_748
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 26 C →
      have w : ℕ → ℕ → Bool := fun m k => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      ∀ x8 ∈ [(0 : ℕ), (13 : ℕ)],
      have x9 : ℕ := if x8 = 0 then 25034751 else 67108341
      have x10 : ℕ := if x8 = 0 then 8191 else 67100672
      have x11 : ℕ := if x8 = 0 then 25018369 else 15860
      ∀ (S : Set ℕ), (∀ i : Fin 26, i.val ∈ S → x9.testBit i.val = false) →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → 26 + j ∈ S →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ g.inputs, a ∈ S) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ a ∈ g.inputs, a ∈ S) ∨
            (∀ a ∈ g.inputs, w (2 ^ x8) a = false) ∧ w x10 (26 + j) = false ∧ w x11 (26 + j) = false)) →
        ∀ k ∈ S, k < 26 + C.size → w x10 k = false ∧ w x11 k = false)
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), 63 ≤ C.size → C.size ≤ 64 →
      PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) →
      have w : ℕ → ℕ → Bool := fun m k => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)],
      have x9 : ℕ := if x8 = 0 then 25034751 else 67108341
      have x10 : ℕ := if x8 = 0 then 8191 else 67100672
      have x11 : ℕ := if x8 = 0 then 25018369 else 15860
      ∀ (S : Set ℕ), C.output ∈ S → (∀ i : Fin 26, i.val ∈ S → x9.testBit i.val = false) →
        (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → 26 + j ∈ S →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ g.inputs, a ∈ S) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ a ∈ g.inputs, a ∈ S) ∨
            (∀ a ∈ g.inputs, w (2 ^ x8) a = false) ∧ w x10 (26 + j) = false ∧ w x11 (26 + j) = false)) →
        (∀ k ∈ S, k < 26 + C.size → w x10 k = false ∧ w x11 k = false) → False) :
     ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : ℕ → ℕ → Bool := fun (x7 x8 : ℕ) => (x1.wires (List.ofFn fun (x9 : Fin (26 : ℕ)) => x7.testBit ↑x9)).getD x8 Bool.false;             ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)],               have x9 : ℕ := if x8 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ);               have x10 : ℕ := if x8 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ);               have x11 : ℕ := if x8 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ);               ∀ (x12 : Set ℕ), x1.output ∈ x12 → (∀ (x14 : Fin (26 : ℕ)), ↑x14 ∈ x12 → x9.testBit ↑x14 = Bool.false) → ¬∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x15]? = Option.some x16 → (26 : ℕ) + x15 ∈ x12 → (x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x20 ∈ x16.inputs, x20 ∈ x12) ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x20 ∈ x16.inputs, x20 ∈ x12) ∨ (∀ x20 ∈ x16.inputs, x7 ((2 : ℕ) ^ x8) x20 = Bool.false) ∧ x7 x10 ((26 : ℕ) + x15) = Bool.false ∧ x7 x11 ((26 : ℕ) + x15) = Bool.false) := by
  intro C h63 h64 hAO hNd hSpec
  obtain ⟨x8, hx8, hx⟩ := h2 C h63 h64 hAO hNd hSpec
  refine ⟨x8, hx8, ?_⟩
  intro x9 x10 x11 S hout hin hcl
  exact hx S hout hin hcl (h1 C hAO x8 hx8 S hin hcl)
