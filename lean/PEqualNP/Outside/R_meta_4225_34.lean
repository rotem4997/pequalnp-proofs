import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On rows where a degree-two input is decisive, its unique disjunction cannot
-- already be true because of its companion. Exclude companions that are raw inputs.
theorem PEqualNP.Outside.R_meta_4225_34
    (noRaw : ∀ (C : Circuit) (u v : Fin 9) (i : Fin C.size),
      circuitFun 9 C = (fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
      fun mask => decide (∀ i : Fin 9, mask.testBit i.val = true → x i = true)) →
      u ∈ ([4,6,7] : List (Fin 9)) → u ≠ v → (C.gates.get i).op = GateOp.or →
      (∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i) →
      v.val ∉ (C.gates.get i).inputs)
    (search : ∀ C : Circuit, IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = (fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
      fun mask => decide (∀ i : Fin 9, mask.testBit i.val = true → x i = true)) →
      (∀ i : Fin C.size, (∀ p ∈ (C.gates.get i).inputs, p < 9 + i.val) ∧
        (C.gates.get i).inputs.Nodup ∧
        ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1 ∨
          (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2)) →
      (∀ u ∈ ([4,6,7] : List (Fin 9)), ∃ i : Fin C.size,
        (∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i) ∧
        (C.gates.get i).op = GateOp.or ∧
        ∀ w ∈ (C.gates.get i).inputs, w ≠ u.val → 9 ≤ w) →
      (∃ j : Fin C.size, (C.gates.get j).op = GateOp.not) → False) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∃ (x8 : Fin x1.size), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  intro C minimal size computes shape readers _ notGate
  have same : circuitFun 9 C = (fun x : Fin 9 → Bool => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
      fun mask => decide (∀ i : Fin 9, mask.testBit i.val = true → x i = true)) := by
    rw [computes]
    decide +kernel
  apply search C minimal size same shape _ notGate
  intro u hu
  obtain ⟨i, only, isOr⟩ := readers u hu
  refine ⟨i, only, isOr, ?_⟩
  intro w hw different
  by_contra! raw
  let v : Fin 9 := ⟨w,raw⟩
  have ne : u ≠ v := fun h => different (congrArg Fin.val h.symm)
  exact noRaw C u v i same hu ne isOr only hw
