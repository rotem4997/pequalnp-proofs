import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2377_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (x4.val < 21 ∧ 21 ≤ x5.val ∧ (x5.val + 21 - x4.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ({x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ)) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (x4.val < 21 ∧ 21 ≤ x5.val ∧ (x5.val + 21 - x4.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ((21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hm hf
  have key : ∀ (u v : Fin 42), ((u.val, v.val) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ))) ↔ (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) := by decide +kernel
  have hfm : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧ x u = true ∧ x v = true := by
    intro x
    have hiff := hf x
    constructor
    · intro he
      rcases (hiff.mp he) with ⟨u, v, huv, hxu, hxv⟩
      exact ⟨u, v, (key u v).mp huv, hxu, hxv⟩
    · intro hm
      rcases hm with ⟨u, v, hmod, hxu, hxv⟩
      exact (hiff.mpr ⟨u, v, (key u v).mpr hmod, hxu, hxv⟩)
  by_cases hle : ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ))
  · exact h1 C hm hfm hle
  · have hge : (21 : ℕ) ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by omega
    exact h2 C hm hfm hge