import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4201_777
  (normalization :
    let computes : Circuit → Prop := fun C =>
      ∀ (x : Fin 42 → Bool), C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 42), (p.val < 21 ∧ 21 ≤ l.val ∧
          (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
          x p = true ∧ x l = true
    let clean : Circuit → Prop := fun C =>
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∀ (x : Fin 42 → Bool), (C.wires (List.ofFn x)).getD (42+j) false = true →
          C.eval (List.ofFn x) = true
    let ors : Circuit → ℕ := fun C =>
      C.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false)
    ∀ (C : Circuit), Monotone2 C → computes C →
      ∃ (D : Circuit), Monotone2 D ∧ computes D ∧ clean D ∧ ors D ≤ ors C)
  (counting :
    let computes : Circuit → Prop := fun C =>
      ∀ (x : Fin 42 → Bool), C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 42), (p.val < 21 ∧ 21 ≤ l.val ∧
          (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
          x p = true ∧ x l = true
    let clean : Circuit → Prop := fun C =>
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∀ (x : Fin 42 → Bool), (C.wires (List.ofFn x)).getD (42+j) false = true →
          C.eval (List.ofFn x) = true
    let ors : Circuit → ℕ := fun C =>
      C.gates.countP (fun g => GateOp.casesOn g.op false true false (fun _ => false) false)
    ∀ (C : Circuit), Monotone2 C → computes C → clean C → 104 ≤ ors C) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x1.gates := by
  intro C hC hcomp
  obtain ⟨D,hD,hDcomp,hclean,hle⟩ := normalization C hC hcomp
  exact (counting D hD hDcomp hclean).trans hle
