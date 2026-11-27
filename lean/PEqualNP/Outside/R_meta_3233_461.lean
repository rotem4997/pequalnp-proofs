import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3233_461
    (classify :
      let f := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      let args := fun (m : Nat) (x : Fin 9 → Bool) =>
        List.ofFn x ++ [x 4 || x 6,(List.finRange 9).any (fun i => m.testBit i.val && x i)]
      ∀ (C : Circuit) (g : Gate), FanInTwo C → C.size ≤ 15 →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false=(x 4 || x 6)) →
        circuitFun 9 C=f → C.gates[1]?=some g → g.op=.or →
        ∃ m∈([3,5,9,17,33,65,129,257,20,36,132,144,81,84,208] : List Nat), ∃ B : Circuit, FanInTwo B ∧ B.size≤13 ∧ ∀ x, B.eval (args m x)=f x)
    (restrictGate :
      let f := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      let args := fun (m : Nat) (x : Fin 9 → Bool) =>
        List.ofFn x ++ [x 4 || x 6,(List.finRange 9).any (fun i => m.testBit i.val && x i)]
      ∀ m∈([17,20,144] : List Nat), ∀ B : Circuit, FanInTwo B → B.size ≤ 13 →
        (∀ x, B.eval (args m x)=f x) → HasCircuitSize 8 (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (lower8 :
      ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (residual :
      let f := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      let args := fun (m : Nat) (x : Fin 9 → Bool) =>
        List.ofFn x ++ [x 4 || x 6,(List.finRange 9).any (fun i => m.testBit i.val && x i)]
      ∀ m∈([3,5,9,33,65,129,257,36,132,81,84,208] : List Nat), ∀ B : Circuit, FanInTwo B →
        (∀ x, B.eval (args m x)=f x) → 14 ≤ B.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size := by
  intro C hf h9 he g hg hop _
  by_contra! h
  obtain ⟨m,hm,B,hB,hsize,eval⟩ := classify C g hf (by omega) h9 he hg hop
  by_cases a : m ∈ ([17,20,144] : List Nat)
  · exact lower8 (restrictGate m a B hB hsize eval)
  · have inc : ∀ t ∈ ([3,5,9,17,33,65,129,257,20,36,132,144,81,84,208] : List Nat), t ∈ ([17,20,144] : List Nat) ∨ t ∈ ([3,5,9,33,65,129,257,36,132,81,84,208] : List Nat) := by decide
    have lb := residual m ((inc m hm).resolve_left a) B hB eval
    omega
