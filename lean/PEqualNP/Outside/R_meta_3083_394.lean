import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3083_394
    (decompose : have reads : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun g v =>
      (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs);
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 15 →
      (∃ i j : Fin C.gates.length, i < j ∧ i.val ≤ 3 ∧ (C.gates.get i).op = .not ∧
        (C.gates.get j).op = .not ∧ ∀ k : Fin C.gates.length,
          (C.gates.get k).op = .not → k = i ∨ k = j) →
      (∀ (x : Fin 9 → Bool), (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (∀ v : ℕ, v = 0 ∨ v = 2 → ∃ g ∈ C.gates.drop 1, reads g v) →
      ∃ (P D : PEqualNP.CircuitLowerBounds.Circuit) (q : Fin 13),
        PEqualNP.MetaComplexity.Monotone2 P ∧ PEqualNP.MetaComplexity.FanInTwo D ∧
        P.size ≤ 2 ∧ P.size + D.size ≤ 13 ∧
        D.gates.countP (fun g => g.op.eval [false]) = 1 ∧
        (∀ v : ℕ, v = 0 ∨ v = 2 → q.val = v ∨ ∃ g ∈ P.gates ++ D.gates, reads g v) ∧
        ∀ (x : Fin 9 → Bool), have w : List Bool := P.wires (List.ofFn x ++ [x 0 || x 2]); D.eval (w ++ [!w.getD q false]) = C.eval (List.ofFn x))
    (remaining : have reads : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun g v =>
      (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs);
    ∀ (P D : PEqualNP.CircuitLowerBounds.Circuit) (q : Fin 13),
      PEqualNP.MetaComplexity.Monotone2 P → PEqualNP.MetaComplexity.FanInTwo D →
      P.size ≤ 2 → P.size + D.size ≤ 13 → D.gates.countP (fun g => g.op.eval [false]) = 1 →
      (∀ v : ℕ, v = 0 ∨ v = 2 → q.val = v ∨ ∃ g ∈ P.gates ++ D.gates, reads g v) →
      ∃ (x : Fin 9 → Bool), have w : List Bool := P.wires (List.ofFn x ++ [x 0 || x 2]); D.eval (w ++ [!w.getD q false]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 ≤ (3 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size := by
  intro _ C fan early first computes reader
  by_contra h
  have small : C.size ≤ 15 := by omega
  obtain ⟨P, D, q, hP, hD, hpre, hsize, hnot, hread, heval⟩ :=
    decompose C fan small early first reader
  obtain ⟨x, hx⟩ := remaining P D q hP hD hpre hsize hnot hread
  exact hx ((heval x).trans (congrFun computes x))
