import Mathlib
import PEqualNP.Defs

-- The first OR becomes a primary input. Three monotone gates precede the first NOT.
-- Its source is one of thirteen wires or the false default. Ten suffix gates remain.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3196_143
    (strip : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
    (∃ i j : Fin C.gates.length, i < j ∧ i.val = 4 ∧
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      ∀ t : Fin C.gates.length, (C.gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not → t = i ∨ t = j) →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
    ∃ (P S : PEqualNP.CircuitLowerBounds.Circuit) (k : Fin 14), P.size = 3 ∧ PEqualNP.MetaComplexity.Monotone2 P ∧
      S.size + 5 = C.size ∧ PEqualNP.MetaComplexity.FanInTwo S ∧
      (∃! j : Fin S.gates.length, (S.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      ∀ x : Fin 9 → Bool,
        let w := P.wires (List.ofFn x ++ [x 0 || x 2])
        S.eval (w ++ [!(w.getD k false)]) = C.eval (List.ofFn x))
    (suffix_bound : ∀ (P S : PEqualNP.CircuitLowerBounds.Circuit) (k : Fin 14),
    P.size = 3 → PEqualNP.MetaComplexity.Monotone2 P → S.size ≤ 10 → PEqualNP.MetaComplexity.FanInTwo S →
    (∃! j : Fin S.gates.length, (S.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not) →
    ∃ x : Fin 9 → Bool,
      let w := P.wires (List.ofFn x ++ [x 0 || x 2])
      S.eval (w ++ [!(w.getD k false)]) ≠ (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD
          (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (4 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hfan positions hfirst hfun
  obtain ⟨P,S,k,hp,hm,hs,hf,hn,heval⟩ := strip C hfan positions hfirst
  by_contra! small
  obtain ⟨x,hx⟩ := suffix_bound P S k hp hm (by omega) hf hn
  apply hx
  rw [heval x]
  change PEqualNP.MetaComplexity.circuitFun 9 C x = _
  rw [hfun]
  have table : ∀ x : Fin 9 → Bool, (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD
          (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64) := by decide
  exact table x
