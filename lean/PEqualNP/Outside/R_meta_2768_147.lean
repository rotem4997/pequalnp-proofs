import Mathlib
import PEqualNP.Defs

-- Supply the first OR as the tenth input. In a counterexample the remaining circuit
-- can be chosen so that each of inputs four, six and seven occurs at most once
-- in its unfolded output formula. The recurrence counts both children of every gate.
set_option maxRecDepth 5000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2768_147
    (terminal : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.gates.length=15 →
    C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[0,3]⟩ →
    C.gates.countP (fun g => g.op.eval [false]) = 1 →
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D ∧
      D.gates.length=14 ∧ D.gates.countP (fun g => g.op.eval [false]) = 1 ∧
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64)) ∧
      ∀ i ∈ ([4,6,7] : List ℕ), ∃ weight : ℕ → ℕ,
      (∀ a < 10, weight a = (if a = i then 1 else 0)) ∧
      (∀ j : Fin D.gates.length, weight (10+j.val) = ((D.gates.get j).inputs.map weight).sum) ∧
      weight D.output ≤ 1)
    (search : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
    D.gates.length=14 → D.gates.countP (fun g => g.op.eval [false]) = 1 →
    (∀ i ∈ ([4,6,7] : List ℕ), ∃ weight : ℕ → ℕ,
      (∀ a < 10, weight a = (if a = i then 1 else 0)) ∧
      (∀ j : Fin D.gates.length, weight (10+j.val) = ((D.gates.get j).inputs.map weight).sum) ∧
      weight D.output ≤ 1) → ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) ≠ (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C dataC countC computes
  obtain ⟨len,_,head,shape⟩ := dataC
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
    have form := shape j hj
    dsimp only at form
    rw [eq] at form
    rcases form with h | ⟨_,_,h⟩ | ⟨_,_,_,_,_,h|h⟩ <;> rw [h] <;> simp
  have truth : ∀ x : Fin 9 → Bool, (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64) := by decide
  have eq (x : Fin 9 → Bool) : C.eval (List.ofFn x) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit (PEqualNP.MetaComplexity.tableIndex x % 64) :=
    (congrFun computes x).trans (truth x)
  obtain ⟨D,hD,back,hd,one,agrees,uses⟩ := terminal C fan len head countC eq
  obtain ⟨x,hx⟩ := search D hD back hd one uses
  exact hx (agrees x)
