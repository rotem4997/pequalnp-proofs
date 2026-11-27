import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2736_14
    (cofactor : ∀ C : Circuit, FanInTwo C → C.size ≤ 14 → (∀ x : Fin 8 → Bool, C.eval [x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7,x 0 && x 3] = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) → C.gates.countP (fun (g : Gate) => g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4) ≤ 1)
    (single : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x3 →     x4.length ≤ (2 : ℕ) →       (∀ (x7 : Fin (9 : ℕ) → Bool),           have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ))];           x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : Fin (11 : ℕ)) => x8.getD (↑x9) Bool.false) x4)]) = (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →         (⟨.or, x4.map Fin.val⟩ :: x3.gates).countP (fun (g : Gate) => g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4) ≤ 1 → (14 : ℕ) ≤ x3.size) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => x2.inputs.head? == Option.some (4 : ℕ) || x2.op.eval [Bool.true, Bool.true] && x2.inputs.contains (4 : ℕ)) x1.gates; have x2 : PEqualNP.CircuitLowerBounds.Circuit → List (Fin (11 : ℕ)) → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin (11 : ℕ))) => { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2.gates, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x3 →     x4.length ≤ (2 : ℕ) →       (∀ (x7 : Fin (9 : ℕ) → Bool),           have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ))];           x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : Fin (11 : ℕ)) => x8.getD (↑x9) Bool.false) x4)]) = (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →         x1 (x2 x3 x4) ≤ (2 : ℕ) → (14 : ℕ) ≤ x3.size := by
  intro readers pack C pins legal arity correct _
  by_contra! small
  let g : Gate := ⟨.or,pins.map Fin.val⟩
  let D : Circuit := ⟨g :: C.gates,C.output⟩
  have valid : FanInTwo D := by
    intro h mem
    rcases List.mem_cons.mp mem with rfl|m
    · exact ⟨by simp [g], by simpa [g] using arity⟩
    · exact legal h m
  have size : D.size ≤ 14 := by change C.gates.length + 1 ≤ 14; change C.gates.length < 14 at small; omega
  have cut := cofactor D valid size (by
    intro x
    let z : Fin 9 → Bool := ![x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7]
    have eq := correct z
    change C.eval ([x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7,x 0 && x 3] ++ [GateOp.or.eval (pins.map fun j => ([x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7,x 0 && x 3] : List Bool).getD j.val false)]) = _ at eq
    change C.eval ([x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7,x 0 && x 3] ++ [GateOp.or.eval ((pins.map Fin.val).map fun j => ([x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7,x 0 && x 3] : List Bool).getD j false)]) = _
    simpa only [List.map_map,Function.comp_def,show z 0 = x 0 from rfl,show z 1 = x 1 from rfl,show z 2 = x 2 from rfl,show z 3 = x 3 from rfl,show z 4 = false from rfl,show z 5 = x 4 from rfl,show z 6 = x 5 from rfl,show z 7 = x 6 from rfl,show z 8 = x 7 from rfl,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] using eq)
  exact (Nat.not_lt_of_ge (single C pins legal arity correct cut)) small
