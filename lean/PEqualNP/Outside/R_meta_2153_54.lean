import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2153_54
  (shrink : ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) →
    C.gates[1]?.map Gate.op = some GateOp.not → C.size ≤ 15 →
    C.eval [true,false,false,false,true,false,false,false,false] ≠
      C.eval [true,false,false,false,false,false,false,false,false] →
    ∃ (j : Fin 8) (D : Circuit), FanInTwo D ∧ D.size ≤ 12 ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y ++ [!(y j),true,false]) =
        C.eval (List.ofFn ((4 : Fin 9).insertNth false y)))
  (lower : ∀ (j : Fin 8) (D : Circuit), FanInTwo D →
    (∀ y : Fin 8 → Bool, D.eval (List.ofFn y ++ [!(y j),true,false]) =
      (fun y : Fin 8 → Bool => ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
          (fun e => y (Fin.ofNat 8 (e / 10)) && y (Fin.ofNat 8 (e % 10)))) y) → 13 ≤ D.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C hf hor he hn
  by_contra! small
  let f := (fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let p : Fin 9 → Bool := ![true,false,false,false,true,false,false,false,false]
  let n : Fin 9 → Bool := ![true,false,false,false,false,false,false,false,false]
  have eq (x : Fin 9 → Bool) : C.eval (List.ofFn x) = f x := congrFun he x
  have diff : C.eval (List.ofFn p) ≠ C.eval (List.ofFn n) := by
    rw [eq p,eq n]
    decide
  obtain ⟨j,D,hD,hsize,hval⟩ := shrink C hf hor hn (by omega) diff
  apply Nat.not_lt_of_ge (lower j D hD ?_) (by omega)
  intro y
  rw [hval,eq]
  have table : ∀ z : Fin 8 → Bool, f ((4 : Fin 9).insertNth false z) = (fun y : Fin 8 → Bool => ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
          (fun e => y (Fin.ofNat 8 (e / 10)) && y (Fin.ofNat 8 (e % 10)))) z := by
    decide +kernel
  exact table y
