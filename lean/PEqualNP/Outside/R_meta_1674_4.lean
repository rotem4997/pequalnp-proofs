import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Treat the specified OR as a tenth input to the suffix. The counting
-- bound charges each NOT and each effective read after the first one.
theorem PEqualNP.Outside.R_meta_1674_4
    (seed : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        circuitFun 9 C = f → C.size ≤ 15 →
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 14 ∧
          (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = f x) ∧
          ∀ i : Fin 10, ∃ x y : Fin 10 → Bool,
            (∀ j, j ≠ i → x j = y j) ∧ circuitFun 10 D x ≠ circuitFun 10 D y)
    (compact : ∀ (n : ℕ) (C : Circuit), 2 ≤ n → FanInTwo C →
      (∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) →
      ∃ D : Circuit, D.size ≤ C.size ∧ FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
          let pins := D.gates.flatMap (fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2));
          (∀ w < n + D.size, w ≠ D.output → w ∈ pins) ∧
          (D.gates.filter fun g => g.op.eval [false]).length + (pins.length - pins.toFinset.card) ≤ D.size + 1 - n)
    (pins : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ D : Circuit, FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = f x) → ∀ (i : Fin 9) (j : Fin 10), i ≠ 0 → i ≠ 2 → i.castSucc ≠ j → ∀ g ∈ D.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) →
        (g.inputs = [i.val,j.val] ∨ g.inputs = [j.val,i.val]) →
        2 ≤ (D.gates.filter fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains i.val).length)
    (searchBound : let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ D : Circuit, FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = f x) →
        (let pins := D.gates.flatMap (fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2));
          (∀ w < 10 + D.size, w ≠ D.output → w ∈ pins) ∧
          (D.gates.filter fun g => g.op.eval [false]).length + (pins.length - pins.toFinset.card) ≤ 5) →
        (∀ (i : Fin 9) (j : Fin 10), i ≠ 0 → i ≠ 2 → i.castSucc ≠ j → ∀ g ∈ D.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) →
        (g.inputs = [i.val,j.val] ∨ g.inputs = [j.val,i.val]) →
        2 ≤ (D.gates.filter fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains i.val).length) → 15 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  by_contra! short
  obtain ⟨D, hd, hsize, heval, hdep⟩ := seed C fan first computes (by omega)
  obtain ⟨B, hlen, hb, he, alive, budget⟩ := compact 10 D (by decide) hd hdep
  have same (x : Fin 9 → Bool) :
      B.eval (List.ofFn x ++ [x 0 || x 2]) = D.eval (List.ofFn x ++ [x 0 || x 2]) := by
    let y : Fin 10 → Bool := Fin.lastCases (x 0 || x 2) x
    have hy : List.ofFn y = List.ofFn x ++ [x 0 || x 2] := by
      rw [List.ofFn_succ_last]
      simp [y]
      rfl
    rw [← hy]
    exact congrFun he y
  have good := fun x => (same x).trans (heval x)
  have small : B.size ≤ 14 := hlen.trans hsize
  have lower := searchBound B hb good ⟨alive, le_trans budget (by omega)⟩ (pins B hb good)
  omega
