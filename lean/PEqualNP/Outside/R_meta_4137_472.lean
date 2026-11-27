import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With vertex 0 false, or with vertex 1 false, the side condition holds and the function is the
-- twelve-edge function of the other nine vertices, after renaming. It needs 15 gates even with
-- one extra false input: base is the statement of the checked L_meta_2317. fixZero and fixOne:
-- every gate that reads the vertex goes away, and so does every gate that reads an AND or NOT
-- gate reading it. Three such gates among 17 leave 14. What remains is fewKilled: at most two
-- such gates at vertex 0 and at most two at vertex 1.
theorem PEqualNP.Outside.R_meta_4137_472
    (base : ∀ (C : Circuit), FanInTwo C →
      (∀ (x : Fin 9 → Bool), C.eval (List.ofFn x ++ [false]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (fixZero : ∀ (C : Circuit), FanInTwo C →
      (∀ y : Fin 9 → Bool, C.eval (List.ofFn (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0))) = true) ∨
      ∃ E : Circuit, FanInTwo E ∧ E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 0 || (Nat.ble (10 : ℕ) k && (C.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 0 && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ C.size ∧
        ∀ y : Fin 9 → Bool, E.eval (List.ofFn y ++ [false]) = C.eval (List.ofFn (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0))))
    (fixOne : ∀ (C : Circuit), FanInTwo C →
      (∀ y : Fin 9 → Bool, C.eval (List.ofFn (fun i : Fin 10 => if i = 1 then false else y (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0))) = true) ∨
      ∃ E : Circuit, FanInTwo E ∧ E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 1 || (Nat.ble (10 : ℕ) k && (C.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 1 && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ C.size ∧
        ∀ y : Fin 9 → Bool, E.eval (List.ofFn y ++ [false]) = C.eval (List.ofFn (fun i : Fin 10 => if i = 1 then false else y (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0))))
    (fewKilled : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → (List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 0 || (Nat.ble (10 : ℕ) k && (x1.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 0 && !h.op.eval [Bool.true, Bool.false])))) x1.gates ≤ 2 ∧ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 1 || (Nat.ble (10 : ℕ) k && (x1.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 1 && !h.op.eval [Bool.true, Bool.false])))) x1.gates ≤ 2) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hfan hsize
  by_contra hne
  have hall : ∀ x : Fin 10 → Bool, (x 0 && x 1) = false →
      C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    intro x hd
    by_contra hx
    exact hne ⟨x, hd, hx⟩
  by_cases hk0 : List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 0 || (Nat.ble (10 : ℕ) k && (C.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 0 && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ 2
  swap
  · rcases fixZero C hfan with hT | ⟨E, hE, hEs, hEf⟩
    · have h1 := hT (fun _ => false)
      have e : (List.ofFn (fun i : Fin 10 => if i = 0 then false else (fun _ : Fin 9 => false) (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)))
          = List.ofFn (fun _ : Fin 10 => false) := rfl
      rw [e, hall (fun _ => false) rfl] at h1
      exact absurd h1 (by decide)
    · have h15 := base E hE (fun y => by
        rw [hEf y]
        have hd : ((fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)) 0 && (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)) 1) = false := rfl
        rw [hall (fun i : Fin 10 => if i = 0 then false else y (([0, 4, 0, 1, 6, 7, 3, 5, 2, 8] : List (Fin 9)).getD i.val 0)) hd]
        have taut : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
            (false && b4 || b4 && b0 || b0 && b1 || b1 && b6 || b6 && false || false && b7 || b4 && b3 || b0 && b5 || b1 && b2 || b6 && b8 || b7 && b5 || b5 && b8 || b8 && b3 || b3 && b2 || b2 && b7)
            = (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by decide
        exact taut (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))
      omega
  by_cases hk1 : List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == 1 || (Nat.ble (10 : ℕ) k && (C.gates[k - 10]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains 1 && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ 2
  swap
  · rcases fixOne C hfan with hT | ⟨E, hE, hEs, hEf⟩
    · have h1 := hT (fun _ => false)
      have e : (List.ofFn (fun i : Fin 10 => if i = 1 then false else (fun _ : Fin 9 => false) (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0)))
          = List.ofFn (fun _ : Fin 10 => false) := rfl
      rw [e, hall (fun _ => false) rfl] at h1
      exact absurd h1 (by decide)
    · have h15 := base E hE (fun y => by
        rw [hEf y]
        have hd : ((fun i : Fin 10 => if i = 1 then false else y (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0)) 0 && (fun i : Fin 10 => if i = 1 then false else y (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0)) 1) = false := by
          show ((fun i : Fin 10 => if i = 1 then false else y (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0)) 0 && false) = false
          exact Bool.and_false _
        rw [hall (fun i : Fin 10 => if i = 1 then false else y (([4, 0, 6, 1, 0, 3, 7, 8, 2, 5] : List (Fin 9)).getD i.val 0)) hd]
        have taut : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
            (b4 && false || false && b6 || b6 && b1 || b1 && b0 || b0 && b4 || b4 && b3 || false && b7 || b6 && b8 || b1 && b2 || b0 && b5 || b3 && b8 || b8 && b5 || b5 && b7 || b7 && b2 || b2 && b3)
            = (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by decide
        exact taut (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))
      omega
  exact hne (fewKilled C hfan hsize ⟨hk0, hk1⟩)
