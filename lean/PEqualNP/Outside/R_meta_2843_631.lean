import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2843_631
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.size - notCount C)
    (monotoneBound : ∀ (C : Circuit) (a : Fin 9), FanInTwo C → notCount C = 0 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ C.size)
    (signedBound : ∀ (C : Circuit) (a : Fin 9), FanInTwo C →
      1 ≤ notCount C → notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) || x4 x2]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (14 : ℕ) ≤ x1.size := by
  intro C a legal computes
  by_cases zero : notCount C = 0
  · exact monotoneBound C a legal zero computes
  by_cases low : notCount C ≤ 2
  · exact signedBound C a legal (by omega) low computes
  let first : Gate := ⟨.or, [0, 4]⟩
  let second : Gate := ⟨.or, [9, a.val]⟩
  let D : Circuit := ⟨first :: second :: C.gates, C.output⟩
  have legalD : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [first]
    · simp [second]
    · exact legal g hg
  have value (x : Fin 9 → Bool) :
      D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) := by
    let evalGate (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have firstValue : evalGate (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
      let w := List.ofFn x
      change w ++ [([w.getD 0 false, w.getD 4 false].any id)] = _
      simp [w, List.getD_eq_getElem?_getD]
    have anchor : (List.ofFn x ++ [x 0 || x 4]).getD 9 false = (x 0 || x 4) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    have input : (List.ofFn x ++ [x 0 || x 4]).getD a.val false = x a := by
      have within : a.val < (List.ofFn x).length := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left within]
      rw [List.getElem?_eq_getElem within, List.getElem_ofFn]
      rfl
    have secondValue : evalGate (List.ofFn x ++ [x 0 || x 4]) second =
        List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a] := by
      let w := List.ofFn x ++ [x 0 || x 4]
      change w ++ [([w.getD 9 false, w.getD a.val false].any id)] = _
      rw [show w.getD 9 false = (x 0 || x 4) from anchor,
          show w.getD a.val false = x a from input]
      simp only [w, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        List.append_assoc, List.singleton_append]
    change (C.gates.foldl evalGate (evalGate (evalGate (List.ofFn x) first) second)).getD
      C.output false = (C.gates.foldl evalGate _).getD C.output false
    rw [firstValue, secondValue]
  have count := binaryBound D legalD (fun x => (value x).trans (computes x))
  have size : D.size = C.size + 2 := by
    change (first :: second :: C.gates).length = C.gates.length + 2
    simp
  have nots : notCount D = notCount C := by
    change (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _))
      (first :: second :: C.gates)).length = _
    change _ = (List.filter (fun g : Gate =>
      @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) C.gates).length
    simp [first, second]
  rw [size, nots] at count
  omega
