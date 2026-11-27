import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2841_1
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.size - notCount C)
    (monotoneBound : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C → T.card ≤ 2 →
      notCount C = 0 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ C.size)
    (signedBound : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C → T.card ≤ 2 →
      1 ≤ notCount C → notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ C.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x6 ∈ x2, x5 x6 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) → (14 : ℕ) ≤ x1.size := by
  intro C T legal card computes
  by_cases zero : notCount C = 0
  · exact monotoneBound C T legal card zero computes
  by_cases low : notCount C ≤ 2
  · exact signedBound C T legal card (by omega) low computes
  let first : Gate := ⟨.or, [0,4]⟩
  let second : Gate := ⟨.or, T.toList.map Fin.val⟩
  let D : Circuit := ⟨first :: second :: C.gates, C.output⟩
  have legalD : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [first]
    · exact ⟨by simp [second], by simpa [second] using card⟩
    · exact legal g hg
  have value (x : Fin 9 → Bool) :
      D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have firstValue : step (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
      change List.ofFn x ++ [([(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false].any id)] = _
      simp [List.getD_eq_getElem?_getD, Bool.or_assoc]
    have read (i : Fin 9) : (List.ofFn x ++ [x 0 || x 4]).getD i.val false = x i := by
      have lt : i.val < (List.ofFn x).length := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left lt]
      rw [List.getElem?_eq_getElem lt, List.getElem_ofFn]
      rfl
    have secondValue :
        step (List.ofFn x ++ [x 0 || x 4]) second =
          List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)] := by
      have mapEq :
          (T.toList.map Fin.val).map (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false) =
            T.toList.map x := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact read i
      have eq : (T.toList.map x).any id = decide (∃ a ∈ T, x a = true) := by
        apply Bool.eq_iff_iff.mpr
        simp [List.any_eq_true]
      change (List.ofFn x ++ [x 0 || x 4]) ++ [((T.toList.map Fin.val).map (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false)).any id] = _
      rw [mapEq]
      simpa [List.append_assoc] using
        congrArg (fun b => List.ofFn x ++ [x 0 || x 4, b]) eq
    change (C.gates.foldl step (step (step (List.ofFn x) first) second)).getD C.output false =
      (C.gates.foldl step _).getD C.output false
    rw [firstValue, secondValue]
  have post := binaryBound D legalD (fun x => (value x).trans (computes x))
  have size : D.size = C.size + 2 := by
    change (first :: second :: C.gates).length = C.gates.length + 2
    simp
  have nots : notCount D = notCount C := by
    change (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _))
      (first :: second :: C.gates)).length = _
    change _ = (List.filter (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) C.gates).length
    simp [first, second]
  rw [size, nots] at post
  omega
