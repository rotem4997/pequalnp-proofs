import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1934_497
    (h_const : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → 0 < C.size → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2, true]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h_input : ∀ i : Fin 9, ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → 0 < C.size → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2, !x i]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h_and : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → 0 < C.size → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2, !(x 0 && x 2)]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro xs _ C hfan hsize
  let F (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let N (x : Fin 9 → Bool) := PEqualNP.CircuitLowerBounds.GateOp.not.eval (xs.map fun i => (w x).getD i false)
  have wlen (x : Fin 9 → Bool) : (w x).length = 10 := by simp [w]
  have rawRead (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
      (w x).getD i false = x ⟨i, hi⟩ := by
    change (List.ofFn x ++ [_]).getD i false = _
    rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have andRead (x : Fin 9 → Bool) : (w x).getD 9 false = (x 0 && x 2) := by
    change (List.ofFn x ++ [_]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have atZero : N (fun _ => false) = true := by
    have hzeros : w (fun _ => false) = List.replicate 10 false := by decide
    cases xs with
    | nil => rfl
    | cons i tail =>
      change !((w (fun _ => false)).getD i false) = true
      rw [hzeros]
      by_cases hi : i < 10
      · rw [List.getD_replicate _ (by simpa using hi)]
        rfl
      · rw [List.getD_eq_default _ _ (by simpa using hi)]
        rfl
  have singleton (j : Fin 9) : F (fun i => decide (i = j)) = false := by
    fin_cases j <;> decide
  by_cases pos : 0 < C.size
  · cases xs with
    | nil =>
      obtain ⟨x, hx⟩ := h_const C hfan pos hsize
      refine ⟨x, ?_⟩
      change C.eval (w x ++ [true]) ≠ F x
      simpa [w, F] using hx
    | cons i tail =>
      by_cases hi : i < 9
      · obtain ⟨x, hx⟩ := h_input ⟨i, hi⟩ C hfan pos hsize
        refine ⟨x, ?_⟩
        change C.eval (w x ++ [!((w x).getD i false)]) ≠ F x
        rw [rawRead x i hi]
        simpa [w, F] using hx
      · by_cases h9 : i = 9
        · subst i
          obtain ⟨x, hx⟩ := h_and C hfan pos hsize
          refine ⟨x, ?_⟩
          change C.eval (w x ++ [!((w x).getD 9 false)]) ≠ F x
          rw [andRead]
          simpa [w, F] using hx
        · obtain ⟨x, hx⟩ := h_const C hfan pos hsize
          refine ⟨x, ?_⟩
          change C.eval (w x ++ [!((w x).getD i false)]) ≠ F x
          rw [List.getD_eq_default _ _ (by rw [wlen]; omega)]
          simpa [w, F] using hx
  · have hg : C.gates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos pos)
    have hw (x : Fin 9 → Bool) :
        C.eval (w x ++ [N x]) = (w x ++ [N x]).getD C.output false := by
      change (C.gates.foldl (fun acc gate =>
        acc ++ [gate.op.eval (gate.inputs.map fun i => acc.getD i false)])
        (w x ++ [N x])).getD C.output false = _
      simp only [hg, List.foldl_nil]
    by_cases hlo : C.output < 9
    · let j : Fin 9 := ⟨C.output, hlo⟩
      let x : Fin 9 → Bool := fun i => decide (i = j)
      refine ⟨x, ?_⟩
      change C.eval (w x ++ [N x]) ≠ F x
      rw [hw, List.getD_append _ _ _ _ (by rw [wlen]; omega), rawRead x C.output hlo,
        singleton j]
      simp [x, j]
    · by_cases h9 : C.output = 9
      · let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
        refine ⟨x, ?_⟩
        change C.eval (w x ++ [N x]) ≠ F x
        rw [hw, h9, List.getD_append _ _ _ _ (by rw [wlen]; decide), andRead]
        decide
      · by_cases h10 : C.output = 10
        · refine ⟨fun _ => false, ?_⟩
          change C.eval (w (fun _ => false) ++ [N (fun _ => false)]) ≠ F (fun _ => false)
          rw [hw, h10, List.getD_append_right _ _ _ _ (by rw [wlen]), wlen, atZero]
          decide
        · refine ⟨fun _ => true, ?_⟩
          change C.eval (w (fun _ => true) ++ [N (fun _ => true)]) ≠ F (fun _ => true)
          have hlen : (w (fun _ => true) ++ [N (fun _ => true)]).length ≤ C.output := by
            simp only [List.length_append, wlen, List.length_cons, List.length_nil]
            omega
          rw [hw, List.getD_eq_default _ _ hlen]
          decide
