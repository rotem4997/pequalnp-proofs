import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3020_529
    (constant : ∀ (b : Bool),
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 → ∃ (x : Fin 9 → Bool),
        let w := List.ofFn x ++ [x 0 || x 2]
        C.eval (w ++ [b]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (copy : ∀ (i : Fin 10),
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 → ∃ (x : Fin 9 → Bool),
        let w := List.ofFn x ++ [x 0 || x 2]
        C.eval (w ++ [w.getD i.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (raw : ∀ (i j : Fin 9), i < j →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 → ∃ (x : Fin 9 → Bool),
        let w := List.ofFn x ++ [x 0 || x 2]
        C.eval (w ++ [x i && x j]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (mixed : ∀ (i : Fin 9),
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 → ∃ (x : Fin 9 → Bool),
        let w := List.ofFn x ++ [x 0 || x 2]
        C.eval (w ++ [x i && (x 0 || x 2)]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro inputs arity C fan size
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  have ofRaw (x : Fin 9 → Bool) (i : Fin 9) : (w x).getD i.val false = x i := by
    change (List.ofFn x ++ [x 0 || x 2]).getD i.val false = x i
    rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
  have last (x : Fin 9 → Bool) : (w x).getD 9 false = (x 0 || x 2) := by
    change (List.ofFn x ++ [x 0 || x 2]).getD 9 false = _
    simp [List.getD_eq_getElem?_getD]
  have missing (x : Fin 9 → Bool) {i : ℕ} (hi : 10 ≤ i) : (w x).getD i false = false := by
    apply List.getD_eq_default
    simpa [w] using hi
  change ∃ x : Fin 9 → Bool, C.eval (w x ++ [GateOp.and.eval (inputs.map
      fun a => (w x).getD a.val false)]) ≠ _
  cases inputs with
  | nil => exact constant true C fan size
  | cons a rest =>
    cases rest with
    | nil =>
      change ∃ x, C.eval (w x ++ [(w x).getD a.val false && true]) ≠ _
      simp only [Bool.and_true]
      by_cases live : a.val < 10
      · exact copy ⟨a.val, live⟩ C fan size
      · obtain ⟨x, h⟩ := constant false C fan size
        refine ⟨x, ?_⟩
        rw [missing x (Nat.le_of_not_gt live)]
        exact h
    | cons b rest =>
      cases rest with
      | nil =>
        change ∃ x, C.eval
          (w x ++ [(w x).getD a.val false && ((w x).getD b.val false && true)]) ≠ _
        simp only [Bool.and_true]
        by_cases inA : a.val < 10
        swap
        · obtain ⟨x, h⟩ := constant false C fan size
          refine ⟨x, ?_⟩
          rw [missing x (Nat.le_of_not_gt inA), Bool.false_and]
          exact h
        by_cases inB : b.val < 10
        swap
        · obtain ⟨x, h⟩ := constant false C fan size
          refine ⟨x, ?_⟩
          rw [missing x (Nat.le_of_not_gt inB), Bool.and_false]
          exact h
        by_cases same : a.val = b.val
        · obtain ⟨x, h⟩ := copy ⟨a.val, inA⟩ C fan size
          refine ⟨x, ?_⟩
          rw [← same, Bool.and_self]
          exact h
        by_cases rawA : a.val < 9
        · let i : Fin 9 := ⟨a.val, rawA⟩
          by_cases rawB : b.val < 9
          · let j : Fin 9 := ⟨b.val, rawB⟩
            rcases Nat.lt_or_gt_of_ne same with ab | ba
            · obtain ⟨x, h⟩ := raw i j ab C fan size
              refine ⟨x, ?_⟩
              rw [show a.val = i.val from rfl, show b.val = j.val from rfl,
                ofRaw x i, ofRaw x j]
              exact h
            · obtain ⟨x, h⟩ := raw j i ba C fan size
              refine ⟨x, ?_⟩
              rw [show a.val = i.val from rfl, show b.val = j.val from rfl,
                ofRaw x i, ofRaw x j]
              simpa only [Bool.and_comm] using h
          · have b9 : b.val = 9 := by omega
            obtain ⟨x, h⟩ := mixed i C fan size
            refine ⟨x, ?_⟩
            rw [show a.val = i.val from rfl, b9, ofRaw x i, last x]
            exact h
        · have rawB : b.val < 9 := by omega
          let j : Fin 9 := ⟨b.val, rawB⟩
          have a9 : a.val = 9 := by omega
          obtain ⟨x, h⟩ := mixed j C fan size
          refine ⟨x, ?_⟩
          rw [a9, show b.val = j.val from rfl, last x, ofRaw x j]
          simpa only [Bool.and_comm] using h
      | cons c rest =>
        simp only [List.length_cons] at arity
        omega
