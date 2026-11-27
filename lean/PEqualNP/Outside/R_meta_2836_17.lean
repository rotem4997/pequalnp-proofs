import PEqualNP.Defs

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_2836_17
    (left : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 0 false) ++
          [x 0 || x 4, x 0 || x 3]) = f x) → False)
    (right : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 4 false) ++
          [x 0 || x 4, x 4 || x 1]) = f x) → False)
    (triple : let f : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ i : Fin 9, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 6) →
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++
            [false, x 0 || x 4 || x i]) = f x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) =>
        x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ))
        || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) →
      ((∀ (x5 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨
      (∀ (x5 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨
      (∀ (x5 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨
      ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C target fan size cases
  let f : (Fin 9 → Bool) → Bool := fun x =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  have edgeForm : ∀ x : Fin 9 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) = f x := by
    decide +kernel
  let p : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have p0 : p 0 = 0 := by decide
  have p4 : p 4 = 4 := by decide
  have p5 : p 5 = 1 := by decide
  have p_inj : ∀ i j, p i = p j → i = j := by decide
  have symm : ∀ x : Fin 9 → Bool, f (x ∘ p) = f x := by
    decide +kernel
  let wire : ℕ → ℕ := fun i => if hi : i < 9 then (p ⟨i, hi⟩).val else i
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let move : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map wire⟩
  let Rel : List Bool → List Bool → Prop := fun w v =>
    w.length = v.length ∧ 9 ≤ w.length ∧ ∀ i, v.getD (wire i) false = w.getD i false
  have foldMove : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w v : List Bool),
      Rel w v → Rel (gs.foldl step w) ((gs.map move).foldl step v) := by
    intro gs
    induction gs with
    | nil => exact fun _ _ h => h
    | cons g gs ih =>
      intro w v h
      obtain ⟨len, bound, reads⟩ := h
      change Rel (gs.foldl step (step w g)) ((gs.map move).foldl step (step v (move g)))
      apply ih
      have value : (move g).op.eval ((move g).inputs.map fun i => v.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [move, List.map_map, Function.comp_def, reads]
      let b := g.op.eval (g.inputs.map fun i => w.getD i false)
      change Rel (w ++ [b]) (v ++ [(move g).op.eval ((move g).inputs.map fun i => v.getD i false)])
      rw [value]
      change (w ++ [b]).length = (v ++ [b]).length ∧ 9 ≤ (w ++ [b]).length ∧ _
      refine ⟨by simp [len], by simp; omega, ?_⟩
      intro i
      by_cases hi : i < w.length
      · have hw : wire i < v.length := by
          dsimp [wire]
          split
          · rename_i hi9
            exact (p ⟨i, hi9⟩).isLt.trans_le (by omega)
          · omega
        rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hi]
        exact reads i
      · have hwire : wire i = i := by simp [wire, show ¬ i < 9 by omega]
        rw [hwire, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map move, wire C.output⟩
  have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(fan g' hg').1, by simpa [move] using (fan g' hg').2⟩
  have sizeD : D.size ≤ 13 := by
    change (C.gates.map move).length ≤ 13
    rw [List.length_map]
    exact size
  have evalD (x : Fin 9 → Bool) (ys : List Bool) :
      D.eval (List.ofFn x ++ ys) = C.eval (List.ofFn (x ∘ p) ++ ys) := by
    have base : Rel (List.ofFn (x ∘ p) ++ ys) (List.ofFn x ++ ys) := by
      refine ⟨by simp, by simp, ?_⟩
      intro i
      by_cases hi : i < 9
      · have hw : wire i < 9 := by simp [wire, hi]
        rw [List.getD_append _ _ _ _ (by simpa using hw),
          List.getD_append _ _ _ _ (by simpa using hi)]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hw),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getElem_ofFn, Function.comp_def]
        congr 1
        apply Fin.ext
        simp [wire, hi]
      · rw [show wire i = i by simp [wire, hi],
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
        simp
    exact (foldMove C.gates _ _ base).2.2 C.output
  rcases cases with h | h | h | ⟨i, hi0, hi4, h⟩
  · exact left C fan size fun x => (h x).trans (edgeForm x)
  · exact right C fan size fun x => (h x).trans (edgeForm x)
  · apply right D fanD sizeD
    intro x
    have update : Function.update x 4 false ∘ p = Function.update (x ∘ p) 4 false := by
      funext i
      by_cases hi : i = 4
      · subst i
        simp [Function.comp_def, p4]
      · have hpi : p i ≠ 4 := fun e => hi (p_inj i 4 (e.trans p4.symm))
        simp [Function.comp_def, Function.update_of_ne hi, Function.update_of_ne hpi]
    rw [evalD, update]
    have hc := (h (x ∘ p)).trans (edgeForm (x ∘ p))
    simpa only [Function.comp_def, p0, p4, p5] using hc.trans (symm x)
  · let rep : Fin 9 → Prop := fun i => i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 6
    have orbits : ∀ i : Fin 9, i ≠ 0 → i ≠ 4 → rep i ∨
        (rep (p i) ∧ p (p i) = i) := by
      decide
    rcases orbits i hi0 hi4 with hr | ⟨hr, hp⟩
    · exact triple i hr C fan size fun x => (h x).trans (edgeForm x)
    · apply triple (p i) hr D fanD sizeD
      intro x
      rw [evalD]
      have hc := (h (x ∘ p)).trans (edgeForm (x ∘ p))
      simpa only [Function.comp_def, p0, p4, hp] using hc.trans (symm x)
