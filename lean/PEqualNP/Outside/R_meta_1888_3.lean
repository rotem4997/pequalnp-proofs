import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_1888_3
    (h_mono : ∀ D : Circuit, Monotone2 D → ReadsBack 11 D → D.size ≤ 18 →
      11 ≤ D.output → D.output < 11 + D.size →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (h_not12 : ∀ D : Circuit, FanInTwo D → ReadsBack 11 D → D.size ≤ 18 →
      11 ≤ D.output → D.output < 11 + D.size →
      1 ≤ notCount D → notCount D ≤ 2 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (h_not34 : ∀ D : Circuit, FanInTwo D → ReadsBack 11 D → D.size ≤ 18 →
      11 ≤ D.output → D.output < 11 + D.size →
      3 ≤ notCount D → notCount D ≤ 4 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (h_not5 : ∀ D : Circuit, FanInTwo D → ReadsBack 11 D → D.size ≤ 18 →
      11 ≤ D.output → D.output < 11 + D.size →
      5 ≤ notCount D →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C σ hFan hSize
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hEvalAnd : ∀ ls : List Bool, GateOp.and.eval ls = ls.all id := fun _ => rfl
  have hEvalOr : ∀ ls : List Bool, GateOp.or.eval ls = ls.any id := fun _ => rfl
  have hEvalNot : ∀ ls : List Bool, GateOp.not.eval ls = !(ls.headD false) := fun _ => rfl
  have hGateAt : ∀ (E : Circuit) (j : ℕ), gateAt E j = E.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have hLen : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have hGetLt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
      exact List.getD_append w _ false i hi
  let ρ : ℕ → ℕ := fun i => if h : i < 10 then (σ ⟨i, h⟩).val else i
  have hρlt : ∀ i, i < 11 → ρ i < 11 := by
    intro i hi
    dsimp only [ρ]
    split_ifs with h
    · have := (σ ⟨i, h⟩).isLt; omega
    · omega
  have hρge : ∀ i, 11 ≤ i → ρ i = i := by
    intro i hi
    dsimp only [ρ]
    have h : ¬ (i < 10) := by omega
    simp [h]
  let cleanGate : ℕ → Gate → Gate := fun j g =>
    GateOp.casesOn g.op
      (if (g.inputs.map ρ).all (fun i => decide (i < 11 + j)) then
        ⟨GateOp.and, g.inputs.map ρ⟩
      else ⟨GateOp.or, []⟩)
      ⟨GateOp.or, (g.inputs.map ρ).filter (fun i => decide (i < 11 + j))⟩
      (List.casesOn (g.inputs.map ρ)
        ⟨GateOp.and, []⟩
        (fun a _ => if a < 11 + j then ⟨GateOp.not, [a]⟩ else ⟨GateOp.and, []⟩))
      (fun m => ⟨GateOp.mod m, g.inputs.map ρ⟩)
      ⟨GateOp.maj, g.inputs.map ρ⟩
  let D : Circuit := ⟨C.gates.mapIdx cleanGate, ρ C.output⟩
  have hCleanEval : ∀ (j : ℕ) (g : Gate) (w w' : List Bool),
      w.length = 11 + j → w'.length = 11 + j →
      (∀ i, w'.getD (ρ i) false = w.getD i false) →
      (cleanGate j g).op.eval ((cleanGate j g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro j g w w' hw hw' hrel
    have hmap : (g.inputs.map ρ).map (fun i => w'.getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hrel i
    cases hop : g.op with
    | or =>
      dsimp only [cleanGate]
      rw [hop]
      dsimp only
      rw [hEvalOr, hEvalOr, ← hmap]
      generalize g.inputs.map ρ = ls
      induction ls with
      | nil => rfl
      | cons a t ih =>
        by_cases ha : a < 11 + j
        · simp only [List.filter_cons, decide_eq_true ha, ↓reduceIte, List.map_cons, List.any_cons, id_eq, ih]
        · have hd : w'.getD a false = false := List.getD_eq_default w' false (by omega)
          simp only [List.filter_cons, decide_eq_false ha, Bool.false_eq_true, ↓reduceIte,
            List.map_cons, List.any_cons, id_eq, hd, Bool.false_or, ih]
    | and =>
      dsimp only [cleanGate]
      rw [hop]
      dsimp only
      by_cases hall : (g.inputs.map ρ).all (fun i => decide (i < 11 + j)) = true
      · simp only [hall, ↓reduceIte, hEvalAnd, hmap]
      · have hallf : (g.inputs.map ρ).all (fun i => decide (i < 11 + j)) = false :=
          Bool.eq_false_iff.mpr hall
        simp only [hallf, Bool.false_eq_true, ↓reduceIte, hEvalOr, hEvalAnd, List.map_nil, List.any_nil]
        rw [← hmap]
        have hne : ∃ a ∈ g.inputs.map ρ, ¬ (a < 11 + j) := by
          by_contra hnone
          apply hall
          rw [List.all_eq_true]
          intro a ha
          apply decide_eq_true
          by_contra hlt
          exact hnone ⟨a, ha, hlt⟩
        obtain ⟨a, ha, hge⟩ := hne
        have hd : w'.getD a false = false := List.getD_eq_default w' false (by omega)
        symm
        rw [List.all_eq_false]
        exact ⟨false, List.mem_map.mpr ⟨a, ha, hd⟩, by decide⟩
    | not =>
      dsimp only [cleanGate]
      rw [hop]
      dsimp only
      rw [← hmap]
      cases hls : g.inputs.map ρ with
      | nil => rfl
      | cons a t =>
        dsimp only
        by_cases ha : a < 11 + j
        · simp only [ha, ↓reduceIte, hEvalNot, List.map_cons]
          rfl
        · have hd : w'.getD a false = false := List.getD_eq_default w' false (by omega)
          simp only [ha, ↓reduceIte, hEvalAnd, hEvalNot, List.map_nil, List.all_nil, List.map_cons, hd]
          rfl
    | mod m =>
      dsimp only [cleanGate]
      rw [hop]
      dsimp only
      rw [hmap]
    | maj =>
      dsimp only [cleanGate]
      rw [hop]
      dsimp only
      rw [hmap]
  have hMapIdxFold : ∀ (gs : List Gate) (w w' : List Bool),
      w.length = 11 → w'.length = 11 →
      (∀ i, w'.getD (ρ i) false = w.getD i false) →
      ∀ i, ((gs.mapIdx cleanGate).foldl step w').getD (ρ i) false = (gs.foldl step w).getD i false := by
    intro gs w w' hw hw' h0
    induction gs using List.reverseRecOn with
    | nil => intro i; exact h0 i
    | append_singleton gs g ih =>
      intro i
      rw [List.mapIdx_append, List.foldl_append, List.foldl_append]
      simp only [List.mapIdx_cons, List.mapIdx_nil, List.foldl_cons, List.foldl_nil]
      generalize hL : gs.foldl step w = L at ih ⊢
      generalize hL' : (gs.mapIdx cleanGate).foldl step w' = L' at ih ⊢
      have hlenL : L.length = 11 + gs.length := by rw [← hL, hLen, hw]
      have hlenL' : L'.length = 11 + gs.length := by rw [← hL', hLen, hw', List.length_mapIdx]
      rcases Nat.lt_trichotomy i (11 + gs.length) with hlt | heq | hgt
      · have hρi : ρ i < 11 + gs.length := by
          by_cases h11 : i < 11
          · have := hρlt i h11; omega
          · rw [hρge i (by omega)]; exact hlt
        simp only [step]
        rw [List.getD_append L' _ false (ρ i) (by omega), List.getD_append L _ false i (by omega)]
        exact ih i
      · have hρi : ρ i = i := hρge i (by omega)
        rw [hρi, heq]
        simp only [step]
        rw [← hlenL', List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hlenL', ← hlenL, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        simpa only [Nat.zero_add] using hCleanEval gs.length g L L' hlenL hlenL' ih
      · rw [hρge i (by omega)]
        simp only [step]
        rw [List.getD_eq_default (L' ++ _) false (by simp [hlenL']; omega),
          List.getD_eq_default (L ++ _) false (by simp [hlenL]; omega)]
  have hEvalEq : ∀ x : Fin 10 → Bool,
      D.eval (List.ofFn x ++ [x 0 || x 2]) =
        C.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) := by
    intro x
    apply hMapIdxFold C.gates (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) (List.ofFn x ++ [x 0 || x 2])
      (by simp) (by simp)
    intro i
    by_cases h10 : i < 10
    · have hσlt : (σ ⟨i, h10⟩).val < 10 := (σ ⟨i, h10⟩).isLt
      have hρi : ρ i = (σ ⟨i, h10⟩).val := by simp [ρ, h10]
      rw [hρi, List.getD_append _ _ false _ (by simp [hσlt]),
        List.getD_append _ _ false _ (by simp [h10])]
      rw [List.getD_eq_getElem _ _ (by simp [hσlt]), List.getD_eq_getElem _ _ (by simp [h10])]
      simp only [List.getElem_ofFn, Function.comp_apply]
    · by_cases h11 : i = 10
      · subst h11
        have hρ10 : ρ 10 = 10 := by simp [ρ]
        rw [hρ10]
        simp [List.getD_eq_getElem?_getD]
      · have hρi : ρ i = i := hρge i (by omega)
        rw [hρi, List.getD_eq_default _ false (by simp; omega),
          List.getD_eq_default _ false (by simp; omega)]
  have hDFan : FanInTwo D := by
    intro g' hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
    rw [List.length_mapIdx] at hj
    simp only [D, List.getElem_mapIdx]
    obtain ⟨hop, hlen⟩ := hFan (C.gates[j]'hj) (List.getElem_mem hj)
    have hop' : (C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or ∨
        (C.gates[j]'hj).op = GateOp.not := by simpa using hop
    rcases hop' with h | h | h
    · dsimp only [cleanGate]
      rw [h]
      dsimp only
      split_ifs
      · exact ⟨by simp, by simp [hlen]⟩
      · exact ⟨by simp, by simp⟩
    · dsimp only [cleanGate]
      rw [h]
      dsimp only
      exact ⟨by simp, (List.length_filter_le _ _).trans (by simp [hlen])⟩
    · dsimp only [cleanGate]
      rw [h]
      dsimp only
      cases hls : (C.gates[j]'hj).inputs.map ρ with
      | nil => exact ⟨by simp, by simp⟩
      | cons a t =>
        dsimp only
        split_ifs
        · exact ⟨by simp, by simp⟩
        · exact ⟨by simp, by simp⟩
  have hDSize : D.size ≤ 18 := by
    change D.gates.length ≤ 18
    rw [List.length_mapIdx]
    exact hSize
  have hDReads : ReadsBack 11 D := by
    intro j hj i hi
    have hj' : j < C.gates.length := by simpa [D] using hj
    have hgj : gateAt D j = cleanGate j (C.gates[j]'hj') := by
      rw [hGateAt]
      simp [D, List.getD_eq_getElem?_getD, hj']
    rw [hgj] at hi
    obtain ⟨hop, _⟩ := hFan (C.gates[j]'hj') (List.getElem_mem hj')
    have hop' : (C.gates[j]'hj').op = GateOp.and ∨ (C.gates[j]'hj').op = GateOp.or ∨
        (C.gates[j]'hj').op = GateOp.not := by simpa using hop
    rcases hop' with h | h | h
    · dsimp only [cleanGate] at hi
      rw [h] at hi
      dsimp only at hi
      split_ifs at hi with hall
      · rw [List.all_eq_true] at hall
        exact of_decide_eq_true (hall i hi)
      · simp at hi
    · dsimp only [cleanGate] at hi
      rw [h] at hi
      dsimp only at hi
      rw [List.mem_filter] at hi
      exact of_decide_eq_true hi.2
    · dsimp only [cleanGate] at hi
      rw [h] at hi
      dsimp only at hi
      cases hls : (C.gates[j]'hj').inputs.map ρ with
      | nil => simp [hls] at hi
      | cons a t =>
        simp only [hls] at hi
        split_ifs at hi with ha
        · simp only [List.mem_singleton] at hi
          exact hi ▸ ha
        · simp at hi
  by_cases hOutHi : 11 + D.size ≤ D.output
  · refine ⟨fun i => decide (i = 0 ∨ i = 1), ?_⟩
    rw [← hEvalEq]
    have hF : D.eval (List.ofFn (fun i : Fin 10 => decide (i = 0 ∨ i = 1)) ++
        [decide ((0 : Fin 10) = 0 ∨ (0 : Fin 10) = 1) || decide ((2 : Fin 10) = 0 ∨ (2 : Fin 10) = 1)]) = false := by
      apply List.getD_eq_default
      change (D.gates.foldl step _).length ≤ D.output
      rw [hLen]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      exact hOutHi
    rw [hF]
    decide
  by_cases hOutLo : D.output < 11
  · by_cases hOut10 : D.output < 10
    · let v : Fin 10 := ⟨D.output, hOut10⟩
      refine ⟨fun i => decide (i = v), ?_⟩
      rw [← hEvalEq]
      have hT : D.eval (List.ofFn (fun i => decide (i = v)) ++
          [decide ((0 : Fin 10) = v) || decide ((2 : Fin 10) = v)]) = true := by
        change (D.gates.foldl step _).getD D.output false = true
        rw [hGetLt D.gates _ D.output (by simp; omega)]
        rw [List.getD_append _ _ false D.output (by simp [hOut10])]
        rw [List.getD_eq_getElem _ _ (by simp [hOut10])]
        simp only [List.getElem_ofFn, decide_eq_true_eq]
        rfl
      have hTargetOne : ∀ u : Fin 10,
          (fun x6 : Fin 10 → Bool =>
            x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
            x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 4 && x6 9 ||
            x6 5 && x6 7 || x6 7 && x6 9 || x6 9 && x6 6 || x6 6 && x6 8 || x6 8 && x6 5)
          (fun i => decide (i = u)) = false := by decide
      rw [hT, hTargetOne v]
      decide
    · have hEq10 : D.output = 10 := by omega
      refine ⟨fun i => decide (i = 0), ?_⟩
      rw [← hEvalEq]
      have hT : D.eval (List.ofFn (fun i : Fin 10 => decide (i = 0)) ++
          [decide ((0 : Fin 10) = 0) || decide ((2 : Fin 10) = 0)]) = true := by
        change (D.gates.foldl step _).getD D.output false = true
        rw [hEq10, hGetLt D.gates _ 10 (by simp)]
        simp [List.getD_eq_getElem?_getD]
      rw [hT]
      decide
  have hLo : 11 ≤ D.output := by omega
  have hHi : D.output < 11 + D.size := by omega
  by_cases hk0 : notCount D = 0
  · have hDMono : Monotone2 D := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hDFan g hg
      have hnot : g.op ≠ GateOp.not := by
        intro hne
        have hpos : 0 < notCount D := by
          change 0 < (D.gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)).length
          refine List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, ?_⟩)
          rw [hne]; rfl
        omega
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
      rcases hop' with h | h | h
      · exact ⟨by simp [h], hlen⟩
      · exact ⟨by simp [h], hlen⟩
      · exact (hnot h).elim
    obtain ⟨x, hx⟩ := h_mono D hDMono hDReads hDSize hLo hHi
    exact ⟨x, by rw [← hEvalEq x]; exact hx⟩
  · by_cases hk2 : notCount D ≤ 2
    · obtain ⟨x, hx⟩ := h_not12 D hDFan hDReads hDSize hLo hHi (by omega) hk2
      exact ⟨x, by rw [← hEvalEq x]; exact hx⟩
    · by_cases hk4 : notCount D ≤ 4
      · obtain ⟨x, hx⟩ := h_not34 D hDFan hDReads hDSize hLo hHi (by omega) hk4
        exact ⟨x, by rw [← hEvalEq x]; exact hx⟩
      · obtain ⟨x, hx⟩ := h_not5 D hDFan hDReads hDSize hLo hHi (by omega)
        exact ⟨x, by rw [← hEvalEq x]; exact hx⟩
