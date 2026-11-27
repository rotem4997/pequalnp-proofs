import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4340_2
    (hNot : ∀ x1 ∈ [(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))],
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size ≤ (14 : ℕ) →
        (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x7 ++ [!x7 x1]) ≠
            (fun (x8 : Fin (9 : ℕ) → Bool) =>
              x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) ||
              x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) ||
              x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) ||
              x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) ||
              x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) ||
              x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) ||
              x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) ||
              x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
              x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
              x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
              x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
              x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7)
    (hFour : ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))),
        ((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)))],
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size ≤ (14 : ℕ) →
        (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∀ x6 ∈ x3.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → (9 : ℕ) ≤ x6.inputs.headD (9 : ℕ)) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠
            (fun (x8 : Fin (9 : ℕ) → Bool) =>
              x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) ||
              x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) ||
              x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) ||
              x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) ||
              x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) ||
              x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) ||
              x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) ||
              x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
              x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
              x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
              x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
              x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7)
    (hOrb02 : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ (14 : ℕ) →
      (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ x6 ∈ x3.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → (9 : ℕ) ≤ x6.inputs.headD (9 : ℕ)) →
      (∀ x6 ∈ x3.gates, ∀ i j : ℕ, i < (9 : ℕ) → j < (9 : ℕ) → i ≠ j → x6.inputs = [i, j] →
        min i j * (9 : ℕ) + max i j ∈ [(2 : ℕ), 6, 7, 8, 12, 13, 14, 16, 22, 24, 26, 32, 33, 34, 41, 44, 51, 71]) →
      ∃ (x7 : Fin (9 : ℕ) → Bool),
        x3.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ))]) ≠
          (fun (x8 : Fin (9 : ℕ) → Bool) =>
            x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) ||
            x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) ||
            x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) ||
            x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) ||
            x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) ||
            x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) ||
            x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) ||
            x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
            x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
            x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
            x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
            x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7)
    (hOrb06 : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ (14 : ℕ) →
      (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ x6 ∈ x3.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → (9 : ℕ) ≤ x6.inputs.headD (9 : ℕ)) →
      (∀ x6 ∈ x3.gates, ∀ i j : ℕ, i < (9 : ℕ) → j < (9 : ℕ) → i ≠ j → x6.inputs = [i, j] →
        min i j * (9 : ℕ) + max i j ∈ [(6 : ℕ), 7, 13, 16, 22, 24, 33, 34, 41, 44, 51, 71]) →
      ∃ (x7 : Fin (9 : ℕ) → Bool),
        x3.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) ≠
          (fun (x8 : Fin (9 : ℕ) → Bool) =>
            x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) ||
            x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) ||
            x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) ||
            x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) ||
            x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) ||
            x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) ||
            x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) ||
            x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
            x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
            x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) ||
            x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) ||
            x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  classical
  let fP9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let S02 : List ℕ := [2, 6, 7, 8, 12, 13, 14, 16, 22, 24, 26, 32, 33, 34, 41, 44, 51, 71]
  let S06 : List ℕ := [6, 7, 13, 16, 22, 24, 33, 34, 41, 44, 51, 71]
  let code : ℕ → ℕ → ℕ := fun i j => min i j * 9 + max i j
  let vGate : List Bool → Gate → Bool := fun w g =>
    g.op.eval (g.inputs.map fun i => w.getD i false)
  let run : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [vGate w g]) w
  have run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      run (g :: gs) w = run gs (w ++ [vGate w g]) := rfl
  have run_append (a b : List Gate) (w : List Bool) :
      run (a ++ b) w = run b (run a w) := List.foldl_append
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih => rw [run_cons, ih]; simp; omega
  have run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [run_cons, ih _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have mem_zipIdx : ∀ (l : List Gate) (n : ℕ) (x : Gate × ℕ), x ∈ l.zipIdx n → x.1 ∈ l := by
    intro l
    induction l with
    | nil => intro n x hx; simp at hx
    | cons a t ih =>
      intro n x hx
      simp only [List.zipIdx_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (n + 1) x hx)
  have getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq (w : List Bool) (b : Bool) :
      (w ++ [b]).getD w.length false = b := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  have getD_ofFn (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x).getD i.val false = x i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some, Fin.eta]

  -- Helper 1: remove gate at index `idx` (whose value depends only on inputs 0..8) and place its value at wire 9!
  have extract_gate : ∀ (C : Circuit) (pre post : List Gate) (g0 : Gate) (seedVal : (Fin 9 → Bool) → Bool),
      C.gates = pre ++ g0 :: post →
      FanInTwo C →
      C.size ≤ 15 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = fP9 x) →
      (∀ x : Fin 9 → Bool, vGate (run pre (List.ofFn x)) g0 = seedVal x) →
      ∃ D : Circuit,
        FanInTwo D ∧
        D.size + 1 = C.size ∧
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [seedVal x]) = fP9 x) ∧
        (∀ g ∈ D.gates, ∃ g' ∈ pre ++ post,
          g.op = g'.op ∧
          g.inputs.length = g'.inputs.length ∧
          ((∀ i ∈ g.inputs, i < 9) ↔ (∀ i ∈ g'.inputs, i < 9)) ∧
          (9 ≤ g.inputs.headD 9 ↔ 9 ≤ g'.inputs.headD 9) ∧
          (∀ i j : ℕ, i < 9 → j < 9 → (g.inputs = [i, j] ↔ g'.inputs = [i, j]))) := by
    intro C pre post g0 seedVal hsplit hfan hsz heval hg0
    let idx := pre.length
    let rWire : ℕ → ℕ → ℕ := fun lim k =>
      if k < 9 then k
      else if lim ≤ k then 100
      else if k < 9 + idx then k + 1
      else if k = 9 + idx then 9
      else k
    have rWire_lt9 (lim k : ℕ) : rWire lim k < 9 ↔ k < 9 := by
      dsimp only [rWire]
      split_ifs <;> omega
    have rWire_eq_lt9 (lim k : ℕ) (hk : k < 9) : rWire lim k = k := by
      simp [rWire, hk]
    let rGate : ℕ → Gate → Gate := fun lim g => ⟨g.op, g.inputs.map (rWire lim)⟩
    let pre' : List Gate := (pre.zipIdx 9).map (fun p => rGate p.2 p.1)
    let post' : List Gate := (post.zipIdx (10 + idx)).map (fun p => rGate p.2 p.1)
    let out' : ℕ := rWire (9 + C.gates.length) C.output
    let D : Circuit := ⟨pre' ++ post', out'⟩
    have hpre'_len : pre'.length = pre.length := by simp [pre']
    have hpost'_len : post'.length = post.length := by simp [post']
    have hD_sz : D.size + 1 = C.size := by
      change (pre' ++ post').length + 1 = C.gates.length
      rw [List.length_append, hpre'_len, hpost'_len, hsplit, List.length_append, List.length_cons]
      omega
    have hD_fan : FanInTwo D := by
      intro g hg
      simp only [D, List.mem_append, pre', post', List.mem_map] at hg
      rcases hg with ⟨⟨g', pos⟩, hm, rfl⟩ | ⟨⟨g', pos⟩, hm, rfl⟩
      · have hg' : g' ∈ C.gates := by
          rw [hsplit]; exact List.mem_append_left _ (mem_zipIdx pre 9 (g', pos) hm)
        obtain ⟨hop, hlen⟩ := hfan g' hg'
        exact ⟨hop, by simp [rGate, hlen]⟩
      · have hg' : g' ∈ C.gates := by
          rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (mem_zipIdx post (10 + idx) (g', pos) hm))
        obtain ⟨hop, hlen⟩ := hfan g' hg'
        exact ⟨hop, by simp [rGate, hlen]⟩
    have hD_gates : ∀ g ∈ D.gates, ∃ g' ∈ pre ++ post,
        g.op = g'.op ∧
        g.inputs.length = g'.inputs.length ∧
        ((∀ i ∈ g.inputs, i < 9) ↔ (∀ i ∈ g'.inputs, i < 9)) ∧
        (9 ≤ g.inputs.headD 9 ↔ 9 ≤ g'.inputs.headD 9) ∧
        (∀ i j : ℕ, i < 9 → j < 9 → (g.inputs = [i, j] ↔ g'.inputs = [i, j])) := by
      intro g hg
      have one_gate : ∀ (g' : Gate) (pos : ℕ), g' ∈ pre ++ post → g = rGate pos g' →
          ∃ g' ∈ pre ++ post,
            g.op = g'.op ∧
            g.inputs.length = g'.inputs.length ∧
            ((∀ i ∈ g.inputs, i < 9) ↔ (∀ i ∈ g'.inputs, i < 9)) ∧
            (9 ≤ g.inputs.headD 9 ↔ 9 ≤ g'.inputs.headD 9) ∧
            (∀ i j : ℕ, i < 9 → j < 9 → (g.inputs = [i, j] ↔ g'.inputs = [i, j])) := by
        intro g' pos hg' heq
        subst heq
        refine ⟨g', hg', rfl, by simp [rGate], ?_, ?_, ?_⟩
        · constructor
          · intro h i hi; exact (rWire_lt9 pos i).1 (h (rWire pos i) (List.mem_map_of_mem hi))
          · intro h i hi; simp only [rGate, List.mem_map] at hi
            obtain ⟨j, hj, rfl⟩ := hi; exact (rWire_lt9 pos j).2 (h j hj)
        · cases hl : g'.inputs with
          | nil => simp [rGate, hl]
          | cons a t =>
            simp only [rGate, hl, List.map_cons, List.headD_cons]
            have := rWire_lt9 pos a; omega
        · intro i j hi hj
          cases hl : g'.inputs with
          | nil => simp [rGate, hl]
          | cons a t =>
            cases t with
            | nil => simp [rGate, hl]
            | cons b t' =>
              cases t' with
              | nil =>
                simp only [rGate, hl, List.map_cons, List.map_nil, List.cons.injEq, and_true]
                constructor
                · rintro ⟨ha, hb⟩
                  have ha9 : a < 9 := (rWire_lt9 pos a).1 (ha ▸ hi)
                  have hb9 : b < 9 := (rWire_lt9 pos b).1 (hb ▸ hj)
                  rw [rWire_eq_lt9 pos a ha9] at ha; rw [rWire_eq_lt9 pos b hb9] at hb
                  exact ⟨ha, hb⟩
                · rintro ⟨rfl, rfl⟩
                  exact ⟨rWire_eq_lt9 pos a hi, rWire_eq_lt9 pos b hj⟩
              | cons c t'' => simp [rGate, hl]
      simp only [D, List.mem_append, pre', post', List.mem_map] at hg
      rcases hg with ⟨⟨g', pos⟩, hm, heq⟩ | ⟨⟨g', pos⟩, hm, heq⟩
      · exact one_gate g' pos (List.mem_append_left _ (mem_zipIdx pre 9 (g', pos) hm)) heq.symm
      · exact one_gate g' pos (List.mem_append_right _ (mem_zipIdx post (10 + idx) (g', pos) hm)) heq.symm
    have hD_eval : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [seedVal x]) = fP9 x := by
      intro x
      have hlen_in : (List.ofFn x).length = 9 := by simp
      have hC_sz : C.gates.length ≤ 15 := hsz
      have hidx_le : idx + post.length + 1 = C.gates.length := by
        rw [hsplit, List.length_append, List.length_cons]; omega
      -- Step 1: simulate `pre`!
      have hpre_sim : ∀ (gs : List Gate) (wC wD : List Bool),
          wC.length = 9 + (wC.length - 9) →
          9 ≤ wC.length →
          wC.length + gs.length ≤ 9 + idx →
          wD.length = wC.length + 1 →
          (∀ k < 9, wD.getD k false = wC.getD k false) →
          (∀ k, 9 ≤ k → k < wC.length → wD.getD (k + 1) false = wC.getD k false) →
          let wC' := run gs wC
          let wD' := run ((gs.zipIdx wC.length).map (fun p => rGate p.2 p.1)) wD
          wD'.length = wC'.length + 1 ∧
          (∀ k < 9, wD'.getD k false = wC'.getD k false) ∧
          (∀ k, 9 ≤ k → k < wC'.length → wD'.getD (k + 1) false = wC'.getD k false) ∧
          wD'.getD 9 false = wD.getD 9 false := by
        intro gs
        induction gs with
        | nil =>
          intro wC wD _ _ _ hlenD hlt hge
          exact ⟨hlenD, hlt, hge, rfl⟩
        | cons g gs ih =>
          intro wC wD _ h9 hle hlenD hlt hge
          simp only [List.zipIdx_cons, List.map_cons, run_cons]
          have hvg : vGate wD (rGate wC.length g) = vGate wC g := by
            simp only [vGate, rGate, List.map_map]
            congr 1
            refine List.map_congr_left fun k _ => ?_
            simp only [Function.comp_apply]
            by_cases hk9 : k < 9
            · rw [rWire_eq_lt9 wC.length k hk9, hlt k hk9]
            · by_cases hkl : wC.length ≤ k
              · have hr : rWire wC.length k = 100 := by simp [rWire, hk9, hkl]
                rw [hr]
                have h1 : wD.length ≤ 100 := by omega
                rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ hkl]
              · have hk_lt : k < 9 + idx := by simp at hle; omega
                have hr : rWire wC.length k = k + 1 := by simp [rWire, hk9, hkl, hk_lt]
                rw [hr, hge k (by omega) (by omega)]
          rw [hvg]
          have hstep := ih (wC ++ [vGate wC g]) (wD ++ [vGate wC g]) (by simp; omega) (by simp; omega)
            (by simp at hle ⊢; omega) (by simp [hlenD])
            (fun k hk => by
              rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
              exact hlt k hk)
            (fun k hk9 hklt => by
              simp only [List.length_append, List.length_singleton] at hklt
              by_cases hkl : k < wC.length
              · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ hkl]
                exact hge k hk9 hkl
              · have heq : k = wC.length := by omega
                subst heq
                rw [← hlenD, getD_snoc_eq, getD_snoc_eq])
          have hlen1 : (wC ++ [vGate wC g]).length = wC.length + 1 := by simp
          rw [hlen1] at hstep
          refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, ?_⟩
          rw [hstep.2.2.2, getD_snoc_lt _ _ _ (by omega)]
      have hpre_res := hpre_sim pre (List.ofFn x) (List.ofFn x ++ [seedVal x]) (by simp) (by simp)
        (by simp [idx]) (by simp)
        (fun k hk => by rw [getD_snoc_lt _ _ _ (by simp; omega)])
        (fun k hk9 hklt => by simp at hklt; omega)
      -- At the boundary after pre + g0:
      set wC1 := run pre (List.ofFn x) with hwC1
      set wD1 := run pre' (List.ofFn x ++ [seedVal x]) with hwD1
      have hwC1_len : wC1.length = 9 + idx := by rw [hwC1, run_len, hlen_in]
      have hwD1_len : wD1.length = 10 + idx := by
        have := hpre_res.1; change wD1.length = wC1.length + 1 at this; omega
      set wC2 := wC1 ++ [vGate wC1 g0] with hwC2
      have hwC2_len : wC2.length = 10 + idx := by rw [hwC2, List.length_append, List.length_singleton, hwC1_len]; omega
      have hmatch2 : ∀ k < wC2.length, wD1.getD (rWire wC2.length k) false = wC2.getD k false := by
        intro k hk
        by_cases hk9 : k < 9
        · rw [rWire_eq_lt9 _ k hk9]
          have h1 : wD1.getD k false = wC1.getD k false := hpre_res.2.1 k hk9
          rw [h1, hwC2, getD_snoc_lt _ _ _ (by omega)]
        · by_cases hki : k < 9 + idx
          · have hr : rWire wC2.length k = k + 1 := by simp [rWire, hk9, hki, show ¬ wC2.length ≤ k by omega]
            rw [hr]
            have h1 : wD1.getD (k + 1) false = wC1.getD k false := hpre_res.2.2.1 k (by omega) (by omega)
            rw [h1, hwC2, getD_snoc_lt _ _ _ (by omega)]
          · have heq : k = 9 + idx := by omega
            subst heq
            have hr : rWire wC2.length (9 + idx) = 9 := by simp [rWire, show ¬ 9 + idx < 9 by omega, show ¬ wC2.length ≤ 9 + idx by omega]
            rw [hr]
            have h1 : wD1.getD 9 false = (List.ofFn x ++ [seedVal x]).getD 9 false := hpre_res.2.2.2
            have h2 : (List.ofFn x ++ [seedVal x]).getD 9 false = seedVal x := by
              simp
            rw [h1, h2, ← hg0 x, hwC2, ← hwC1_len, getD_snoc_eq]
      -- Step 2: simulate `post`!
      have hpost_sim : ∀ (gs : List Gate) (wC wD : List Bool),
          10 + idx ≤ wC.length →
          wC.length + gs.length ≤ 24 →
          wD.length = wC.length →
          (∀ k < wC.length, wD.getD (rWire wC.length k) false = wC.getD k false) →
          let wC' := run gs wC
          let wD' := run ((gs.zipIdx wC.length).map (fun p => rGate p.2 p.1)) wD
          wD'.length = wC'.length ∧
          (∀ k < wC'.length, wD'.getD (rWire wC'.length k) false = wC'.getD k false) := by
        intro gs
        induction gs with
        | nil => intro wC wD _ _ hlen hm; exact ⟨hlen, hm⟩
        | cons g gs ih =>
          intro wC wD h10 hle hlen hm
          simp only [List.zipIdx_cons, List.map_cons, run_cons]
          have hvg : vGate wD (rGate wC.length g) = vGate wC g := by
            simp only [vGate, rGate, List.map_map]
            congr 1
            refine List.map_congr_left fun k _ => ?_
            simp only [Function.comp_apply]
            by_cases hkl : k < wC.length
            · exact hm k hkl
            · have hk9 : ¬ k < 9 := by omega
              have hr : rWire wC.length k = 100 := by simp [rWire, hk9, show wC.length ≤ k by omega]
              rw [hr, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          rw [hvg]
          have hlen1 : (wC ++ [vGate wC g]).length = wC.length + 1 := by simp
          rw [← hlen1]
          refine ih (wC ++ [vGate wC g]) (wD ++ [vGate wC g]) (by simp; omega) (by simp at hle ⊢; omega) (by simp [hlen]) ?_
          intro k hk
          simp only [List.length_append, List.length_singleton] at hk
          by_cases hkl : k < wC.length
          · have hr_eq : rWire (wC.length + 1) k = rWire wC.length k := by
              dsimp only [rWire]
              split_ifs <;> omega
            have hr_lt : rWire wC.length k < wD.length := by
              dsimp only [rWire]
              split_ifs <;> omega
            rw [hlen1, hr_eq, getD_snoc_lt _ _ _ hr_lt, getD_snoc_lt _ _ _ hkl]
            exact hm k hkl
          · have heq : k = wC.length := by omega
            subst heq
            have hr : rWire (wC ++ [vGate wC g]).length wC.length = wC.length := by
              simp only [List.length_append, List.length_singleton, rWire]
              split_ifs <;> omega
            rw [hr, getD_snoc_eq, ← hlen, getD_snoc_eq]
      have hpost_res := hpost_sim post wC2 wD1 (by omega) (by omega) (by omega) hmatch2
      have hwD_full : D.wires (List.ofFn x ++ [seedVal x]) = run post' wD1 := by
        change run (pre' ++ post') (List.ofFn x ++ [seedVal x]) = run post' wD1
        rw [run_append]
      have hwC_full : C.wires (List.ofFn x) = run post wC2 := by
        change run C.gates (List.ofFn x) = run post wC2
        rw [hsplit, run_append, run_cons]
      have hlen_final : (run post wC2).length = 9 + C.gates.length := by
        rw [run_len, hwC2_len]; omega
      change (D.wires (List.ofFn x ++ [seedVal x])).getD out' false = fP9 x
      rw [← heval x]
      change (D.wires (List.ofFn x ++ [seedVal x])).getD out' false = (C.wires (List.ofFn x)).getD C.output false
      rw [hwD_full, hwC_full]
      have hp' : post' = (post.zipIdx wC2.length).map (fun p => rGate p.2 p.1) := by rw [hwC2_len]
      rw [hp']
      by_cases hout : C.output < 9 + C.gates.length
      · have := hpost_res.2 C.output (by rw [hlen_final]; exact hout)
        rw [hlen_final] at this
        exact this
      · have hout9 : ¬ C.output < 9 := by omega
        have hro : out' = 100 := by simp [out', rWire, hout9, show 9 + C.gates.length ≤ C.output by omega]
        rw [hro]
        have hlenD : (run ((post.zipIdx wC2.length).map (fun p => rGate p.2 p.1)) wD1).length = 9 + C.gates.length := by
          rw [hpost_res.1, hlen_final]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [hlen_final]; omega)]
    exact ⟨D, hD_fan, hD_sz, hD_eval, hD_gates⟩

  -- Helper 2: Relabel inputs 0..8 by any automorphism σ of P9!
  have relabel_aut : ∀ (C : Circuit) (σ σi : Fin 9 → Fin 9),
      (∀ v : Fin 9, σi (σ v) = v) →
      (∀ v : Fin 9, σ (σi v) = v) →
      (∀ x : Fin 9 → Bool, fP9 (fun v => x (σ v)) = fP9 x) →
      FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = fP9 x) →
      let mp : ℕ → ℕ := fun k => if h : k < 9 then (σ ⟨k, h⟩).val else k
      let C' : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map mp⟩), mp C.output⟩
      FanInTwo C' ∧
      C'.size = C.size ∧
      (∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = fP9 x) := by
    intro C σ σi hinv1 hinv2 hfP9 hfan heval mp C'
    have hmp_lt9 : ∀ k, mp k < 9 ↔ k < 9 := fun k => by
      dsimp only [mp]; split_ifs with h
      · exact ⟨fun _ => h, fun _ => (σ ⟨k, h⟩).isLt⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h' h⟩
    have hC'_fan : FanInTwo C' := by
      intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      obtain ⟨hop, hlen⟩ := hfan g' hg'
      exact ⟨hop, by simp [hlen]⟩
    have hC'_sz : C'.size = C.size := by
      change (C.gates.map _).length = C.gates.length
      simp
    have hC'_eval : ∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = fP9 x := by
      intro x
      let y : Fin 9 → Bool := fun v => x (σ v)
      have hsim : ∀ (gs : List Gate) (w1 w2 : List Bool),
          w1.length = w2.length →
          9 ≤ w1.length →
          (∀ k (hk : k < 9), w1.getD (σ ⟨k, hk⟩).val false = w2.getD k false) →
          (∀ k, 9 ≤ k → w1.getD k false = w2.getD k false) →
          let w1' := run (gs.map (fun g => ⟨g.op, g.inputs.map mp⟩)) w1
          let w2' := run gs w2
          w1'.length = w2'.length ∧
          (∀ k (hk : k < 9), w1'.getD (σ ⟨k, hk⟩).val false = w2'.getD k false) ∧
          (∀ k, 9 ≤ k → w1'.getD k false = w2'.getD k false) := by
        intro gs
        induction gs with
        | nil => intro w1 w2 hl _ hlt hge; exact ⟨hl, hlt, hge⟩
        | cons g gs ih =>
          intro w1 w2 hl h9 hlt hge
          simp only [List.map_cons, run_cons]
          have hvg : vGate w1 ⟨g.op, g.inputs.map mp⟩ = vGate w2 g := by
            simp only [vGate, List.map_map]
            congr 1
            refine List.map_congr_left fun k _ => ?_
            simp only [Function.comp_apply, mp]
            split_ifs with hk
            · exact hlt k hk
            · exact hge k (by omega)
          rw [hvg]
          refine ih (w1 ++ [vGate w2 g]) (w2 ++ [vGate w2 g]) (by simp [hl]) (by simp; omega)
            (fun k hk => by
              have hlt1 : (σ ⟨k, hk⟩).val < w1.length := by have := (σ ⟨k, hk⟩).isLt; omega
              rw [getD_snoc_lt _ _ _ hlt1, getD_snoc_lt _ _ _ (by omega)]
              exact hlt k hk)
            (fun k hk => by
              by_cases hkl : k < w1.length
              · rw [getD_snoc_lt _ _ _ hkl, getD_snoc_lt _ _ _ (by omega)]
                exact hge k hk
              · by_cases hke : k = w1.length
                · subst hke
                  rw [getD_snoc_eq, hl, getD_snoc_eq]
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      have hres := hsim C.gates (List.ofFn x) (List.ofFn y) (by simp) (by simp)
        (fun k hk => by rw [getD_ofFn x (σ ⟨k, hk⟩), getD_ofFn y ⟨k, hk⟩])
        (fun k hk => by rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      have he1 : C'.eval (List.ofFn x) = C.eval (List.ofFn y) := by
        change (run (C.gates.map (fun g => ⟨g.op, g.inputs.map mp⟩)) (List.ofFn x)).getD (mp C.output) false =
          (run C.gates (List.ofFn y)).getD C.output false
        dsimp only [mp]
        split_ifs with ho
        · exact hres.2.1 C.output ho
        · exact hres.2.2 C.output (by omega)
      rw [he1, heval y, hfP9 x]
    exact ⟨hC'_fan, hC'_sz, hC'_eval⟩

  -- Explicit Aut(P9) permutations (all 12 elements, as Fin 9 -> Fin 9)
  let autL : List (List ℕ) := [
    [0, 1, 2, 3, 4, 5, 6, 7, 8],
    [0, 5, 8, 3, 4, 1, 7, 6, 2],
    [1, 0, 5, 8, 6, 2, 4, 7, 3],
    [1, 2, 3, 8, 6, 0, 7, 4, 5],
    [2, 1, 0, 5, 7, 3, 6, 4, 8],
    [2, 3, 8, 5, 7, 1, 4, 6, 0],
    [3, 2, 1, 0, 4, 8, 7, 6, 5],
    [3, 8, 5, 0, 4, 2, 6, 7, 1],
    [5, 0, 1, 2, 7, 8, 4, 6, 3],
    [5, 8, 3, 2, 7, 0, 6, 4, 1],
    [8, 3, 2, 1, 6, 5, 4, 7, 0],
    [8, 5, 0, 1, 6, 3, 7, 4, 2]
  ]
  let applyPerm : List ℕ → Fin 9 → Fin 9 := fun p v => Fin.ofNat 9 (p.getD v.val 0)
  have aut_ok : ∀ p ∈ autL,
      (∃ q ∈ autL, (∀ v : Fin 9, applyPerm q (applyPerm p v) = v) ∧ (∀ v : Fin 9, applyPerm p (applyPerm q v) = v)) ∧
      (∀ x : Fin 9 → Bool, fP9 (fun v => x (applyPerm p v)) = fP9 x) ∧
      (∀ i j : Fin 9, code (applyPerm p i).val (applyPerm p j).val ∈ S02 ↔ code i.val j.val ∈ S02) := by
    have hinv : autL.all (fun p => autL.any (fun q =>
        (List.finRange 9).all (fun v => decide (applyPerm q (applyPerm p v) = v) && decide (applyPerm p (applyPerm q v) = v)))) = true := by decide
    have hS02 : autL.all (fun p => (List.finRange 9).all (fun i => (List.finRange 9).all (fun j =>
        decide (code (applyPerm p i).val (applyPerm p j).val ∈ S02 ↔ code i.val j.val ∈ S02)))) = true := by decide
    let edges : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
    have hAdj : ∀ p ∈ autL,
        (∀ e ∈ edges, (applyPerm p e.1, applyPerm p e.2) ∈ edges ∨ (applyPerm p e.2, applyPerm p e.1) ∈ edges) ∧
        (∀ e ∈ edges, ∃ e' ∈ edges, (applyPerm p e'.1 = e.1 ∧ applyPerm p e'.2 = e.2) ∨ (applyPerm p e'.1 = e.2 ∧ applyPerm p e'.2 = e.1)) := by
      have h1 : autL.all (fun p => edges.all (fun e => edges.contains (applyPerm p e.1, applyPerm p e.2) || edges.contains (applyPerm p e.2, applyPerm p e.1))) = true := by decide
      have h2 : autL.all (fun p => edges.all (fun e => edges.any (fun e' =>
          (decide (applyPerm p e'.1 = e.1) && decide (applyPerm p e'.2 = e.2)) ||
          (decide (applyPerm p e'.1 = e.2) && decide (applyPerm p e'.2 = e.1))))) = true := by decide
      intro p hp
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have := List.all_eq_true.1 (List.all_eq_true.1 h1 p hp) e he
        simpa only [Bool.or_eq_true, List.contains_iff_mem] using this
      · have := List.all_eq_true.1 (List.all_eq_true.1 h2 p hp) e he
        simpa only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using this
    have hf_eq : ∀ x : Fin 9 → Bool, fP9 x = edges.any (fun e => x e.1 && x e.2) := fun x => by
      simp only [fP9, edges, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · have := List.all_eq_true.1 hinv p hp
      simp only [List.any_eq_true, List.all_eq_true, List.mem_finRange, Bool.and_eq_true, decide_eq_true_eq, true_implies] at this
      obtain ⟨q, hq, hqq⟩ := this
      exact ⟨q, hq, fun v => (hqq v).1, fun v => (hqq v).2⟩
    · intro x
      rw [hf_eq (fun v => x (applyPerm p v)), hf_eq x]
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true, Bool.and_eq_true]
      obtain ⟨hfwd, hbwd⟩ := hAdj p hp
      constructor
      · rintro ⟨e, he, h1, h2⟩
        rcases hfwd e he with hmem | hmem
        · exact ⟨(applyPerm p e.1, applyPerm p e.2), hmem, h1, h2⟩
        · exact ⟨(applyPerm p e.2, applyPerm p e.1), hmem, h2, h1⟩
      · rintro ⟨e, he, h1, h2⟩
        obtain ⟨e', he', hc⟩ := hbwd e he
        rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨e', he', by rw [e1]; exact h1, by rw [e2]; exact h2⟩
        · exact ⟨e', he', by rw [e1]; exact h2, by rw [e2]; exact h1⟩
    · intro i j
      have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hS02 p hp) i (List.mem_finRange i)) j (List.mem_finRange j)
      exact of_decide_eq_true this

  -- Main proof of L-meta-4340 from hNot, hFour, hOrb02, hOrb06!
  intro x1 hx1 C hfan hsz hno
  by_contra hContra
  have heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x x1.1 || x x1.2]) = fP9 x := by
    intro x
    by_contra hne
    exact hContra ⟨x, hne⟩
  -- Prepend gate g_first = OR(x1.1, x1.2) to form 15-gate circuit C' on 9 inputs!
  let gFirst : Gate := ⟨GateOp.or, [x1.1.val, x1.2.val]⟩
  let C' : Circuit := ⟨gFirst :: C.gates, C.output⟩
  have hC'_fan : FanInTwo C' := by
    intro g hg
    simp only [C', List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨by simp [gFirst], by simp [gFirst]⟩
    · exact hfan g hg
  have hC'_sz : C'.size ≤ 15 := by
    change (gFirst :: C.gates).length ≤ 15
    have : C.gates.length ≤ 14 := hsz
    simp; omega
  have hC'_eval : ∀ x : Fin 9 → Bool, C'.eval (List.ofFn x) = fP9 x := by
    intro x
    have hv : vGate (List.ofFn x) gFirst = (x x1.1 || x x1.2) := by
      change ([x1.1.val, x1.2.val].map (fun i => (List.ofFn x).getD i false)).any id = (x x1.1 || x x1.2)
      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id]
      rw [getD_ofFn x x1.1, getD_ofFn x x1.2]
    change (run (gFirst :: C.gates) (List.ofFn x)).getD C.output false = fP9 x
    rw [run_cons, hv]
    exact heval x
  have hC'_noAnd : ∀ g ∈ C'.gates, (∀ i ∈ g.inputs, i < 9) → g.op ≠ GateOp.and := by
    intro g hg hall
    simp only [C', List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [gFirst]
    · exact (hno g hg hall).1

  -- Step 1: Eliminate ALL gates with g.op = .not and g.inputs.headD 9 < 9 via hNot (= L-meta-4338)!
  have hC'_noNot : ∀ g ∈ C'.gates, g.op = GateOp.not → 9 ≤ g.inputs.headD 9 := by
    intro g hg hop
    by_contra hlt
    have hu9 : g.inputs.headD 9 < 9 := by omega
    let u : Fin 9 := ⟨g.inputs.headD 9, hu9⟩
    have hfind : ∃ p ∈ autL, applyPerm p u ∈ ([(0 : Fin 9), (4 : Fin 9)] : List (Fin 9)) := by
      have h : (List.finRange 9).all (fun v => autL.any (fun p => decide (applyPerm p v = 0) || decide (applyPerm p v = 4))) = true := by decide
      have h1 := List.all_eq_true.1 h u (List.mem_finRange u)
      simp only [List.any_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
      obtain ⟨p, hp, h04⟩ := h1
      refine ⟨p, hp, ?_⟩
      rcases h04 with h0 | h4
      · simp [h0]
      · simp [h4]
    obtain ⟨p, hp, hp04⟩ := hfind
    obtain ⟨⟨q, _, hinv1, hinv2⟩, hfP9, _⟩ := aut_ok p hp
    let σ := applyPerm p
    let mp : ℕ → ℕ := fun k => if h : k < 9 then (σ ⟨k, h⟩).val else k
    let C1 : Circuit := ⟨C'.gates.map (fun g => Gate.mk g.op (g.inputs.map mp)), mp C'.output⟩
    obtain ⟨hC1_fan, hC1_sz, hC1_eval⟩ := relabel_aut C' σ (applyPerm q) hinv1 hinv2 hfP9 hC'_fan hC'_eval
    change C1.size = C'.size at hC1_sz
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    let pre1 : List Gate := pre.map (fun g => Gate.mk g.op (g.inputs.map mp))
    let post1 : List Gate := post.map (fun g => Gate.mk g.op (g.inputs.map mp))
    let g1 : Gate := Gate.mk g.op (g.inputs.map mp)
    have hsplit1 : C1.gates = pre1 ++ g1 :: post1 := by
      simp [C1, hsplit, pre1, post1, g1]
    have hg1_val : ∀ x : Fin 9 → Bool, vGate (run pre1 (List.ofFn x)) g1 = !(x (σ u)) := by
      intro x
      cases hl : g.inputs with
      | nil => simp [hl] at hu9
      | cons a t =>
        have ha9 : a < 9 := by simpa [hl] using hu9
        have hau : ⟨a, ha9⟩ = u := by ext; simp [u, hl]
        have hvg_eq : vGate (run pre1 (List.ofFn x)) g1 = !((run pre1 (List.ofFn x)).getD (mp a) false) := by
          dsimp only [vGate, g1]
          rw [hop, hl]
          rfl
        rw [hvg_eq]
        have hmpa : mp a = (σ u).val := by simp [mp, ha9, hau]
        rw [hmpa, run_keep _ _ _ (by simp), getD_ofFn x (σ u)]
    obtain ⟨D, hD_fan, hD_sz, hD_eval, hD_gates⟩ :=
      extract_gate C1 pre1 post1 g1 (fun x => !(x (σ u))) hsplit1 hC1_fan (by omega) hC1_eval hg1_val
    have hD_noAnd : ∀ g' ∈ D.gates, (∀ i ∈ g'.inputs, i < 9) → g'.op ≠ GateOp.and := by
      intro g' hg' hall
      obtain ⟨g2, hg2, heqop, _, hlt_iff, _, _⟩ := hD_gates g' hg'
      have hg2_map : g2 ∈ (pre ++ post).map (fun g => Gate.mk g.op (g.inputs.map mp)) := by
        simpa [pre1, post1, List.map_append] using hg2
      rw [List.mem_map] at hg2_map
      obtain ⟨g0, hg0, rfl⟩ := hg2_map
      have hg0_C' : g0 ∈ C'.gates := by
        rw [hsplit]; simp only [List.mem_append] at hg0 ⊢
        exact hg0.imp id (List.mem_cons_of_mem g)
      have hall0 : ∀ i ∈ g0.inputs, i < 9 := by
        intro i hi
        have h1 := hlt_iff.1 hall (mp i) (List.mem_map_of_mem hi)
        dsimp only [mp] at h1
        split_ifs at h1 with h; exact h; omega
      rw [heqop]; exact hC'_noAnd g0 hg0_C' hall0
    obtain ⟨x, hx⟩ := hNot (σ u) hp04 D hD_fan (by omega) hD_noAnd
    exact hx (hD_eval x)

  -- Step 2: Eliminate ALL input-OR gates in orbits (0,4), (4,6), (0,1), (0,3) via hFour!
  have hC'_S02 : ∀ g ∈ C'.gates, ∀ i j : ℕ, i < 9 → j < 9 → i ≠ j → g.inputs = [i, j] → code i j ∈ S02 := by
    intro g hg i j hi hj hij hin
    by_contra hnotS02
    have hgop : g.op = GateOp.or := by
      have hop := (hC'_fan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · exact absurd h (hC'_noAnd g hg (fun k hk => by simp [hin] at hk; rcases hk with rfl | rfl <;> assumption))
      · exact h
      · have := hC'_noNot g hg h; simp [hin] at this; omega
    let u : Fin 9 := ⟨i, hi⟩
    let v : Fin 9 := ⟨j, hj⟩
    let fourList : List (Fin 9 × Fin 9) := [(0, 4), (4, 6), (0, 1), (0, 3)]
    have hfind : ∃ p ∈ autL, ∃ ab ∈ fourList, (applyPerm p u = ab.1 ∧ applyPerm p v = ab.2) ∨ (applyPerm p u = ab.2 ∧ applyPerm p v = ab.1) := by
      have h : (List.finRange 9).all (fun a => (List.finRange 9).all (fun b =>
          decide (a = b) || decide (code a.val b.val ∈ S02) ||
          autL.any (fun p => fourList.any (fun ab =>
            (decide (applyPerm p a = ab.1) && decide (applyPerm p b = ab.2)) ||
            (decide (applyPerm p a = ab.2) && decide (applyPerm p b = ab.1)))))) = true := by decide
      have h1 := List.all_eq_true.1 (List.all_eq_true.1 h u (List.mem_finRange u)) v (List.mem_finRange v)
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h1
      rcases h1 with (heq | hs02) | ⟨p, hp, ab, hab, hc⟩
      · exact absurd (congrArg Fin.val heq) hij
      · exact absurd hs02 hnotS02
      · exact ⟨p, hp, ab, hab, hc⟩
    obtain ⟨p, hp, ab, hab, hmap_uv⟩ := hfind
    obtain ⟨⟨q, _, hinv1, hinv2⟩, hfP9, _⟩ := aut_ok p hp
    let σ := applyPerm p
    let mp : ℕ → ℕ := fun k => if h : k < 9 then (σ ⟨k, h⟩).val else k
    let C1 : Circuit := ⟨C'.gates.map (fun g => Gate.mk g.op (g.inputs.map mp)), mp C'.output⟩
    obtain ⟨hC1_fan, hC1_sz, hC1_eval⟩ := relabel_aut C' σ (applyPerm q) hinv1 hinv2 hfP9 hC'_fan hC'_eval
    change C1.size = C'.size at hC1_sz
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    let pre1 : List Gate := pre.map (fun g => Gate.mk g.op (g.inputs.map mp))
    let post1 : List Gate := post.map (fun g => Gate.mk g.op (g.inputs.map mp))
    let g1 : Gate := Gate.mk g.op (g.inputs.map mp)
    have hsplit1 : C1.gates = pre1 ++ g1 :: post1 := by simp [C1, hsplit, pre1, post1, g1]
    have hg1_val : ∀ x : Fin 9 → Bool, vGate (run pre1 (List.ofFn x)) g1 = (x ab.1 || x ab.2) := by
      intro x
      have hvg_eq : vGate (run pre1 (List.ofFn x)) g1 =
          ((run pre1 (List.ofFn x)).getD (mp i) false || (run pre1 (List.ofFn x)).getD (mp j) false) := by
        dsimp only [vGate, g1]
        rw [hgop, hin]
        change ((run pre1 (List.ofFn x)).getD (mp i) false || ((run pre1 (List.ofFn x)).getD (mp j) false || false)) = _
        simp only [Bool.or_false]
      rw [hvg_eq]
      have hmi : mp i = (σ u).val := by simp [mp, hi, u]
      have hmj : mp j = (σ v).val := by simp [mp, hj, v]
      rw [hmi, hmj, run_keep _ _ _ (by simp), run_keep _ _ _ (by simp), getD_ofFn x (σ u), getD_ofFn x (σ v)]
      dsimp only [σ]
      rcases hmap_uv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Bool.or_comm]
    obtain ⟨D, hD_fan, hD_sz, hD_eval, hD_gates⟩ :=
      extract_gate C1 pre1 post1 g1 (fun x => x ab.1 || x ab.2) hsplit1 hC1_fan (by omega) hC1_eval hg1_val
    have hD_noAnd : ∀ g' ∈ D.gates, (∀ k ∈ g'.inputs, k < 9) → g'.op ≠ GateOp.and := by
      intro g' hg' hall
      obtain ⟨g2, hg2, heqop, _, hlt_iff, _, _⟩ := hD_gates g' hg'
      have hg2_map : g2 ∈ (pre ++ post).map (fun g => Gate.mk g.op (g.inputs.map mp)) := by
        simpa [pre1, post1, List.map_append] using hg2
      rw [List.mem_map] at hg2_map; obtain ⟨g0, hg0, rfl⟩ := hg2_map
      have hg0_C' : g0 ∈ C'.gates := by rw [hsplit]; simp only [List.mem_append] at hg0 ⊢; exact hg0.imp id (List.mem_cons_of_mem g)
      have hall0 : ∀ k ∈ g0.inputs, k < 9 := fun k hk => by
        have h1 := hlt_iff.1 hall (mp k) (List.mem_map_of_mem hk)
        dsimp only [mp] at h1; split_ifs at h1 with h; exact h; omega
      rw [heqop]; exact hC'_noAnd g0 hg0_C' hall0
    have hD_noNot : ∀ g' ∈ D.gates, g'.op = GateOp.not → 9 ≤ g'.inputs.headD 9 := by
      intro g' hg' hop'
      obtain ⟨g2, hg2, heqop, _, _, hhd_iff, _⟩ := hD_gates g' hg'
      have hg2_map : g2 ∈ (pre ++ post).map (fun g => Gate.mk g.op (g.inputs.map mp)) := by
        simpa [pre1, post1, List.map_append] using hg2
      rw [List.mem_map] at hg2_map; obtain ⟨g0, hg0, rfl⟩ := hg2_map
      have hg0_C' : g0 ∈ C'.gates := by rw [hsplit]; simp only [List.mem_append] at hg0 ⊢; exact hg0.imp id (List.mem_cons_of_mem g)
      have h0 := hC'_noNot g0 hg0_C' (heqop ▸ hop')
      apply hhd_iff.2
      cases hl : g0.inputs with
      | nil => simp
      | cons a t =>
        simp only [hl, List.map_cons, List.headD_cons] at h0 ⊢
        simp [mp, show ¬ a < 9 by omega]; omega
    obtain ⟨x, hx⟩ := hFour ab hab D hD_fan (by omega) hD_noAnd hD_noNot
    exact hx (hD_eval x)

  -- Step 3: Eliminate ALL input-OR gates in orbit (0,2) via hOrb02!
  have hC'_S06 : ∀ g ∈ C'.gates, ∀ i j : ℕ, i < 9 → j < 9 → i ≠ j → g.inputs = [i, j] → code i j ∈ S06 := by
    intro g hg i j hi hj hij hin
    by_contra hnotS06
    have hinS02 : code i j ∈ S02 := hC'_S02 g hg i j hi hj hij hin
    have hgop : g.op = GateOp.or := by
      have hop := (hC'_fan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · exact absurd h (hC'_noAnd g hg (fun k hk => by simp [hin] at hk; rcases hk with rfl | rfl <;> assumption))
      · exact h
      · have := hC'_noNot g hg h; simp [hin] at this; omega
    let u : Fin 9 := ⟨i, hi⟩
    let v : Fin 9 := ⟨j, hj⟩
    have hfind : ∃ p ∈ autL, (applyPerm p u = 0 ∧ applyPerm p v = 2) ∨ (applyPerm p u = 2 ∧ applyPerm p v = 0) := by
      have h : (List.finRange 9).all (fun a => (List.finRange 9).all (fun b =>
          decide (a = b) || !decide (code a.val b.val ∈ S02) || decide (code a.val b.val ∈ S06) ||
          autL.any (fun p =>
            (decide (applyPerm p a = 0) && decide (applyPerm p b = 2)) ||
            (decide (applyPerm p a = 2) && decide (applyPerm p b = 0))))) = true := by decide
      have h1 := List.all_eq_true.1 (List.all_eq_true.1 h u (List.mem_finRange u)) v (List.mem_finRange v)
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h1
      rcases h1 with ((heq | hns02) | hs06) | ⟨p, hp, hc⟩
      · exact absurd (congrArg Fin.val heq) hij
      · exact absurd hinS02 hns02
      · exact absurd hs06 hnotS06
      · exact ⟨p, hp, hc⟩
    obtain ⟨p, hp, hmap_uv⟩ := hfind
    obtain ⟨⟨q, _, hinv1, hinv2⟩, hfP9, hpresS02⟩ := aut_ok p hp
    let σ := applyPerm p
    let mp : ℕ → ℕ := fun k => if h : k < 9 then (σ ⟨k, h⟩).val else k
    let C1 : Circuit := ⟨C'.gates.map (fun g => Gate.mk g.op (g.inputs.map mp)), mp C'.output⟩
    obtain ⟨hC1_fan, hC1_sz, hC1_eval⟩ := relabel_aut C' σ (applyPerm q) hinv1 hinv2 hfP9 hC'_fan hC'_eval
    change C1.size = C'.size at hC1_sz
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    let pre1 : List Gate := pre.map (fun g => Gate.mk g.op (g.inputs.map mp))
    let post1 : List Gate := post.map (fun g => Gate.mk g.op (g.inputs.map mp))
    let g1 : Gate := Gate.mk g.op (g.inputs.map mp)
    have hsplit1 : C1.gates = pre1 ++ g1 :: post1 := by simp [C1, hsplit, pre1, post1, g1]
    have hg1_val : ∀ x : Fin 9 → Bool, vGate (run pre1 (List.ofFn x)) g1 = (x 0 || x 2) := by
      intro x
      have hvg_eq : vGate (run pre1 (List.ofFn x)) g1 =
          ((run pre1 (List.ofFn x)).getD (mp i) false || (run pre1 (List.ofFn x)).getD (mp j) false) := by
        dsimp only [vGate, g1]
        rw [hgop, hin]
        change ((run pre1 (List.ofFn x)).getD (mp i) false || ((run pre1 (List.ofFn x)).getD (mp j) false || false)) = _
        simp only [Bool.or_false]
      rw [hvg_eq]
      have hmi : mp i = (σ u).val := by simp [mp, hi, u]
      have hmj : mp j = (σ v).val := by simp [mp, hj, v]
      rw [hmi, hmj, run_keep _ _ _ (by simp), run_keep _ _ _ (by simp), getD_ofFn x (σ u), getD_ofFn x (σ v)]
      dsimp only [σ]
      rcases hmap_uv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Bool.or_comm]
    obtain ⟨D, hD_fan, hD_sz, hD_eval, hD_gates⟩ :=
      extract_gate C1 pre1 post1 g1 (fun x => x 0 || x 2) hsplit1 hC1_fan (by omega) hC1_eval hg1_val
    have hD_noAnd : ∀ g' ∈ D.gates, (∀ k ∈ g'.inputs, k < 9) → g'.op ≠ GateOp.and := by
      intro g' hg' hall
      obtain ⟨g2, hg2, heqop, _, hlt_iff, _, _⟩ := hD_gates g' hg'
      have hg2_map : g2 ∈ (pre ++ post).map (fun g => Gate.mk g.op (g.inputs.map mp)) := by
        simpa [pre1, post1, List.map_append] using hg2
      rw [List.mem_map] at hg2_map; obtain ⟨g0, hg0, rfl⟩ := hg2_map
      have hg0_C' : g0 ∈ C'.gates := by rw [hsplit]; simp only [List.mem_append] at hg0 ⊢; exact hg0.imp id (List.mem_cons_of_mem g)
      have hall0 : ∀ k ∈ g0.inputs, k < 9 := fun k hk => by
        have h1 := hlt_iff.1 hall (mp k) (List.mem_map_of_mem hk)
        dsimp only [mp] at h1; split_ifs at h1 with h; exact h; omega
      rw [heqop]; exact hC'_noAnd g0 hg0_C' hall0
    have hD_noNot : ∀ g' ∈ D.gates, g'.op = GateOp.not → 9 ≤ g'.inputs.headD 9 := by
      intro g' hg' hop'
      obtain ⟨g2, hg2, heqop, _, _, hhd_iff, _⟩ := hD_gates g' hg'
      have hg2_map : g2 ∈ (pre ++ post).map (fun g => Gate.mk g.op (g.inputs.map mp)) := by
        simpa [pre1, post1, List.map_append] using hg2
      rw [List.mem_map] at hg2_map; obtain ⟨g0, hg0, rfl⟩ := hg2_map
      have hg0_C' : g0 ∈ C'.gates := by rw [hsplit]; simp only [List.mem_append] at hg0 ⊢; exact hg0.imp id (List.mem_cons_of_mem g)
      have h0 := hC'_noNot g0 hg0_C' (heqop ▸ hop')
      apply hhd_iff.2
      cases hl : g0.inputs with
      | nil => simp
      | cons a t =>
        simp only [hl, List.map_cons, List.headD_cons] at h0 ⊢
        simp [mp, show ¬ a < 9 by omega]; omega
    have hD_S02 : ∀ g' ∈ D.gates, ∀ a b : ℕ, a < 9 → b < 9 → a ≠ b → g'.inputs = [a, b] → code a b ∈ S02 := by
      intro g' hg' a b ha hb hab hin'
      obtain ⟨g2, hg2, _, _, _, _, hij_iff⟩ := hD_gates g' hg'
      have hg2_in : g2.inputs = [a, b] := (hij_iff a b ha hb).1 hin'
      have hg2_map : g2 ∈ (pre ++ post).map (fun g => Gate.mk g.op (g.inputs.map mp)) := by
        simpa [pre1, post1, List.map_append] using hg2
      rw [List.mem_map] at hg2_map; obtain ⟨g0, hg0, hge⟩ := hg2_map
      subst hge
      have hg0_C' : g0 ∈ C'.gates := by rw [hsplit]; simp only [List.mem_append] at hg0 ⊢; exact hg0.imp id (List.mem_cons_of_mem g)
      cases hl : g0.inputs with
      | nil => simp [hl] at hg2_in
      | cons a0 t =>
        cases t with
        | nil => simp [hl] at hg2_in
        | cons b0 t' =>
          cases t' with
          | nil =>
            simp only [hl, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hg2_in
            obtain ⟨ha0_eq, hb0_eq⟩ := hg2_in
            have ha0 : a0 < 9 := by dsimp only [mp] at ha0_eq; split_ifs at ha0_eq with h; exact h; omega
            have hb0 : b0 < 9 := by dsimp only [mp] at hb0_eq; split_ifs at hb0_eq with h; exact h; omega
            have hab0 : a0 ≠ b0 := fun e => hab (by rw [← ha0_eq, ← hb0_eq, e])
            have hc0 := hC'_S02 g0 hg0_C' a0 b0 ha0 hb0 hab0 hl
            have ha_val : (σ ⟨a0, ha0⟩).val = a := by simpa [mp, ha0] using ha0_eq
            have hb_val : (σ ⟨b0, hb0⟩).val = b := by simpa [mp, hb0] using hb0_eq
            rw [← ha_val, ← hb_val]
            exact (hpresS02 ⟨a0, ha0⟩ ⟨b0, hb0⟩).2 hc0
          | cons _ _ => simp [hl] at hg2_in
    obtain ⟨x, hx⟩ := hOrb02 D hD_fan (by omega) hD_noAnd hD_noNot hD_S02
    exact hx (hD_eval x)

  -- Step 4: Now gFirst ∈ C'.gates forces x1 = (0, 6), and C itself contradicts hOrb06!
  have hx1_06 : x1 = ((0 : Fin 9), (6 : Fin 9)) := by
    have hmem : gFirst ∈ C'.gates := List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
    rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl
    · have := hC'_S06 gFirst hmem 0 1 (by omega) (by omega) (by omega) rfl; simp [code, S06] at this
    · have := hC'_S06 gFirst hmem 0 2 (by omega) (by omega) (by omega) rfl; simp [code, S06] at this
    · have := hC'_S06 gFirst hmem 0 3 (by omega) (by omega) (by omega) rfl; simp [code, S06] at this
    · have := hC'_S06 gFirst hmem 0 4 (by omega) (by omega) (by omega) rfl; simp [code, S06] at this
    · rfl
    · have := hC'_S06 gFirst hmem 4 6 (by omega) (by omega) (by omega) rfl; simp [code, S06] at this
  subst hx1_06
  obtain ⟨x, hx⟩ := hOrb06 C hfan hsz
    (fun g hg hall => (hno g hg hall).1)
    (fun g hg hop => hC'_noNot g (List.mem_cons_of_mem _ hg) hop)
    (fun g hg i j hi hj hij hin => hC'_S06 g (List.mem_cons_of_mem _ hg) i j hi hj hij hin)
  exact hx (heval x)
