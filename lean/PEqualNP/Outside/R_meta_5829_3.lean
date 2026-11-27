import Mathlib.Data.List.GetD
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5829_3
    (hVar0 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x7 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate };
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 ((10 : ℕ) + ↑x3) = Bool.true ∧ x9 x10 ((10 : ℕ) + ↑x4) = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x11 ((10 : ℕ) + ↑x4) = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x12 ((10 : ℕ) + ↑x4) = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x13 ((10 : ℕ) + ↑x4) = Bool.false)
    (hConst : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x7 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(10 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate };
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 ((10 : ℕ) + ↑x3) = Bool.true ∧ x9 x10 ((10 : ℕ) + ↑x4) = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x11 ((10 : ℕ) + ↑x4) = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x12 ((10 : ℕ) + ↑x4) = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x13 ((10 : ℕ) + ↑x4) = Bool.false) :
    (∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x1] : PEqualNP.CircuitLowerBounds.Gate };       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));       have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x7], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;       (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 ((10 : ℕ) + ↑x3) = Bool.true ∧ x9 x10 ((10 : ℕ) + ↑x4) = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x11 ((10 : ℕ) + ↑x4) = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x12 ((10 : ℕ) + ↑x4) = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 ((10 : ℕ) + ↑x3) = Bool.false ∧ x9 x13 ((10 : ℕ) + ↑x4) = Bool.false) := by
  intro x1 x2 x3 x4 hfan hsize x7 fP wOrig hA hB hC
  by_cases h10 : x1.val = 10
  · have hx1 : x1 = (10 : Fin 11) := Fin.ext h10
    subst hx1
    exact hConst x2 x3 x4 hfan hsize hA hB hC
  · have hkLt : x1.val < 10 := by omega
    let k : Fin 10 := ⟨x1.val, hkLt⟩
    let aut0 : Fin 10 → Fin 10 → Fin 10 := fun a i =>
      Fin.ofNat 10 ((([[0,1,2,3,4,5,6,7,8,9], [1,0,4,3,2,6,5,9,8,7], [2,1,0,4,3,7,6,5,9,8],
        [2,3,4,0,1,7,8,9,5,6], [1,2,3,4,0,6,7,8,9,5], [1,2,3,8,6,0,7,4,5,9],
        [2,1,6,8,3,7,0,9,5,4], [2,3,4,9,7,1,8,0,6,5], [2,3,8,5,7,1,4,6,0,9],
        [2,3,8,6,1,7,4,5,9,0]] : List (List ℕ)).getD a.val []).getD i.val 0)
    let inv0 : Fin 10 → Fin 10 → Fin 10 := fun a i =>
      Fin.ofNat 10 ((([[0,1,2,3,4,5,6,7,8,9], [1,0,4,3,2,6,5,9,8,7], [2,1,0,4,3,7,6,5,9,8],
        [3,4,0,1,2,8,9,5,6,7], [4,0,1,2,3,9,5,6,7,8], [5,0,1,2,7,8,4,6,3,9],
        [6,1,0,4,9,8,2,5,3,7], [7,5,0,1,2,9,8,4,6,3], [8,5,0,1,6,3,7,4,2,9],
        [9,4,0,1,6,7,3,5,2,8]] : List (List ℕ)).getD a.val []).getD i.val 0)
    have hautFix : ∀ a : Fin 10, aut0 a a = 0 := by decide
    have hautLeft : ∀ a i : Fin 10, inv0 a (aut0 a i) = i := by decide
    have hautRight : ∀ a i : Fin 10, aut0 a (inv0 a i) = i := by decide
    let edges : List (Fin 10 × Fin 10) :=
      [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    let adj : Fin 10 → Fin 10 → Bool := fun i j =>
      edges.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)
    have hautEdge : ∀ a : Fin 10, edges.all (fun e => adj (aut0 a e.1) (aut0 a e.2)) = true := by decide
    have hinvEdge : ∀ a : Fin 10, edges.all (fun e => adj (inv0 a e.1) (inv0 a e.2)) = true := by decide
    have hfPEq : ∀ x : Fin 10 → Bool, fP x = true ↔ ∃ e ∈ edges, x e.1 = true ∧ x e.2 = true := by
      intro x
      dsimp only [fP, edges]
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h
        simp only [or_assoc] at h
        rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
        · exact ⟨(0, 1), by simp, h.1, h.2⟩
        · exact ⟨(1, 2), by simp, h.1, h.2⟩
        · exact ⟨(2, 3), by simp, h.1, h.2⟩
        · exact ⟨(3, 4), by simp, h.1, h.2⟩
        · exact ⟨(4, 0), by simp, h.1, h.2⟩
        · exact ⟨(0, 5), by simp, h.1, h.2⟩
        · exact ⟨(1, 6), by simp, h.1, h.2⟩
        · exact ⟨(2, 7), by simp, h.1, h.2⟩
        · exact ⟨(3, 8), by simp, h.1, h.2⟩
        · exact ⟨(4, 9), by simp, h.1, h.2⟩
        · exact ⟨(5, 7), by simp, h.1, h.2⟩
        · exact ⟨(7, 9), by simp, h.1, h.2⟩
        · exact ⟨(9, 6), by simp, h.1, h.2⟩
        · exact ⟨(6, 8), by simp, h.1, h.2⟩
        · exact ⟨(8, 5), by simp, h.1, h.2⟩
      · rintro ⟨e, he, h1, h2⟩
        rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [h1, h2]
    have hadjMem : ∀ i j : Fin 10, adj i j = true → ∃ e ∈ edges, (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) := by
      intro i j h
      dsimp only [adj] at h
      obtain ⟨e, he, hcond⟩ := List.any_eq_true.mp h
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
      exact ⟨e, he, hcond⟩
    have hfPAut : ∀ (y : Fin 10 → Bool), fP (fun i => y (aut0 k i)) = fP y := by
      intro y
      apply Bool.eq_iff_iff.mpr
      rw [hfPEq (fun i => y (aut0 k i)), hfPEq y]
      constructor
      · rintro ⟨e, he, h1, h2⟩
        have hadj := List.all_eq_true.mp (hautEdge k) e he
        obtain ⟨e', he', hcond⟩ := hadjMem _ _ hadj
        rcases hcond with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨e', he', ha ▸ h1, hb ▸ h2⟩
        · exact ⟨e', he', ha ▸ h2, hb ▸ h1⟩
      · rintro ⟨e, he, h1, h2⟩
        have hadj := List.all_eq_true.mp (hinvEdge k) e he
        obtain ⟨e', he', hcond⟩ := hadjMem _ _ hadj
        rcases hcond with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨e', he', by rw [ha, hautRight]; exact h1, by rw [hb, hautRight]; exact h2⟩
        · exact ⟨e', he', by rw [ha, hautRight]; exact h2, by rw [hb, hautRight]; exact h1⟩
    let rwWire : ℕ → ℕ := fun w => if h : w < 10 then (aut0 k ⟨w, h⟩).val else w
    let x2' : PEqualNP.CircuitLowerBounds.Circuit :=
      { gates := x2.gates.map fun g => { op := g.op, inputs := g.inputs.map rwWire }, output := x2.output }
    have hfan' : PEqualNP.MetaComplexity.FanInTwo x2' := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop, hlen⟩ := hfan g0 hg0
      exact ⟨hop, by simp [hlen]⟩
    have hsize' : x2'.size ≤ 17 := by
      change x2'.gates.length ≤ 17
      dsimp only [x2']
      rw [List.length_map]
      exact hsize
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun ws g =>
      ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws1 ws2 : List Bool),
        ws1.length = ws2.length → 10 ≤ ws1.length →
        (∀ i : ℕ, ws1.getD i false = ws2.getD (rwWire i) false) →
        (gs.foldl step ws1).length = ((gs.map fun g => { op := g.op, inputs := g.inputs.map rwWire : PEqualNP.CircuitLowerBounds.Gate }).foldl step ws2).length ∧
        ∀ i : ℕ, (gs.foldl step ws1).getD i false =
          ((gs.map fun g => { op := g.op, inputs := g.inputs.map rwWire : PEqualNP.CircuitLowerBounds.Gate }).foldl step ws2).getD (rwWire i) false := by
      intro gs
      induction gs with
      | nil =>
        intro ws1 ws2 hlen _ hget
        exact ⟨hlen, hget⟩
      | cons g gs ih =>
        intro ws1 ws2 hlen h10len hget
        simp only [List.map_cons, List.foldl_cons]
        have hstepEq : g.op.eval (g.inputs.map fun i => ws1.getD i false) =
            g.op.eval ((g.inputs.map rwWire).map fun i => ws2.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact hget i
        apply ih (step ws1 g) (step ws2 { op := g.op, inputs := g.inputs.map rwWire })
        · simp only [step, List.length_append, List.length_singleton, hlen]
        · simp only [step, List.length_append, List.length_singleton]; omega
        · intro i
          dsimp only [step]
          by_cases hi10 : i < 10
          · have hrwLt : rwWire i < 10 := by
              dsimp only [rwWire]; simp only [hi10, ↓reduceDIte]; exact (aut0 k ⟨i, hi10⟩).isLt
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            exact hget i
          · have hrwEq : rwWire i = i := by dsimp only [rwWire]; simp only [hi10, ↓reduceDIte]
            rw [hrwEq]
            by_cases hiLt : i < ws1.length
            · rw [List.getD_append _ _ _ _ hiLt, List.getD_append _ _ _ _ (by omega)]
              simpa [hrwEq] using hget i
            · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]
              cases hsub : i - ws2.length with
              | zero => simp only [List.getD_cons_zero]; exact hstepEq
              | succ m => simp
    have hwireCorr : ∀ (y : Fin 10 → Bool) (m : ℕ), 10 ≤ m →
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD m false =
        wOrig (fun i => y (aut0 k i)) m := by
      intro y m hm
      let ws1 := ({ gates := [x7], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (fun i => y (aut0 k i))))
      let ws2 := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))
      have hws1Len : ws1.length = 11 := by
        dsimp only [ws1, PEqualNP.CircuitLowerBounds.Circuit.wires]; simp
      have hws2Len : ws2.length = 11 := by
        dsimp only [ws2, PEqualNP.CircuitLowerBounds.Circuit.wires]; simp
      have hwsGet : ∀ i : ℕ, ws1.getD i false = ws2.getD (rwWire i) false := by
        intro i
        by_cases hi10 : i < 10
        · have hrw : rwWire i = (aut0 k ⟨i, hi10⟩).val := by dsimp only [rwWire]; simp [hi10]
          rw [hrw]
          dsimp only [ws1, ws2, PEqualNP.CircuitLowerBounds.Circuit.wires]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [List.getD_append _ _ _ _ (by simp [hi10]), List.getD_append _ _ _ _ (by simp [(aut0 k ⟨i, hi10⟩).isLt])]
          rw [List.getD_eq_getElem _ _ (by simp [hi10]), List.getD_eq_getElem _ _ (by simp [(aut0 k ⟨i, hi10⟩).isLt])]
          rw [List.getElem_ofFn, List.getElem_ofFn]
        · have hrw : rwWire i = i := by dsimp only [rwWire]; simp [hi10]
          rw [hrw]
          by_cases hi11 : i = 10
          · subst hi11
            have eval_not : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun _ => rfl
            dsimp only [ws1, ws2, x7, PEqualNP.CircuitLowerBounds.Circuit.wires]
            simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, eval_not, List.headD_cons]
            rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
            simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
            rw [List.getD_eq_getElem _ _ (by simp [hkLt]), List.getD_eq_getElem _ _ (by simp)]
            simp only [List.getElem_ofFn]
            have hfix := hautFix k
            dsimp only [k] at hfix
            rw [hfix]
            rfl
          · have hgt : 11 ≤ i := by omega
            rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hres := (hfold x2.gates ws1 ws2 (by omega) (by omega) hwsGet).2 m
      have hrwm : rwWire m = m := by dsimp only [rwWire]; simp [Nat.not_lt.mpr hm]
      rw [hrwm] at hres
      exact hres.symm
    have hA' : ∃ y : Fin 10 → Bool,
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (10 + ↑x3) false = true ∧
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (10 + ↑x4) false = false := by
      obtain ⟨x10, h1, h2⟩ := hA
      refine ⟨fun j => x10 (inv0 k j), ?_, ?_⟩
      · rw [hwireCorr _ _ (by omega)]
        have heq : (fun i => x10 (inv0 k (aut0 k i))) = x10 := funext fun i => by rw [hautLeft]
        rw [heq]; exact h1
      · rw [hwireCorr _ _ (by omega)]
        have heq : (fun i => x10 (inv0 k (aut0 k i))) = x10 := funext fun i => by rw [hautLeft]
        rw [heq]; exact h2
    have hB' : ∃ y : Fin 10 → Bool,
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (10 + ↑x3) false = false ∧
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (10 + ↑x4) false = true := by
      obtain ⟨x11, h1, h2⟩ := hB
      refine ⟨fun j => x11 (inv0 k j), ?_, ?_⟩
      · rw [hwireCorr _ _ (by omega)]
        have heq : (fun i => x11 (inv0 k (aut0 k i))) = x11 := funext fun i => by rw [hautLeft]
        rw [heq]; exact h1
      · rw [hwireCorr _ _ (by omega)]
        have heq : (fun i => x11 (inv0 k (aut0 k i))) = x11 := funext fun i => by rw [hautLeft]
        rw [heq]; exact h2
    have hC' : ∀ y : Fin 10 → Bool, fP y = false →
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (10 + ↑x3) false = false ∧
        (x2'.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (10 + ↑x4) false = false := by
      intro y hy
      rw [hwireCorr _ _ (by omega), hwireCorr _ _ (by omega)]
      exact hC (fun i => y (aut0 k i)) (by rw [hfPAut]; exact hy)
    obtain ⟨y13, hy1, hy2, hy3⟩ := hVar0 x2' x3 x4 hfan' hsize' hA' hB' hC'
    refine ⟨fun i => y13 (aut0 k i), ?_, ?_, ?_⟩
    · rw [hfPAut]; exact hy1
    · rw [← hwireCorr y13 (10 + ↑x3) (by omega)]; exact hy2
    · rw [← hwireCorr y13 (10 + ↑x4) (by omega)]; exact hy3
