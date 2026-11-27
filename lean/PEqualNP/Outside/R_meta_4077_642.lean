import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4077_642
    (hNot : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x4) = x1 x4) → (15 : ℕ) + PEqualNP.NotBracket.notCount x2 ≤ x2.size)
    (hNon34 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (3 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (4 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))))
    (hRest : ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) → PEqualNP.NotBracket.notCount x2 ≤ (if x1 = Bool.true then (4 : ℕ) else (2 : ℕ)) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true) :
    (∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true) := by
  intro x1 x2 x3 x4 hfan hsize x7 x8 H1 H2 H3
  by_contra hneg
  letI decOp : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  have exactPair : ∀ x : Fin 10 → Bool, (x8 x x3 && x8 x x4) = x7 x := by
    intro x
    cases hx : x7 x
    · cases hA : x8 x x3 <;> cases hB : x8 x x4 <;> try rfl
      exact (hneg ⟨x, hx, hA, hB⟩).elim
    · obtain ⟨hA, hB⟩ := H3 x hx
      rw [hA, hB]; rfl
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have lengthRun : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; rfl
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hsz : x2.size = x2.gates.length := rfl
  let seed : (Fin 10 → Bool) → List Bool := fun x =>
    List.ofFn x ++ [x 0 || if x1 = Bool.true then x 1 else x 2]
  have seedLen : ∀ x, (seed x).length = 11 := by intro x; simp [seed]
  have hW : ∀ x i, x8 x i = (x2.gates.foldl step (seed x)).getD i false := fun _ _ => rfl
  have bound : ∀ i, (∀ x, x7 x = true → x8 x i = true) → i < 11 + x2.gates.length := by
    intro i h
    let xa : Fin 10 → Bool := fun j => decide (j.val = 0 ∨ j.val = 1)
    have hxa : x8 xa i = true := h xa (by decide)
    by_contra hi
    rw [hW, List.getD_eq_default _ _ (by rw [lengthRun, seedLen]; omega)] at hxa
    exact Bool.false_ne_true hxa
  have hb3 := bound x3 (fun x hx => (H3 x hx).1)
  have hb4 := bound x4 (fun x hx => (H3 x hx).2)
  let fin : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [x3, x4]⟩
  have finEval : ∀ W : List Bool, W.length = 11 + x2.gates.length →
      (step W fin).getD (11 + x2.gates.length) false = (W.getD x3 false && W.getD x4 false) := by
    intro W hlen
    change (W ++ [fin.op.eval (fin.inputs.map fun i => W.getD i false)]).getD (11 + x2.gates.length) false = _
    rw [← hlen, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem_cons_zero]
    change [W.getD x3 false, W.getD x4 false].all id = _
    cases W.getD x3 false <;> cases W.getD x4 false <;> rfl
  have ncDef : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.NotBracket.notCount C =
      (C.gates.filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length := fun _ => rfl
  have ncX2 := ncDef x2
  let seedG : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, if x1 = Bool.true then 1 else 2]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨seedG :: (x2.gates ++ [fin]), 11 + x2.gates.length⟩
  have seedStep : ∀ x : Fin 10 → Bool, step (List.ofFn x) seedG = seed x := by
    intro x
    have g0 : (List.ofFn x).getD 0 false = x 0 := by simp
    have g1 : (List.ofFn x).getD 1 false = x 1 := by simp
    have g2 : (List.ofFn x).getD 2 false = x 2 := by simp
    cases x1
    · change List.ofFn x ++ [[(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false].any id] = _
      rw [g0, g2]
      show _ = List.ofFn x ++ [x 0 || x 2]
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
    · change List.ofFn x ++ [[(List.ofFn x).getD 0 false, (List.ofFn x).getD 1 false].any id] = _
      rw [g0, g1]
      show _ = List.ofFn x ++ [x 0 || x 1]
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
  have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with hg | hg
    · subst hg; exact ⟨Or.inr (Or.inl rfl), le_refl _⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact hfan g hg
    · rw [List.mem_singleton] at hg
      subst hg
      exact ⟨Or.inl rfl, le_refl _⟩
  have evalD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = x7 x := by
    intro x
    change ((seedG :: (x2.gates ++ [fin])).foldl step (List.ofFn x)).getD (11 + x2.gates.length) false = _
    rw [List.foldl_cons, seedStep, List.foldl_append, List.foldl_cons, List.foldl_nil,
      finEval _ (by rw [lengthRun, seedLen])]
    exact exactPair x
  have ncD : PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount x2 := by
    rw [ncDef D, ncX2]
    change ((seedG :: (x2.gates ++ [fin])).filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = _
    have nOr : ¬ decide (PEqualNP.CircuitLowerBounds.GateOp.or = PEqualNP.CircuitLowerBounds.GateOp.not) = true := by decide
    have nAnd : ¬ decide (PEqualNP.CircuitLowerBounds.GateOp.and = PEqualNP.CircuitLowerBounds.GateOp.not) = true := by decide
    rw [List.filter_cons_of_neg (p := fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) (a := seedG) nOr,
      List.filter_append,
      List.filter_cons_of_neg (p := fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) (a := fin) nAnd,
      List.filter_nil, List.append_nil]
  have szD : D.size = x2.gates.length + 2 := by
    change (seedG :: (x2.gates ++ [fin])).length = _
    simp
  have nc4 : PEqualNP.NotBracket.notCount x2 ≤ 4 := by
    have := hNot D fanD evalD
    rw [ncD, szD] at this
    omega
  cases x1 with
  | true => exact hneg (hRest Bool.true x2 x3 x4 hfan hsize nc4 H1 H2 H3)
  | false =>
  by_cases hsmall : PEqualNP.NotBracket.notCount x2 ≤ 2
  · exact hneg (hRest Bool.false x2 x3 x4 hfan hsize hsmall H1 H2 H3)
  let norm : ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun L g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => PEqualNP.CircuitLowerBounds.Gate)
      (if g.inputs.all (fun i => decide (i < L)) then g else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, g.inputs.filter fun i => decide (i < L)⟩
      ⟨PEqualNP.CircuitLowerBounds.GateOp.not, (g.inputs.take 1).filter fun i => decide (i < L)⟩
      (fun _ => g) g g.op
  have hge3 : 3 ≤ PEqualNP.NotBracket.notCount x2 := by omega
  have evAnd : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have evOr : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have evNot : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  let ops : PEqualNP.CircuitLowerBounds.Gate → Prop := fun g =>
    g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  have fanOps : ∀ g ∈ x2.gates, ops g := by
    intro g hg
    have h := (hfan g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have orAny : ∀ (ws : List Bool) (ins : List ℕ),
      ((ins.filter fun i => decide (i < ws.length)).map fun i => ws.getD i false).any id =
        (ins.map fun i => ws.getD i false).any id := by
    intro ws ins
    induction ins with
    | nil => rfl
    | cons a rest ih =>
      by_cases ha : a < ws.length
      · simp only [List.filter_cons, ha, decide_true, if_true, List.map_cons, List.any_cons, ih]
      · have hd : ws.getD a false = false := List.getD_eq_default _ _ (by omega)
        simp only [List.filter_cons, ha, decide_false, Bool.false_eq_true, if_false, List.map_cons,
          List.any_cons, ih, hd, id_eq, Bool.false_or]
  have gateOk : ∀ (ws : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), ops g →
      step ws (norm ws.length g) = step ws g := by
    intro ws g hop
    obtain ⟨op, ins⟩ := g
    rcases hop with h | h | h <;> (change op = _ at h) <;> subst h
    · have e : norm ws.length ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ =
          (if ins.all (fun i => decide (i < ws.length)) then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩
            else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩) := rfl
      by_cases hall : ins.all (fun i => decide (i < ws.length)) = true
      · rw [e, if_pos hall]
      · rw [e, if_neg hall]
        rw [List.all_eq_true] at hall
        push_neg at hall
        obtain ⟨i, hi, hil⟩ := hall
        have hd : ws.getD i false = false := List.getD_eq_default _ _ (by simpa using hil)
        change ws ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval []] =
          ws ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (ins.map fun i => ws.getD i false)]
        rw [evOr, evAnd]
        congr 2
        symm
        change (ins.map fun i => ws.getD i false).all id = false
        rw [Bool.eq_false_iff]
        intro hA
        have := List.all_eq_true.mp hA (ws.getD i false) (List.mem_map_of_mem hi)
        rw [hd] at this
        exact Bool.false_ne_true this
    · change ws ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          ((ins.filter fun i => decide (i < ws.length)).map fun i => ws.getD i false)] =
        ws ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (ins.map fun i => ws.getD i false)]
      rw [evOr, evOr, orAny]
    · change ws ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (((ins.take 1).filter fun i => decide (i < ws.length)).map fun i => ws.getD i false)] =
        ws ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (ins.map fun i => ws.getD i false)]
      rw [evNot, evNot]
      cases ins with
      | nil => rfl
      | cons a rest =>
        by_cases ha : a < ws.length
        · simp only [List.take_succ_cons, List.take_zero, List.filter_cons, ha, decide_true, if_true,
            List.filter_nil, List.map_cons, List.map_nil, List.headD_cons]
        · have hd : ws.getD a false = false := List.getD_eq_default _ _ (by omega)
          simp only [List.take_succ_cons, List.take_zero, List.filter_cons, ha, decide_false,
            Bool.false_eq_true, if_false, List.filter_nil, List.map_cons, List.map_nil, List.headD_cons,
            List.headD_nil, hd]
  have normIn : ∀ (L : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), ops g → ∀ i ∈ (norm L g).inputs, i < L := by
    intro L g hop i hi
    obtain ⟨op, ins⟩ := g
    rcases hop with h | h | h <;> (change op = _ at h) <;> subst h
    · by_cases hall : ins.all (fun i => decide (i < L)) = true
      · have e : norm L ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ := by
          change (if ins.all (fun i => decide (i < L)) then _ else _) = _
          rw [if_pos hall]
        rw [e] at hi
        simpa using List.all_eq_true.mp hall i hi
      · have e : norm L ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          change (if ins.all (fun i => decide (i < L)) then _ else _) = _
          rw [if_neg hall]
        rw [e] at hi
        exact absurd hi List.not_mem_nil
    · change i ∈ ins.filter (fun i => decide (i < L)) at hi
      simpa using (List.mem_filter.mp hi).2
    · change i ∈ (ins.take 1).filter (fun i => decide (i < L)) at hi
      simpa using (List.mem_filter.mp hi).2
  have normFan : ∀ (L : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), ops g → g.inputs.length ≤ 2 →
      (norm L g).op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      (norm L g).inputs.length ≤ 2 := by
    intro L g hop hlen
    obtain ⟨op, ins⟩ := g
    change ins.length ≤ 2 at hlen
    rcases hop with h | h | h <;> (change op = _ at h) <;> subst h
    · by_cases hall : ins.all (fun i => decide (i < L)) = true
      · have e : norm L ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ := by
          change (if ins.all (fun i => decide (i < L)) then _ else _) = _
          rw [if_pos hall]
        rw [e]; exact ⟨Or.inl rfl, hlen⟩
      · have e : norm L ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          change (if ins.all (fun i => decide (i < L)) then _ else _) = _
          rw [if_neg hall]
        rw [e]; exact ⟨Or.inr (Or.inl rfl), Nat.zero_le _⟩
    · exact ⟨Or.inr (Or.inl rfl), le_trans (List.length_filter_le _ _) hlen⟩
    · refine ⟨Or.inr (Or.inr rfl), ?_⟩
      change ((ins.take 1).filter fun i => decide (i < L)).length ≤ 2
      have h1 := List.length_filter_le (fun i => decide (i < L)) (ins.take 1)
      have h2 : (ins.take 1).length ≤ 1 := by simp
      omega
  have normNot : ∀ (L : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), ops g →
      decide ((norm L g).op = PEqualNP.CircuitLowerBounds.GateOp.not) =
        decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) := by
    intro L g hop
    obtain ⟨op, ins⟩ := g
    rcases hop with h | h | h <;> (change op = _ at h) <;> subst h
    · by_cases hall : ins.all (fun i => decide (i < L)) = true
      · have e : norm L ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ := by
          change (if ins.all (fun i => decide (i < L)) then _ else _) = _
          rw [if_pos hall]
        rw [e]
      · have e : norm L ⟨PEqualNP.CircuitLowerBounds.GateOp.and, ins⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          change (if ins.all (fun i => decide (i < L)) then _ else _) = _
          rw [if_neg hall]
        rw [e]; rfl
    · rfl
    · rfl
  let NG : List PEqualNP.CircuitLowerBounds.Gate := x2.gates.mapIdx fun j g => norm (11 + j) g
  have shiftFun : ∀ k : ℕ, (fun (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) => norm (k + (j + 1)) g) =
      (fun j g => norm (k + 1 + j) g) := by
    intro k; funext j g; congr 1; omega
  have runNorm : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool), (∀ g ∈ gs, ops g) →
      (gs.mapIdx fun j g => norm (ws.length + j) g).foldl step ws = gs.foldl step ws := by
    intro gs
    induction gs with
    | nil => intro ws _; rfl
    | cons g gs ih =>
      intro ws hops
      rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons, Nat.add_zero,
        gateOk ws g (hops g List.mem_cons_self), shiftFun]
      have hl : (step ws g).length = ws.length + 1 := by
        simp only [step, List.length_append, List.length_singleton]
      rw [← hl]
      exact ih (step ws g) (fun h hh => hops h (List.mem_cons_of_mem _ hh))
  have ncNorm : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (k : ℕ), (∀ g ∈ gs, ops g) →
      ((gs.mapIdx fun j g => norm (k + j) g).filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length =
        (gs.filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length := by
    intro gs
    induction gs with
    | nil => intro k _; rfl
    | cons g gs ih =>
      intro k hops
      rw [List.mapIdx_cons, shiftFun, List.filter_cons, List.filter_cons, Nat.add_zero,
        normNot k g (hops g List.mem_cons_self)]
      have ih' := ih (k + 1) (fun h hh => hops h (List.mem_cons_of_mem _ hh))
      split_ifs
      · simp only [List.length_cons, ih']
      · exact ih'
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨NG ++ [fin], 11 + x2.gates.length⟩
  have lenNG : NG.length = x2.gates.length := List.length_mapIdx
  have fanC : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      rw [List.getElem_mapIdx]
      have hj' : j < x2.gates.length := by rw [← lenNG]; exact hj
      exact normFan _ _ (fanOps _ (List.getElem_mem hj')) (hfan _ (List.getElem_mem hj')).2
    · rw [List.mem_singleton] at hg
      subst hg
      exact ⟨Or.inl rfl, le_refl _⟩
  have rbC : PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 C := by
    intro j hj i hi
    change i ∈ ((NG ++ [fin]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
    change j < (NG ++ [fin]).length at hj
    rw [List.length_append, List.length_singleton, lenNG] at hj
    by_cases hjl : j < x2.gates.length
    · rw [List.getD_append _ _ _ _ (by rw [lenNG]; exact hjl),
        List.getD_eq_getElem _ _ (by rw [lenNG]; exact hjl), List.getElem_mapIdx] at hi
      exact normIn _ _ (fanOps _ (List.getElem_mem hjl)) i hi
    · have hje : j = x2.gates.length := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [lenNG]; omega), lenNG, hje, Nat.sub_self] at hi
      change i ∈ [x3, x4] at hi
      rw [hje]
      rcases List.mem_pair.mp hi with h | h <;> subst h <;> assumption
  have szC : C.size = x2.gates.length + 1 := by
    change (NG ++ [fin]).length = _
    rw [List.length_append, List.length_singleton, lenNG]
  have ncC : PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount x2 := by
    rw [ncDef C, ncX2]
    have nAnd : ¬ decide (PEqualNP.CircuitLowerBounds.GateOp.and = PEqualNP.CircuitLowerBounds.GateOp.not) = true := by decide
    change ((NG ++ [fin]).filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = _
    rw [List.filter_append,
      List.filter_cons_of_neg (p := fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) (a := fin) nAnd,
      List.filter_nil, List.append_nil]
    exact ncNorm x2.gates 11 fanOps
  obtain ⟨x, hx⟩ := hNon34 C fanC rbC (by rw [szC]; omega) (Nat.le_add_right _ _)
    (by rw [szC]; change 11 + x2.gates.length < 11 + (x2.gates.length + 1); omega)
    (by rw [ncC]; exact hge3) (by rw [ncC]; exact nc4)
  apply hx
  have hseed : List.ofFn x ++ [x 0 || x 2] = seed x := rfl
  change ((NG ++ [fin]).foldl step (List.ofFn x ++ [x 0 || x 2])).getD (11 + x2.gates.length) false = _
  rw [hseed, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hNG : NG.foldl step (seed x) = x2.gates.foldl step (seed x) := by
    have := runNorm x2.gates (seed x) fanOps
    rw [seedLen] at this
    exact this
  rw [hNG, finEval _ (by rw [lengthRun, seedLen])]
  exact exactPair x
