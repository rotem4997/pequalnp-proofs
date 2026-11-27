import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2375_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) → PEqualNP.NotBracket.notCount x2 + (15 : ℕ) ≤ x2.size →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro g0 C p q fan0 fan sz
  by_cases hn : PEqualNP.NotBracket.notCount C + (15 : ℕ) ≤ C.size
  · exact dense g0 C p q fan0 fan sz hn
  · intro pet val e1 e2 e3
    by_contra none
    let step := fun (w : List Bool) (h : PEqualNP.CircuitLowerBounds.Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
    have pre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), ∃ r : List Bool, gs.foldl step w = w ++ r ∧ r.length = gs.length := by
      intro gs
      induction gs with
      | nil => exact fun w => ⟨[], by rw [List.foldl_nil, List.append_nil], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨r, hr, hl⟩ := ih (step w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: r, ?_, ?_⟩
        · rw [List.foldl_cons, hr]
          show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ++ r = _
          rw [List.append_assoc, List.singleton_append]
        · rw [List.length_cons, List.length_cons, hl]
    have valEq : ∀ (x : Fin 10 → Bool) (i : ℕ), val x i = (C.gates.foldl step (step (List.ofFn x) g0)).getD i false := fun x i => rfl
    have wlen : ∀ x : Fin 10 → Bool, (C.gates.foldl step (step (List.ofFn x) g0)).length = 11 + C.gates.length := by
      intro x
      obtain ⟨r, hr, hl⟩ := pre C.gates (step (List.ofFn x) g0)
      rw [hr, List.length_append, hl]
      show (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).length + C.gates.length = _
      rw [List.length_append, List.length_ofFn, List.length_singleton]
    have andEq : ∀ x : Fin 10 → Bool, (val x p && val x q) = pet x := by
      intro x
      cases hx : pet x
      · cases h4 : val x p
        · rfl
        · cases h5 : val x q
          · rfl
          · exact absurd ⟨x, hx, h4, h5⟩ none
      · rw [(e3 x hx).1, (e3 x hx).2]
        rfl
    by_cases hp : p < 11 + C.gates.length
    · by_cases hq : q < 11 + C.gates.length
      · let g2 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p, q]⟩
        let F : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: (C.gates ++ [g2]), 11 + C.gates.length⟩
        have fanF : PEqualNP.MetaComplexity.FanInTwo F := by
          intro h hh
          rcases List.mem_cons.mp hh with e | hh
          · rw [e]
            exact fan0 g0 (List.mem_singleton.mpr rfl)
          · rcases List.mem_append.mp hh with hh | hh
            · exact fan h hh
            · rcases List.mem_cons.mp hh with e | hh
              · rw [e]
                exact ⟨Or.inl rfl, Nat.le_refl 2⟩
              · exact absurd hh List.not_mem_nil
        have evalF : ∀ (x3 : Fin (10 : ℕ) → Bool), F.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ))) := by
          intro x
          have hb : ((C.gates.foldl step (step (List.ofFn x) g0)) ++ [List.all [(C.gates.foldl step (step (List.ofFn x) g0)).getD p false, (C.gates.foldl step (step (List.ofFn x) g0)).getD q false] id]).getD (11 + C.gates.length) false = List.all [(C.gates.foldl step (step (List.ofFn x) g0)).getD p false, (C.gates.foldl step (step (List.ofFn x) g0)).getD q false] id := by
            rw [List.getD_append_right _ _ _ _ (by rw [wlen x])]
            rw [wlen x]
            simp
          show ((g0 :: (C.gates ++ [g2])).foldl step (List.ofFn x)).getD (11 + C.gates.length) false = _
          rw [List.foldl_cons, List.foldl_append]
          show ((C.gates.foldl step (step (List.ofFn x) g0)) ++ [List.all [(C.gates.foldl step (step (List.ofFn x) g0)).getD p false, (C.gates.foldl step (step (List.ofFn x) g0)).getD q false] id]).getD (11 + C.gates.length) false = _
          rw [hb, ← valEq x, ← valEq x]
          have k := andEq x
          simp only [List.all_cons, List.all_nil, id, Bool.and_true]
          exact k
        have bd := bound F fanF evalF
        have nc : PEqualNP.NotBracket.notCount C ≤ PEqualNP.NotBracket.notCount F := by
          change (C.gates.filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length ≤ ((g0 :: (C.gates ++ [g2])).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
          exact (((List.sublist_append_left C.gates [g2]).cons g0).filter _).length_le
        have dl : F.size = C.size + 2 := by
          change (g0 :: (C.gates ++ [g2])).length = C.gates.length + 2
          rw [List.length_cons, List.length_append]
          rfl
        omega
      · obtain ⟨y, _, hy⟩ := e2
        rw [valEq y, List.getD_eq_default _ _ (by rw [wlen y]; omega)] at hy
        exact Bool.false_ne_true hy
    · obtain ⟨y, hy, _⟩ := e1
      rw [valEq y, List.getD_eq_default _ _ (by rw [wlen y]; omega)] at hy
      exact Bool.false_ne_true hy
