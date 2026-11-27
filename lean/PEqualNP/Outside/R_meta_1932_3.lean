import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1932_3
    (hAnd : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) → 11 ≤ x3.output → (x3.gates[x3.output - 11]?).map PEqualNP.CircuitLowerBounds.Gate.op = some PEqualNP.CircuitLowerBounds.GateOp.and →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hOr : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) → 11 ≤ x3.output → (x3.gates[x3.output - 11]?).map PEqualNP.CircuitLowerBounds.Gate.op = some PEqualNP.CircuitLowerBounds.GateOp.or →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hNot : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) → 11 ≤ x3.output → (x3.gates[x3.output - 11]?).map PEqualNP.CircuitLowerBounds.Gate.op = some PEqualNP.CircuitLowerBounds.GateOp.not →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hp C hf hs
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      simp only [List.foldl_cons, ht, List.append_assoc, List.singleton_append]
  by_cases hout : 11 ≤ C.output ∧ C.output - 11 < C.gates.length
  · obtain ⟨h11, hlt⟩ := hout
    have hg : C.gates[C.output - 11]? = some (C.gates[C.output - 11]) := List.getElem?_eq_getElem hlt
    have hmem := (hf _ (List.getElem_mem hlt)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact hAnd pins hp C hf hs h11 (by rw [hg]; simp [h])
    · exact hOr pins hp C hf hs h11 (by rw [hg]; simp [h])
    · exact hNot pins hp C hf hs h11 (by rw [hg]; simp [h])
  · dsimp only
    by_cases hbig : 11 + C.gates.length ≤ C.output
    · refine ⟨fun _ => true, ?_⟩
      intro heq
      obtain ⟨t, ht, hl⟩ := hpre C.gates ((List.ofFn (fun _ : Fin 9 => true) ++ [true && true]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => (List.ofFn (fun _ : Fin 9 => true) ++ [true && true]).getD x8 Bool.false) pins)])
      have hev : C.eval ((List.ofFn (fun _ : Fin 9 => true) ++ [true && true]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => (List.ofFn (fun _ : Fin 9 => true) ++ [true && true]).getD x8 Bool.false) pins)]) = false := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
        rw [ht]
        apply List.getD_eq_default
        simp [hl]; omega
      rw [hev] at heq
      simp at heq
    · have hlo : C.output < 11 := by omega
      have key : ∀ x : Fin 9 → Bool, ∀ q : Bool, C.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [q]) = ((List.ofFn x ++ [x 0 && x 2]) ++ [q]).getD C.output false := by
        intro x q
        obtain ⟨t, ht, hl⟩ := hpre C.gates ((List.ofFn x ++ [x 0 && x 2]) ++ [q])
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
        rw [ht, List.getD_append _ _ _ _ (by simp; omega)]
      simp only [key]
      clear key hbig hout hpre hf hs
      generalize C.output = o at hlo ⊢
      by_cases h10 : o = 10
      · subst h10
        have e : ∀ x : Fin 9 → Bool, ∀ q : Bool, ((List.ofFn x ++ [x 0 && x 2]) ++ [q]).getD 10 false = q := by
          intro x q; simp
        simp only [e]
        have cl : ∀ x : Fin 9 → Bool, ∀ a : ℕ, 10 ≤ a → (List.ofFn x ++ [x 0 && x 2]).getD a false = false := by
          intro x a ha; apply List.getD_eq_default; simp; omega
        rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · exact ⟨fun _ => true, by decide⟩
        · by_cases ha : a < 10
          · rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
              | exact ⟨(fun i : Fin 9 => i.val == 0 || i.val == 1), by decide⟩
              | exact ⟨(fun i : Fin 9 => i.val == 3 || i.val == 4), by decide⟩
          · refine ⟨fun _ => true, ?_⟩
            simp only [List.map_cons, List.map_nil, cl _ a (by omega)]
            decide
        · by_cases ha : a < 10 <;> by_cases hb : b < 10
          · rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
              | exact ⟨(fun i : Fin 9 => i.val == 0 || i.val == 1), by decide⟩
              | exact ⟨(fun i : Fin 9 => i.val == 3 || i.val == 4), by decide⟩
              | exact ⟨(fun i : Fin 9 => i.val == 6 || i.val == 8), by decide⟩
          · rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
              | exact ⟨(fun i : Fin 9 => i.val == 0 || i.val == 1), by simp only [List.map_cons, List.map_nil, cl _ b (by omega)]; decide⟩
              | exact ⟨(fun i : Fin 9 => i.val == 3 || i.val == 4), by simp only [List.map_cons, List.map_nil, cl _ b (by omega)]; decide⟩
          · rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
              | exact ⟨(fun i : Fin 9 => i.val == 0 || i.val == 1), by simp only [List.map_cons, List.map_nil, cl _ a (by omega)]; decide⟩
              | exact ⟨(fun i : Fin 9 => i.val == 3 || i.val == 4), by simp only [List.map_cons, List.map_nil, cl _ a (by omega)]; decide⟩
          · refine ⟨fun _ => true, ?_⟩
            simp only [List.map_cons, List.map_nil, cl _ a (by omega), cl _ b (by omega)]
            decide
        · simp at hp
      · have hlt : o < 10 := by omega
        have e : ∀ x : Fin 9 → Bool, ∀ q : Bool, ((List.ofFn x ++ [x 0 && x 2]) ++ [q]).getD o false = (List.ofFn x ++ [x 0 && x 2]).getD o false := by
          intro x q; rw [List.getD_append _ _ _ _ (by simp; omega)]
        simp only [e]
        clear e h10 hlo
        rcases (show o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7 ∨ o = 8 ∨ o = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
          | exact ⟨(fun i : Fin 9 => i.val == 0 || i.val == 1), by decide⟩
          | exact ⟨(fun i : Fin 9 => i.val == 3 || i.val == 4), by decide⟩
