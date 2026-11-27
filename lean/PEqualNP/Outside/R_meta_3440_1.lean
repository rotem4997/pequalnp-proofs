import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3440_1
    (hAnd : ∀ (x1 : Fin (9 : ℕ)), (1 : ℕ) ≤ ↑x1 → ↑x1 ≤ (4 : ℕ) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size = (13 : ℕ) → 11 ≤ x4.output → (x4.gates[x4.output - 11]?).map PEqualNP.CircuitLowerBounds.Gate.op = some PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), !x7 x1]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (hOr : ∀ (x1 : Fin (9 : ℕ)), (1 : ℕ) ≤ ↑x1 → ↑x1 ≤ (4 : ℕ) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size = (13 : ℕ) → 11 ≤ x4.output → (x4.gates[x4.output - 11]?).map PEqualNP.CircuitLowerBounds.Gate.op = some PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), !x7 x1]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : Fin (9 : ℕ)), (1 : ℕ) ≤ ↑x1 → ↑x1 ≤ (4 : ℕ) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size = (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), !x7 x1]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro j hj1 hj4 C hm hs
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
    have hmem := (hm _ (List.getElem_mem hlt)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hAnd j hj1 hj4 C hm hs h11 (by rw [hg]; simp [h])
    · exact hOr j hj1 hj4 C hm hs h11 (by rw [hg]; simp [h])
  · have key : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, !x j]) = (List.ofFn x ++ [!x 0, !x j]).getD C.output false := by
      intro x
      obtain ⟨t, ht, hl⟩ := hpre C.gates (List.ofFn x ++ [!x 0, !x j])
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [ht]
      by_cases hlo : C.output < 11
      · rw [List.getD_append _ _ _ _ (by simp; omega)]
      · have hbig : 11 + C.gates.length ≤ C.output := by omega
        rw [List.getD_eq_default _ _ (by simp [hl]; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp only [key]
    clear key hpre hm hs
    by_cases hlo : C.output < 11
    · generalize C.output = o at hlo ⊢
      have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;> interval_cases o <;> first
        | exact ⟨fun _ => false, by decide⟩
        | exact ⟨fun i => i.val == 0, by decide⟩
        | exact ⟨fun i => i.val == 1, by decide⟩
        | exact ⟨fun i => i.val == 2, by decide⟩
        | exact ⟨fun i => i.val == 3, by decide⟩
        | exact ⟨fun i => i.val == 4, by decide⟩
        | exact ⟨fun i => i.val == 5, by decide⟩
        | exact ⟨fun i => i.val == 6, by decide⟩
        | exact ⟨fun i => i.val == 7, by decide⟩
        | exact ⟨fun i => i.val == 8, by decide⟩
    · refine ⟨fun _ => true, ?_⟩
      rw [List.getD_eq_default _ _ (by simp; omega)]
      decide
