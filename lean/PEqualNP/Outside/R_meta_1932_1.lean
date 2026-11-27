import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1932_1
    (small : ∀ (x1 : List (Fin 11)),   x1.length ≤ (1 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin 11) => x7.getD x8.val Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (double : ∀ (x1 : List (Fin 11)),   x1.length = (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin 11) => x7.getD x8.val Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro xs hlen C hfan hsize
  let clip (i : ℕ) : Fin 11 := ⟨min i 10, by omega⟩
  let ys : List (Fin 11) := xs.map clip
  have hylen : ys.length ≤ 2 := by simpa [ys] using hlen
  have hvalue (w : List Bool) (hw : w.length = 10) (i : ℕ) :
      w.getD (clip i).val false = w.getD i false := by
    by_cases hi : i < 10
    · have hmin : min i 10 = i := Nat.min_eq_left (by omega)
      simp [clip, hmin]
    · have hmin : min i 10 = 10 := Nat.min_eq_right (by omega)
      have ha : w.getD 10 false = false := List.getD_eq_default _ _ (by omega)
      have hb : w.getD i false = false := List.getD_eq_default _ _ (by omega)
      change w.getD (min i 10) false = w.getD i false
      rw [hmin, ha, hb]
  have eqmap (x : Fin 9 → Bool) :
      let w : List Bool := List.ofFn x ++ [x 0 && x 2]
      (ys.map (fun i => w.getD i.val false)) = xs.map (fun i => w.getD i false) := by
    intro w
    simp only [ys, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i hi
    exact hvalue w (by simp [w]) i
  by_cases hh : ys.length ≤ 1
  · obtain ⟨x, hx⟩ := small ys hh C hfan hsize
    refine ⟨x, ?_⟩
    change C.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (ys.map fun (i : Fin 11) => (List.ofFn x ++ [x 0 && x 2]).getD i.val false)]) ≠ _ at hx
    change C.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (xs.map fun (i : ℕ) => (List.ofFn x ++ [x 0 && x 2]).getD i false)]) ≠ _
    simpa only [eqmap] using hx
  · have htwo : ys.length = 2 := by omega
    obtain ⟨x, hx⟩ := double ys htwo C hfan hsize
    refine ⟨x, ?_⟩
    change C.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (ys.map fun (i : Fin 11) => (List.ofFn x ++ [x 0 && x 2]).getD i.val false)]) ≠ _ at hx
    change C.eval ((List.ofFn x ++ [x 0 && x 2]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (xs.map fun (i : ℕ) => (List.ofFn x ++ [x 0 && x 2]).getD i false)]) ≠ _
    simpa only [eqmap] using hx
