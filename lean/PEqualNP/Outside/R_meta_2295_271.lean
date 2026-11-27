import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2295_271
    (readers :
      let reads := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun i => i == 4 || i == 9)
      ∀ C : Circuit, IsMinimalCircuit 9 C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) →
        circuitFun 9 C (fun i => decide (i = 3)) ≠
          circuitFun 9 C (fun i => decide (i = 3 ∨ i = 4)) →
        circuitFun 9 C (fun i => decide (i = 1 ∨ i = 2)) = true →
        2 ≤ C.gates.tail.countP reads)
    (erase :
      let reads := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun i => i == 4 || i == 9)
      let pinned := fun x : Fin 8 → Bool =>
        [x 0, x 1, x 2, x 3, false, x 4, x 5, x 6, x 7, false]
      ∀ S : Circuit, FanInTwo S → 2 ≤ S.gates.countP reads →
        (∃ x y, S.eval (pinned x) ≠ S.eval (pinned y)) →
        ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ S.size ∧
          ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = S.eval (pinned x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∃ (x5 : ℕ), x5 + (3 : ℕ) ≤ x1.size ∧ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x6 : Fin (8 : ℕ) → Bool) => x6 (0 : Fin (8 : ℕ)) && x6 (1 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (2 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (3 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (5 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (4 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (5 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (7 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ))) x5 := by
  let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let embed := fun x : Fin 8 → Bool => (4 : Fin 9).insertNth (α := fun _ => Bool) false x
  let pinned := fun x : Fin 8 → Bool =>
    [x 0, x 1, x 2, x 3, false, x 4, x 5, x 6, x 7, false]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have endValue (w : List Bool) (q : Bool) : (w ++ [q]).getD w.length false = q := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  intro C minimal first output
  change circuitFun 9 C = f at output
  have sensitive : circuitFun 9 C (fun i => decide (i = 3)) ≠
      circuitFun 9 C (fun i => decide (i = 3 ∨ i = 4)) := by
    rw [output]
    decide
  have nonzero : circuitFun 9 C (fun i => decide (i = 1 ∨ i = 2)) = true := by
    rw [output]
    decide
  have count := readers C minimal first sensitive nonzero
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil => simp at count
  | cons g rest =>
    let S : Circuit := ⟨rest, o⟩
    have fan : FanInTwo S := fun k hk => minimal.1 k (List.mem_cons_of_mem g hk)
    have correct (y : Fin 9 → Bool) :
        S.eval (List.ofFn y ++ [y 0 && y 4]) = f y := by
      let w := List.ofFn y
      let q := g.op.eval (g.inputs.map fun i => w.getD i false)
      have length : w.length = 9 := List.length_ofFn ..
      have hq := first y
      change (rest.foldl step (w ++ [q])).getD 9 false = _ at hq
      rw [preserved rest (w ++ [q]) 9 (by simp [length])] at hq
      have atEnd := endValue w q
      rw [length] at atEnd
      rw [atEnd] at hq
      have value := congrFun output y
      change S.eval (w ++ [q]) = f y at value
      simpa only [hq] using value
    have restrict (x : Fin 8 → Bool) : S.eval (pinned x) = lo x := by
      have h := correct (embed x)
      have at4 : embed x 4 = false := Fin.insertNth_apply_same _ _ _
      have listed : List.ofFn (embed x) ++ [embed x 0 && embed x 4] = pinned x := by
        rw [at4, Bool.and_false]
        simp only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append]
        rfl
      rw [listed] at h
      have fun_eq : f (embed x) = lo x := by
        change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && false) ||
          (false && x 0) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
          (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) = lo x
        simp [lo]
      exact h.trans fun_eq
    have varies : ∃ x y, S.eval (pinned x) ≠ S.eval (pinned y) := by
      let zero : Fin 8 → Bool := fun _ => false
      let edge : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 2)
      refine ⟨zero, edge, ?_⟩
      rw [restrict zero, restrict edge]
      decide
    obtain ⟨D, fanD, shorter, same⟩ := erase S fan count varies
    refine ⟨D.size, ?_, D, fanD, le_rfl, fun x => (same x).trans (restrict x)⟩
    change D.size + 3 ≤ rest.length + 1
    change D.size + 2 ≤ rest.length at shorter
    omega
