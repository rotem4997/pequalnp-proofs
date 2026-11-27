import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4139_1
  (eight : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
      (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
  (dropFrozen :
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hits := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 1 ∨ i = 10))
    let pre := fun z : Fin 8 → Bool => [false,false,z 0,z 1,z 5,z 6,z 3,z 4,z 2,z 7,false]
    ∀ C : Circuit, FanInTwo C → (∃ z, C.eval (pre z) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP hits ≤ C.size ∧
        ∀ z : Fin 8 → Bool, D.eval (List.ofFn z) = C.eval (pre z))
  (sparse :
    let F := fun x : Fin 10 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hits := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 1 ∨ i = 10))
    ∀ C : Circuit, FanInTwo C → C.size ≤ 18 → C.gates.countP hits ≤ 4 → 13 + C.gates.countP hits ≤ C.size →
      (∀ v : ℕ, v = 0 ∨ v = 1 → ∃ g ∈ C.gates, v ∈ reads g) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) ≠ F x)
  (boundary :
    let F := fun x : Fin 10 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hits := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 1 ∨ i = 10))
    ∀ C : Circuit, FanInTwo C → C.size = 18 → C.gates.countP hits = 5 →
      (∀ v : ℕ, v = 0 ∨ v = 1 → ∃ g ∈ C.gates, v ∈ reads g) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) ≠ F x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C fan size
  let F := fun x : Fin 10 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let H := fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
      (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let input := fun x : Fin 10 → Bool => List.ofFn x ++ [x 0 || x 1]
  let pre := fun z : Fin 8 → Bool => [false,false,z 0,z 1,z 5,z 6,z 3,z 4,z 2,z 7,false]
  let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let hits := fun g : Gate => (reads g).any (fun i => decide (i = 0 ∨ i = 1 ∨ i = 10))
  change ∃ x : Fin 10 → Bool, C.eval (input x) ≠ F x
  have inputLen (x : Fin 10 → Bool) : (input x).length = 11 := by simp [input]
  let complete := fun z : Fin 8 → Bool =>
    (![false,false,z 0,z 1,z 5,z 6,z 3,z 4,z 2,z 7] : Fin 10 → Bool)
  have inputComplete (z : Fin 8 → Bool) : input (complete z) = pre z := rfl
  have targetComplete : ∀ z : Fin 8 → Bool, F (complete z) = H z := by
    dsimp only [F, H, complete]
    decide +kernel
  have scenarios (v : ℕ) (hv : v = 0 ∨ v = 1) :
      ∃ x y u : Fin 10 → Bool, F x = false ∧ F y = true ∧ F u = false ∧
        (input u).getD v false = true ∧
        ∀ j : Fin 11, j.val ≠ v → (input x).getD j.val false = (input y).getD j.val false := by
    rcases hv with rfl | rfl
    · refine ⟨![false,true,false,false,false,false,false,false,false,false],
        ![true,true,false,false,false,false,false,false,false,false],
        ![true,false,false,false,false,false,false,false,false,false], ?_⟩
      dsimp only [F, input]
      decide +kernel
    · refine ⟨![true,false,false,false,false,false,false,false,false,false],
        ![true,true,false,false,false,false,false,false,false,false],
        ![false,true,false,false,false,false,false,false,false,false], ?_⟩
      dsimp only [F, input]
      decide +kernel
  classical
  by_contra bad
  have computes (x : Fin 10 → Bool) : C.eval (input x) = F x := by
    by_contra different
    exact bad ⟨x, different⟩
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  let agree := fun (v : ℕ) (a b : List Bool) =>
    a.length = b.length ∧ ∀ j, j ≠ v → a.getD j false = b.getD j false
  let legal := fun g : Gate => g.op = .and ∨ g.op = .or ∨ g.op = .not
  have allLegal (g : Gate) (hg : g ∈ C.gates) : legal g := by
    simpa only [legal, Set.mem_insert_iff, Set.mem_singleton_iff] using (fan g hg).1
  have evalReads (w : List Bool) (g : Gate) (hg : legal g) :
      g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval ((reads g).map fun k => w.getD k false) := by
    obtain ⟨op, ins⟩ := g
    change op = .and ∨ op = .or ∨ op = .not at hg
    rcases hg with rfl | rfl | rfl
    · rfl
    · rfl
    · cases ins <;> rfl
  have propagate (gs : List Gate) (v : ℕ) (good : ∀ g ∈ gs, legal g)
      (skip : ∀ g ∈ gs, v ∉ reads g)
      (a b : List Bool) (eq : agree v a b) :
      agree v (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact eq
    | cons g gs ih =>
      have eqval : g.op.eval (g.inputs.map fun k => a.getD k false) =
          g.op.eval (g.inputs.map fun k => b.getD k false) := by
        rw [evalReads a g (good g List.mem_cons_self), evalReads b g (good g List.mem_cons_self)]
        apply congrArg (GateOp.eval g.op)
        apply List.map_congr_left
        intro i hi
        exact eq.2 i (fun e => skip g List.mem_cons_self (e ▸ hi))
      have eqstep : agree v (step a g) (step b g) := by
        obtain ⟨len, same⟩ := eq
        refine ⟨by simp [step, len], fun i hi => ?_⟩
        change (a ++ [_]).getD i false = (b ++ [_]).getD i false
        rw [eqval]
        by_cases lt : i < a.length
        · rw [List.getD_append _ _ _ _ lt, List.getD_append _ _ _ _ (by omega)]
          exact same i hi
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]
      exact ih (fun h hh => good h (List.mem_cons_of_mem _ hh))
        (fun h hh => skip h (List.mem_cons_of_mem _ hh)) _ _ eqstep
  have keeps (gs : List Gate) (w : List Bool) (i : ℕ) (inside : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ inside
  have necessary (v : ℕ) (hv : v = 0 ∨ v = 1) : ∃ g ∈ C.gates, v ∈ reads g := by
    by_contra unneeded
    obtain ⟨x, y, u, fx, fy, fu, rawU, initEq⟩ := scenarios v hv
    have neOut : C.output ≠ v := by
      intro out
      have evalU : C.eval (input u) = true := by
        change (C.gates.foldl step (input u)).getD C.output false = true
        rw [out, keeps _ _ _ (by rw [inputLen]; omega)]
        exact rawU
      rw [computes u, fu] at evalU
      cases evalU
    have init : agree v (input x) (input y) := by
      refine ⟨by rw [inputLen, inputLen], fun j hj => ?_⟩
      by_cases h : j < 11
      · exact initEq ⟨j, h⟩ hj
      · rw [List.getD_eq_default _ _ (by rw [inputLen]; omega),
          List.getD_eq_default _ _ (by rw [inputLen]; omega)]
    have identical : C.eval (input x) = C.eval (input y) :=
      (propagate C.gates v allLegal (fun g hg hin => unneeded ⟨g, hg, hin⟩) _ _ init).2 C.output neOut
    rw [computes x, computes y, fx, fy] at identical
    cases identical
  have slice (z : Fin 8 → Bool) : C.eval (pre z) = H z := by
    rw [← inputComplete, computes, targetComplete]
  have zeroRow : ∃ z : Fin 8 → Bool, C.eval (pre z) = false := by
    exact ⟨fun _ => false, slice (fun _ => false)⟩
  obtain ⟨D, fanD, saved, same⟩ := dropFrozen C fan zeroRow
  change D.size + C.gates.countP hits ≤ C.size at saved
  have lowerD : 13 ≤ D.size := by
    by_contra tooSmall
    apply eight
    exact ⟨D, fanD, by omega, fun z => (same z).trans (slice z)⟩
  have lowerC : 13 + C.gates.countP hits ≤ C.size := by omega
  by_cases smallBudget : C.gates.countP hits ≤ 4
  · exact bad (sparse C fan size smallBudget lowerC necessary)
  · have narrow : C.gates.countP hits = 5 := by omega
    have full : C.size = 18 := by omega
    exact bad (boundary C fan full narrow necessary)
