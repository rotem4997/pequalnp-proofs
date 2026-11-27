import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2527_513
    (mask : ∀ ins : List ℕ, ins.length ≤ 2 →
      ∃ T : Finset (Fin 9), (T.card ≤ 2 ∨ ∃ a : Fin 9, T = {0,4,a}) ∧
        ∀ x : Fin 9 → Bool,
          GateOp.or.eval (ins.map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false) =
            decide (∃ a ∈ T, x a = true))
    (smallMask : ∀ (D : Circuit) (T : Finset (Fin 9)), FanInTwo D → T.card ≤ 2 →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      14 ≤ D.size)
    (triple : ∀ (D : Circuit) (a : Fin 9), FanInTwo D →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x a]) =
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 14 ≤ D.size) :have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (∃ x7 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x7.inputs) → (∃ x8 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x8.inputs) → (16 : ℕ) ≤ x2.size := by
  dsimp only
  intro C fan front correct second _ _
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]
        omega
  rcases C with ⟨gates,o⟩
  cases gates with
  | nil => cases second
  | cons g rest =>
    cases rest with
    | nil => cases second
    | cons h gs =>
      let D : Circuit := ⟨gs,o⟩
      let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 4]
      have firstValue (x : Fin 9 → Bool) : step (List.ofFn x) g = row x := by
        have e := front x
        change ((h::gs).foldl step (step (List.ofFn x) g)).getD 9 false = _ at e
        rw [keep _ _ _ (by simp [step])] at e
        have read : (step (List.ofFn x) g).getD 9 false =
            g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
          change (List.ofFn x ++ [_]).getD 9 false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp
        rw [read] at e
        change List.ofFn x ++ [_] = List.ofFn x ++ [_]
        rw [e]
      have hop : h.op = GateOp.or := Option.some.inj second
      have hin : h ∈ (g::h::gs) := by simp
      obtain ⟨T,classification,fromMask⟩ := mask h.inputs (fan h hin).2
      have computes (x : Fin 9 → Bool) :
          D.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
        have e := congrFun correct x
        change (gs.foldl step (step (step (List.ofFn x) g) h)).getD o false = _ at e
        rw [firstValue] at e
        change (gs.foldl step (row x ++ [h.op.eval (h.inputs.map fun i => (row x).getD i false)])).getD o false = _ at e
        rw [hop, fromMask x] at e
        change D.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [decide (∃ a ∈ T, x a = true)]) = _ at e
        simpa only [List.append_assoc, List.singleton_append] using e
      have fanD : FanInTwo D := fun a ha =>
        fan a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
      have bound : 14 ≤ D.size := by
        rcases classification with hs | ⟨a,rfl⟩
        · exact smallMask D T fanD hs computes
        · apply triple D a fanD
          intro x
          have h : decide (∃ b ∈ ({0,4,a} : Finset (Fin 9)), x b = true) =
              ((x 0 || x 4) || x a) := by
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, Bool.or_eq_true, Finset.mem_insert, Finset.mem_singleton]
            aesop
          simpa only [h] using computes x
      exact Nat.succ_le_succ (Nat.succ_le_succ bound)
