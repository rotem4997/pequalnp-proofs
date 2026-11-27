import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3061_1 :
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     let h : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       A.output + 1 = 8 + A.size →
       B.output ≠ 8 + A.size →
       B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size)) = 1 →
       11 ≤ A.size + B.size →
       A.size + B.size ≤ 13 →
       (∀ i : Fin 8, (PEqualNP.MetaComplexity.circuitFun 8 A ≠ fun x => x i) ∧
         (PEqualNP.MetaComplexity.circuitFun 8 A ≠ fun x => !(x i))) →
       (∀ x, f x ≠ h x → PEqualNP.MetaComplexity.circuitFun 8 A x = !k) →
       (∀ x, B.eval (A.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 A x]) = f x) →
       (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) → False) →
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     let h : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       A.output + 1 = 8 + A.size →
       B.output ≠ 8 + A.size →
       B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size)) = 2 →
       12 ≤ A.size + B.size →
       A.size + B.size ≤ 13 →
       (∀ i : Fin 8, (PEqualNP.MetaComplexity.circuitFun 8 A ≠ fun x => x i) ∧
         (PEqualNP.MetaComplexity.circuitFun 8 A ≠ fun x => !(x i))) →
       (∀ x, f x ≠ h x → PEqualNP.MetaComplexity.circuitFun 8 A x = !k) →
       (∀ x, B.eval (A.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 A x]) = f x) →
       (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) → False) →
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     let h : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       A.output + 1 = 8 + A.size →
       B.output ≠ 8 + A.size →
       B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size)) = 3 →
       A.size + B.size = 13 →
       (∀ i : Fin 8, (PEqualNP.MetaComplexity.circuitFun 8 A ≠ fun x => x i) ∧
         (PEqualNP.MetaComplexity.circuitFun 8 A ≠ fun x => !(x i))) →
       (∀ x, f x ≠ h x → PEqualNP.MetaComplexity.circuitFun 8 A x = !k) →
       (∀ x, B.eval (A.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 A x]) = f x) →
       (∀ x, B.eval (A.wires (List.ofFn x) ++ [k]) = h x) → False) →
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Bool), PEqualNP.MetaComplexity.FanInTwo x3 → PEqualNP.MetaComplexity.FanInTwo x4 → x3.output + (1 : ℕ) = (8 : ℕ) + x3.size → (10 : ℕ) + List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (if x9.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x9.inputs else x9.inputs).contains ((8 : ℕ) + x3.size)) x4.gates ≤ x3.size + x4.size → (∀ (x10 : Fin (8 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x11 : Fin (8 : ℕ) → Bool) => x11 x10) ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x11 : Fin (8 : ℕ) → Bool) => !x11 x10) → (∀ (x11 : Fin (8 : ℕ) → Bool), x1 x11 ≠ x2 x11 → PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x11 = !x5) → (∀ (x12 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x12) ++ [PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x12]) = x1 x12) → (∀ (x13 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x5]) = x2 x13) → (14 : ℕ) ≤ x3.size + x4.size := by
  intro hR1 hR2 hR3
  dsimp only at hR1 hR2 hR3 ⊢
  intro A B k hFanA hFanB hAout hCount hNotLit hDiff hEvalF hEvalH
  by_contra hlt
  have hLe13 : A.size + B.size ≤ 13 := by omega
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ extra, gs.foldl step w = w ++ extra ∧ extra.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨extra, heq, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
      rw [List.foldl_cons, heq]
      simp [step, List.append_assoc]
  have foldl_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨extra, heq, hlen⟩ := step_ext gs w
    simp [heq, hlen]
  have getD_foldl_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs w i hi
    obtain ⟨extra, heq, _⟩ := step_ext gs w
    rw [heq, List.getD_append _ _ false i hi]
  let s := 8 + A.size
  have hAwires_len : ∀ x : Fin 8 → Bool, (A.wires (List.ofFn x)).length = s := by
    intro x
    change (A.gates.foldl step (List.ofFn x)).length = 8 + A.gates.length
    rw [foldl_len, List.length_ofFn]
  let xZero : Fin 8 → Bool := fun _ => false
  let xUnit0 : Fin 8 → Bool := fun i => i == 0
  have hBout : B.output ≠ s := by
    intro heq
    have hconst : ∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [k]) = k := by
      intro x
      change (B.gates.foldl step (A.wires (List.ofFn x) ++ [k])).getD B.output false = k
      rw [heq, getD_foldl_lt B.gates (A.wires (List.ofFn x) ++ [k]) s
        (by rw [List.length_append, hAwires_len x, List.length_singleton]; omega)]
      rw [List.getD_append_right _ _ false s (by rw [hAwires_len x])]
      rw [hAwires_len x, Nat.sub_self]
      rfl
    have h0 : k = false := by
      have e := hEvalH xZero
      rw [hconst xZero] at e
      exact e
    have h1 : k = true := by
      have e := hEvalH xUnit0
      rw [hconst xUnit0] at e
      exact e
    rw [h0] at h1
    cases h1
  let r := List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
    (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s) B.gates
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    have hno : ∀ g ∈ B.gates,
        (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s = false := by
      intro g hg
      have h := List.countP_eq_zero.mp hr0 g hg
      cases hc : (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s with
      | false => rfl
      | true => exact False.elim (h hc)
    have hind : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) →
        (∀ g ∈ gs, (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s = false) →
        w1.length = w2.length →
        s < w1.length →
        (∀ i, i ≠ s → w1.getD i false = w2.getD i false) →
        ∀ i, i ≠ s → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ _ _ hag i hi; exact hag i hi
      | cons g gs ih =>
        intro w1 w2 hfan hnoread hlen hslt hag i hi
        simp only [List.foldl_cons]
        have hg_op : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfan g (by simp)
        have hgn : (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s = false :=
          hnoread g (by simp)
        have hval : g.op.eval (g.inputs.map fun j => w1.getD j false) =
            g.op.eval (g.inputs.map fun j => w2.getD j false) := by
          rcases hg_op with hand | hor | hnot
          · rw [hand] at hgn ⊢
            have hns : g.inputs.contains s = false := hgn
            have hmap : (g.inputs.map fun j => w1.getD j false) = (g.inputs.map fun j => w2.getD j false) := by
              apply List.map_congr_left
              intro j hj
              apply hag j
              intro hjs
              rw [hjs] at hj
              have hmem : g.inputs.contains s = true := List.elem_eq_true_of_mem hj
              rw [hns] at hmem
              cases hmem
            rw [hmap]
          · rw [hor] at hgn ⊢
            have hns : g.inputs.contains s = false := hgn
            have hmap : (g.inputs.map fun j => w1.getD j false) = (g.inputs.map fun j => w2.getD j false) := by
              apply List.map_congr_left
              intro j hj
              apply hag j
              intro hjs
              rw [hjs] at hj
              have hmem : g.inputs.contains s = true := List.elem_eq_true_of_mem hj
              rw [hns] at hmem
              cases hmem
            rw [hmap]
          · rw [hnot] at hgn ⊢
            have hns : (g.inputs.take 1).contains s = false := hgn
            cases hin : g.inputs with
            | nil => rfl
            | cons a as =>
              rw [hin] at hns
              have ha_ne : a ≠ s := by
                intro has
                have hmem : [a].contains s = true := by simp [has]
                change [a].contains s = false at hns
                rw [hns] at hmem
                cases hmem
              change (!(w1.getD a false)) = (!(w2.getD a false))
              rw [hag a ha_ne]
        apply ih (step w1 g) (step w2 g)
          (fun g' hg' => hfan g' (by simp [hg']))
          (fun g' hg' => hnoread g' (by simp [hg']))
          (by simp [step, hlen])
          (by simp [step]; omega)
          _ i hi
        intro j hj
        by_cases hjl : j < w1.length
        · have hjl2 : j < w2.length := by omega
          dsimp only [step]
          rw [List.getD_append _ _ false j hjl, List.getD_append _ _ false j hjl2, hag j hj]
        · by_cases hje : j = w1.length
          · subst hje
            dsimp only [step]
            rw [List.getD_append_right _ _ false _ (le_refl _),
                List.getD_append_right _ _ false _ (by omega),
                Nat.sub_self, hlen, Nat.sub_self]
            exact congrArg (fun b => [b].getD 0 false) hval
          · dsimp only [step]
            rw [List.getD_eq_default _ false (by rw [List.length_append, List.length_singleton]; omega),
                List.getD_eq_default _ false (by rw [List.length_append, List.length_singleton]; omega)]
    have heqEval : B.eval (A.wires (List.ofFn xUnit0) ++ [PEqualNP.MetaComplexity.circuitFun 8 A xUnit0]) =
        B.eval (A.wires (List.ofFn xUnit0) ++ [k]) := by
      apply hind B.gates
        (A.wires (List.ofFn xUnit0) ++ [PEqualNP.MetaComplexity.circuitFun 8 A xUnit0])
        (A.wires (List.ofFn xUnit0) ++ [k])
        (fun g hg => (hFanB g hg).1)
        hno
        (by simp)
        (by rw [List.length_append, hAwires_len xUnit0, List.length_singleton]; omega)
        _ B.output hBout
      intro i hi
      by_cases hil : i < s
      · rw [List.getD_append _ _ false i (by rw [hAwires_len xUnit0]; exact hil),
            List.getD_append _ _ false i (by rw [hAwires_len xUnit0]; exact hil)]
      · have hgt : s + 1 ≤ i := by omega
        rw [List.getD_eq_default _ false (by rw [List.length_append, hAwires_len xUnit0, List.length_singleton]; omega),
            List.getD_eq_default _ false (by rw [List.length_append, hAwires_len xUnit0, List.length_singleton]; omega)]
    rw [hEvalF xUnit0, hEvalH xUnit0] at heqEval
    cases heqEval
  have hr_le3 : r ≤ 3 := by
    change 10 + r ≤ A.size + B.size at hCount
    omega
  rcases hr : r with _ | _ | _ | _ | r'
  · exact hr_ne_zero hr
  · exact hR1 A B k hFanA hFanB hAout hBout hr (by change 10 + r ≤ A.size + B.size at hCount; omega) hLe13 hNotLit hDiff hEvalF hEvalH
  · exact hR2 A B k hFanA hFanB hAout hBout hr (by change 10 + r ≤ A.size + B.size at hCount; omega) hLe13 hNotLit hDiff hEvalF hEvalH
  · exact hR3 A B k hFanA hFanB hAout hBout hr (by change 10 + r ≤ A.size + B.size at hCount; omega) hNotLit hDiff hEvalF hEvalH
  · omega
