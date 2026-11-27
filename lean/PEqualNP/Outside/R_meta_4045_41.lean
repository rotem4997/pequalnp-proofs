import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4045_41
    (h_one : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
      (∀ v : Fin (26 : ℕ), (x1.gates.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ (4 : ℕ)) →
      PEqualNP.TopForm.andPairs (26 : ℕ) x1 = (1 : ℕ) →
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) →
      x1.size ≤ (62 : ℕ) →
      (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) →
      (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12))
    (h_ge_two : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
      (∀ v : Fin (26 : ℕ), (x1.gates.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ (4 : ℕ)) →
      (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x1 →
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) →
      x1.size ≤ (62 : ℕ) →
      (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) →
      (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) → x1.size ≤ (62 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) → (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  let incPG : Fin 13 → Fin 13 → Bool := fun p l =>
    decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
  let adj : Fin 26 → Fin 26 → Bool := fun u v =>
    if hu : u.val < 13 then
      if hv : 13 ≤ v.val then incPG ⟨u.val, hu⟩ ⟨v.val - 13, by omega⟩ else false
    else
      if hv : v.val < 13 then incPG ⟨v.val, hv⟩ ⟨u.val - 13, by omega⟩ else false
  have hAdjSymm : ∀ u v : Fin 26, adj u v = adj v u := by decide +kernel
  have hAdjIrrefl : ∀ u : Fin 26, adj u u = false := by decide +kernel
  have hDeg4 : ∀ u : Fin 26, (Finset.univ.filter fun v : Fin 26 => adj u v = true).card = 4 := by
    decide +kernel
  have hCommonPt : ∀ p1 p2 : Fin 13, p1 ≠ p2 →
      (Finset.univ.filter fun l : Fin 13 => incPG p1 l = true ∧ incPG p2 l = true).card ≤ 1 := by
    decide +kernel
  have hCommonLn : ∀ l1 l2 : Fin 13, l1 ≠ l2 →
      (Finset.univ.filter fun p : Fin 13 => incPG p l1 = true ∧ incPG p l2 = true).card ≤ 1 := by
    decide +kernel
  have hEdgeCard : ((Finset.univ : Finset (Fin 26 × Fin 26)).filter
      fun p => p.1 < p.2 ∧ adj p.1 p.2 = true).card = 52 := by decide +kernel
  classical
  have hNoC4 : ∀ u1 u2 v1 v2 : Fin 26, u1 ≠ u2 → v1 ≠ v2 →
      adj u1 v1 = true → adj u1 v2 = true → adj u2 v1 = true → adj u2 v2 = true → False := by
    intro u1 u2 v1 v2 hune hvne h11 h12 h21 h22
    by_cases hu1 : u1.val < 13
    · have hv1 : 13 ≤ v1.val := by
        by_contra hlt
        have : adj u1 v1 = false := by dsimp only [adj]; rw [dif_pos hu1, dif_neg hlt]
        rw [this] at h11; exact Bool.false_ne_true h11
      have hv2 : 13 ≤ v2.val := by
        by_contra hlt
        have : adj u1 v2 = false := by dsimp only [adj]; rw [dif_pos hu1, dif_neg hlt]
        rw [this] at h12; exact Bool.false_ne_true h12
      have hu2 : u2.val < 13 := by
        by_contra hge
        have : adj u2 v1 = false := by dsimp only [adj]; rw [dif_neg hge, dif_neg (by omega)]
        rw [this] at h21; exact Bool.false_ne_true h21
      let p1 : Fin 13 := ⟨u1.val, hu1⟩
      let p2 : Fin 13 := ⟨u2.val, hu2⟩
      let l1 : Fin 13 := ⟨v1.val - 13, by omega⟩
      let l2 : Fin 13 := ⟨v2.val - 13, by omega⟩
      have hpne : p1 ≠ p2 := fun h => hune (Fin.ext (by have := congrArg Fin.val h; exact this))
      have hlne : l1 ≠ l2 := fun h => hvne (Fin.ext (by have := congrArg Fin.val h; dsimp [l1, l2] at this; omega))
      have hi11 : incPG p1 l1 = true := by dsimp only [adj] at h11; rw [dif_pos hu1, dif_pos hv1] at h11; exact h11
      have hi12 : incPG p1 l2 = true := by dsimp only [adj] at h12; rw [dif_pos hu1, dif_pos hv2] at h12; exact h12
      have hi21 : incPG p2 l1 = true := by dsimp only [adj] at h21; rw [dif_pos hu2, dif_pos hv1] at h21; exact h21
      have hi22 : incPG p2 l2 = true := by dsimp only [adj] at h22; rw [dif_pos hu2, dif_pos hv2] at h22; exact h22
      have hsub : ({l1, l2} : Finset (Fin 13)) ⊆
          Finset.univ.filter fun l : Fin 13 => incPG p1 l = true ∧ incPG p2 l = true := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_insert.mp hl with rfl | hl2
        · exact ⟨hi11, hi21⟩
        · rw [Finset.mem_singleton.mp hl2]; exact ⟨hi12, hi22⟩
      have hc2 : ({l1, l2} : Finset (Fin 13)).card = 2 := Finset.card_pair hlne
      have hle := Finset.card_le_card hsub
      have h1 := hCommonPt p1 p2 hpne
      omega
    · have hv1 : v1.val < 13 := by
        by_contra hge
        have : adj u1 v1 = false := by dsimp only [adj]; rw [dif_neg hu1, dif_neg hge]
        rw [this] at h11; exact Bool.false_ne_true h11
      have hv2 : v2.val < 13 := by
        by_contra hge
        have : adj u1 v2 = false := by dsimp only [adj]; rw [dif_neg hu1, dif_neg hge]
        rw [this] at h12; exact Bool.false_ne_true h12
      have hu2 : ¬ u2.val < 13 := by
        intro hlt
        have : adj u2 v1 = false := by dsimp only [adj]; rw [dif_pos hlt, dif_neg (by omega)]
        rw [this] at h21; exact Bool.false_ne_true h21
      let l1 : Fin 13 := ⟨u1.val - 13, by omega⟩
      let l2 : Fin 13 := ⟨u2.val - 13, by omega⟩
      let p1 : Fin 13 := ⟨v1.val, hv1⟩
      let p2 : Fin 13 := ⟨v2.val, hv2⟩
      have hlne : l1 ≠ l2 := fun h => hune (Fin.ext (by have := congrArg Fin.val h; dsimp [l1, l2] at this; omega))
      have hpne : p1 ≠ p2 := fun h => hvne (Fin.ext (by have := congrArg Fin.val h; exact this))
      have hi11 : incPG p1 l1 = true := by dsimp only [adj] at h11; rw [dif_neg hu1, dif_pos hv1] at h11; exact h11
      have hi12 : incPG p2 l1 = true := by dsimp only [adj] at h12; rw [dif_neg hu1, dif_pos hv2] at h12; exact h12
      have hi21 : incPG p1 l2 = true := by dsimp only [adj] at h21; rw [dif_neg hu2, dif_pos hv1] at h21; exact h21
      have hi22 : incPG p2 l2 = true := by dsimp only [adj] at h22; rw [dif_neg hu2, dif_pos hv2] at h22; exact h22
      have hsub : ({p1, p2} : Finset (Fin 13)) ⊆
          Finset.univ.filter fun p : Fin 13 => incPG p l1 = true ∧ incPG p l2 = true := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_insert.mp hp with rfl | hp2
        · exact ⟨hi11, hi21⟩
        · rw [Finset.mem_singleton.mp hp2]; exact ⟨hi12, hi22⟩
      have hc2 : ({p1, p2} : Finset (Fin 13)).card = 2 := Finset.card_pair hpne
      have hle := Finset.card_le_card hsub
      have h1 := hCommonLn l1 l2 hlne
      omega
  intro C W hLegal hSz hVal hComp
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wF : List Gate → List Bool → List Bool := fun gs w => gs.foldl stepW w
  have hEvalAnd : ∀ ls : List Bool, GateOp.and.eval ls = ls.all id := fun _ => rfl
  have hEvalOr : ∀ ls : List Bool, GateOp.or.eval ls = ls.any id := fun _ => rfl
  have hGateAt : ∀ (j : ℕ), gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ => rfl
  have hGateAtEq : ∀ (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    rw [hGateAt, List.getD_eq_getElem C.gates _ hj]
  have hLenWF : ∀ (gs : List Gate) (w : List Bool), (wF gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wF]
    | cons g gs ih =>
      intro w
      change (wF gs (stepW w g)).length = w.length + (gs.length + 1)
      rw [ih]; simp [stepW]; omega
  have hWFAppend : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      wF (gs1 ++ gs2) w = wF gs2 (wF gs1 w) := fun _ _ _ => List.foldl_append
  have hWFLt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wF gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (wF gs (stepW w g)).getD i false = w.getD i false
      rw [ih (stepW w g) i (by simp [stepW]; omega)]
      exact List.getD_append w _ false i hi
  have hGateInfo : ∀ j < C.gates.length,
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
    intro j hj
    rw [hGateAtEq j hj]
    exact hLegal j C.gates[j] (List.getElem?_eq_getElem hj)
  let in0 : ℕ → ℕ := fun j => (gateAt C j).inputs.getD 0 0
  let in1 : ℕ → ℕ := fun j => (gateAt C j).inputs.getD 1 0
  have hInsEq : ∀ j < C.gates.length, (gateAt C j).inputs = [in0 j, in1 j] := by
    intro j hj
    obtain ⟨_, a, b, hab, _, _, _⟩ := hGateInfo j hj
    simp only [in0, in1, hab, List.getD_cons_zero, List.getD_cons_succ]
  have hInNe : ∀ j < C.gates.length, in0 j ≠ in1 j := by
    intro j hj
    obtain ⟨_, a, b, hab, hne, _, _⟩ := hGateInfo j hj
    have h0 : in0 j = a := by simp only [in0, hab, List.getD_cons_zero]
    have h1 : in1 j = b := by simp only [in1, hab, List.getD_cons_succ, List.getD_cons_zero]
    rw [h0, h1]; exact hne
  have hInLt : ∀ j < C.gates.length, in0 j < 26 + j ∧ in1 j < 26 + j := by
    intro j hj
    obtain ⟨_, a, b, hab, _, ha, hb⟩ := hGateInfo j hj
    have h0 : in0 j = a := by simp only [in0, hab, List.getD_cons_zero]
    have h1 : in1 j = b := by simp only [in1, hab, List.getD_cons_succ, List.getD_cons_zero]
    rw [h0, h1]; exact ⟨ha, hb⟩
  have hRB : ReadsBack 26 C := by
    intro j hj w hw
    rw [hInsEq j hj] at hw
    obtain ⟨h0, h1⟩ := hInLt j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h0
    · exact h1
  have hWireGate : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      W x (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => W x i) := by
    intro x j hj
    rw [hVal x (26 + j)]
    have hLenX : (List.ofFn x).length = 26 := List.length_ofFn
    have hSplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hTakeLen : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
    have hPreLen : (wF (C.gates.take j) (List.ofFn x)).length = 26 + j := by
      rw [hLenWF, hLenX, hTakeLen]
    have hWires : C.wires (List.ofFn x) =
        wF (C.gates.drop (j + 1)) (stepW (wF (C.gates.take j) (List.ofFn x)) C.gates[j]) := by
      change wF C.gates (List.ofFn x) = _
      conv_lhs => rw [hSplit]
      rw [hWFAppend]; rfl
    have hStepVal : (C.wires (List.ofFn x)).getD (26 + j) false =
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => (wF (C.gates.take j) (List.ofFn x)).getD i false) := by
      rw [hWires, hWFLt _ _ (26 + j) (by dsimp only [stepW]; rw [List.length_append, hPreLen]; simp)]
      dsimp only [stepW]
      rw [List.getD_append_right _ _ _ _ (by omega), hPreLen, Nat.sub_self]
      rfl
    rw [hStepVal, hGateAtEq j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiLt : i < 26 + j := hRB j hj i (by rw [hGateAtEq j hj]; exact hi)
    rw [hVal x i, hWires]
    symm
    rw [hWFLt _ _ i (by dsimp only [stepW]; rw [List.length_append, hPreLen]; simp; omega)]
    exact List.getD_append _ _ false i (by omega)
  have hWireInp : ∀ (x : Fin 26 → Bool) (u : Fin 26), W x u.val = x u := by
    intro x u
    rw [hVal x u.val]
    change (wF C.gates (List.ofFn x)).getD u.val false = x u
    rw [hWFLt _ _ u.val (by rw [List.length_ofFn]; exact u.isLt)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact u.isLt), List.getElem_ofFn]
  by_cases hFan : ∃ v : Fin 26, 5 ≤ (C.gates.filter (fun g => decide (v.val ∈ g.inputs))).length
  · obtain ⟨v, hv⟩ := hFan
    let S : Finset ℕ := (Finset.range C.size).filter (fun j => v.val ∈ (gateAt C j).inputs)
    have hCardEq : ∀ gs : List Gate,
        ((Finset.range gs.length).filter (fun j => v.val ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs)).card =
        (gs.filter (fun g => decide (v.val ∈ g.inputs))).length := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => simp
      | append_singleton gs g ih =>
        rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert,
          List.filter_append, List.filter_cons, List.filter_nil, List.length_append]
        have hget : ∀ j < gs.length,
            (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          intro j hj
          exact List.getD_append gs [g] _ j hj
        have hlast : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          rw [List.getD_append_right gs [g] _ gs.length (le_refl _), Nat.sub_self]; rfl
        have hfilt : (Finset.range gs.length).filter (fun j => v.val ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs) =
            (Finset.range gs.length).filter (fun j => v.val ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hj, hm⟩; exact ⟨hj, by rwa [hget j hj] at hm⟩
          · rintro ⟨hj, hm⟩; exact ⟨hj, by rwa [hget j hj]⟩
        by_cases hm : v.val ∈ g.inputs
        · rw [if_pos (by rwa [hlast]), Finset.card_insert_of_notMem (by simp), hfilt, ih]
          simp [hm]
        · rw [if_neg (by rwa [hlast]), hfilt, ih]
          simp [hm]
    have hScard : 5 ≤ S.card := by
      have : S.card = (C.gates.filter (fun g => decide (v.val ∈ g.inputs))).length := hCardEq C.gates
      omega
    refine ⟨v, S, hScard, ?_⟩
    intro j hjS
    simp only [S, Finset.mem_filter, Finset.mem_range] at hjS
    obtain ⟨hj, hvin⟩ := hjS
    refine ⟨hj, ?_⟩
    obtain ⟨hops, _⟩ := hGateInfo j hj
    obtain ⟨hlt0, hlt1⟩ := hInLt j hj
    have hmem : v.val = in0 j ∨ v.val = in1 j := by
      rw [hInsEq j hj] at hvin
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hvin
    let other : ℕ := if v.val = in0 j then in1 j else in0 j
    have hotherLt : other < 26 + j := by dsimp only [other]; split_ifs <;> omega
    rcases hops with hand | hor
    · refine ⟨false, false, other, hotherLt, ?_⟩
      intro x hxv
      rw [hWireGate x j hj, hand, hInsEq j hj]
      simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, Bool.false_and, Bool.false_or]
      rcases hmem with heq | heq
      · rw [← heq, hWireInp x v, hxv, Bool.false_and]
      · rw [← heq, hWireInp x v, hxv, Bool.and_false]
    · refine ⟨true, false, other, hotherLt, ?_⟩
      intro x hxv
      rw [hWireGate x j hj, hor, hInsEq j hj]
      simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false, Bool.true_and]
      rcases hmem with heq | heq
      · have : other = in1 j := by simp [other, heq]
        rw [this, ← heq, hWireInp x v, hxv, Bool.false_or]
      · have hne : v.val ≠ in0 j := by rw [heq]; exact (hInNe j hj).symm
        have : other = in0 j := by simp [other, hne]
        rw [this, ← heq, hWireInp x v, hxv, Bool.or_false]
  push Not at hFan
  have hFanLe : ∀ v : Fin 26, (C.gates.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ 4 := by
    intro v; have := hFan v; omega
  by_cases hAP0 : andPairs 26 C = 0
  · exfalso
    have hCompSingle : ∀ u : Fin 26, W (fun w => decide (w = u)) C.output = false := by
      intro u
      cases hc : W (fun w => decide (w = u)) C.output with
      | false => rfl
      | true =>
        obtain ⟨p, l, _, hp, hl⟩ := (hComp (fun w => decide (w = u))).mp hc
        simp only [decide_eq_true_eq] at hp hl
        have : Fin.castAdd 13 p = Fin.natAdd 13 l := hp.trans hl.symm
        have hv := congrArg Fin.val this
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    have hCompPair : ∀ u v : Fin 26, W (fun w => decide (w = u ∨ w = v)) C.output = adj u v := by
      intro u v
      apply Bool.eq_iff_iff.mpr
      rw [hComp]
      constructor
      · rintro ⟨p, l, hinc, hp, hl⟩
        simp only [decide_eq_true_eq] at hp hl
        have hne : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
          intro heq
          have hv := congrArg Fin.val heq
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        rcases hp with hpu | hpv
        · rcases hl with hlu | hlv
          · exact absurd (hpu.trans hlu.symm) hne
          · have hu13 : u.val < 13 := by rw [← hpu]; exact p.isLt
            have hv13 : 13 ≤ v.val := by rw [← hlv]; simp
            dsimp only [adj]; rw [dif_pos hu13, dif_pos hv13]
            have hpeq : (⟨u.val, hu13⟩ : Fin 13) = p := Fin.ext (by have := congrArg Fin.val hpu; simpa using this.symm)
            have hleq : (⟨v.val - 13, by omega⟩ : Fin 13) = l := Fin.ext (by dsimp only; have := congrArg Fin.val hlv; simp at this; omega)
            rw [hpeq, hleq]; exact decide_eq_true hinc
        · rcases hl with hlu | hlv
          · have hv13 : v.val < 13 := by rw [← hpv]; exact p.isLt
            have hu13 : 13 ≤ u.val := by rw [← hlu]; simp
            dsimp only [adj]; rw [dif_neg (by omega), dif_pos hv13]
            have hpeq : (⟨v.val, hv13⟩ : Fin 13) = p := Fin.ext (by have := congrArg Fin.val hpv; simpa using this.symm)
            have hleq : (⟨u.val - 13, by omega⟩ : Fin 13) = l := Fin.ext (by dsimp only; have := congrArg Fin.val hlu; simp at this; omega)
            rw [hpeq, hleq]; exact decide_eq_true hinc
          · exact absurd (hpv.trans hlv.symm) hne
      · intro hadj
        by_cases hu : u.val < 13
        · have hv : 13 ≤ v.val := by
            by_contra hlt
            have : adj u v = false := by dsimp only [adj]; rw [dif_pos hu, dif_neg hlt]
            rw [this] at hadj; exact Bool.false_ne_true hadj
          dsimp only [adj] at hadj
          rw [dif_pos hu, dif_pos hv] at hadj
          refine ⟨⟨u.val, hu⟩, ⟨v.val - 13, by omega⟩, of_decide_eq_true hadj, ?_, ?_⟩
          · simp only [decide_eq_true_eq]; left; exact Fin.ext rfl
          · simp only [decide_eq_true_eq]; right; exact Fin.ext (by simp; omega)
        · have hv : v.val < 13 := by
            by_contra hlt
            have : adj u v = false := by dsimp only [adj]; rw [dif_neg hu, dif_neg hlt]
            rw [this] at hadj; exact Bool.false_ne_true hadj
          dsimp only [adj] at hadj
          rw [dif_neg hu, dif_pos hv] at hadj
          refine ⟨⟨v.val, hv⟩, ⟨u.val - 13, by omega⟩, of_decide_eq_true hadj, ?_, ?_⟩
          · simp only [decide_eq_true_eq]; right; exact Fin.ext rfl
          · simp only [decide_eq_true_eq]; left; exact Fin.ext (by simp; omega)
    have hOutLo : 26 ≤ C.output := by
      by_contra hlt
      have h1 : W (fun w => decide (w = ⟨C.output, by omega⟩)) C.output = true := by
        have := hWireInp (fun w => decide (w = ⟨C.output, by omega⟩)) ⟨C.output, by omega⟩
        simpa using this
      rw [hCompSingle] at h1
      exact Bool.false_ne_true h1
    have hOutHi : C.output < 26 + C.gates.length := by
      have hall : W (fun _ => true) C.output = true :=
        (hComp (fun _ => true)).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
      rw [hVal] at hall
      by_contra hge
      have hlen : (C.wires (List.ofFn (fun _ : Fin 26 => true))).length = 26 + C.gates.length := by
        change (wF C.gates (List.ofFn _)).length = 26 + C.gates.length
        rw [hLenWF, List.length_ofFn]
      have hnone : (C.wires (List.ofFn (fun _ : Fin 26 => true)))[C.output]? = none :=
        List.getElem?_eq_none (by omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hall
      exact Bool.false_ne_true hall
    have hConeStep : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 26 cs g =
        cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
          (fun w => (w - 26) :: cs.getD (w - 26) [])] := fun _ _ => rfl
    have hConesLen : ∀ gs : List Gate, ∀ cs : List (List ℕ),
        (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih, hConeStep]
        simp; omega
    have hConesLt : ∀ gs : List Gate, ∀ cs : List (List ℕ), ∀ i < cs.length,
        (gs.foldl (coneStep 26) cs).getD i [] = cs.getD i [] := by
      intro gs
      induction gs with
      | nil => intro cs i _; rfl
      | cons g gs ih =>
        intro cs i hi
        rw [List.foldl_cons, ih _ i (by rw [hConeStep]; simp; omega), hConeStep]
        exact List.getD_append cs _ [] i hi
    have hConeMem : ∀ (j : ℕ) (hj : j < C.gates.length) (w : ℕ),
        w ∈ (gateAt C j).inputs → 26 ≤ w →
        InCone 26 C (w - 26) j ∧ ∀ i : ℕ, InCone 26 C i (w - 26) → InCone 26 C i j := by
      intro j hj w hw hw26
      have hwLt : w < 26 + j := hRB j hj w hw
      have hSplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      let cs := (C.gates.take j).foldl (coneStep 26) []
      have hcsLen : cs.length = j := by
        rw [hConesLen, List.length_nil, Nat.zero_add, List.length_take_of_le (le_of_lt hj)]
      have hConesEq : cones 26 C = (C.gates.drop (j + 1)).foldl (coneStep 26) (coneStep 26 cs C.gates[j]) := by
        unfold cones
        conv_lhs => rw [hSplit]
        rw [List.foldl_append, List.foldl_cons]
      have hGetJ : (cones 26 C).getD j [] =
          (C.gates[j].inputs.filter (fun u => decide (26 ≤ u ∧ u < 26 + j))).flatMap
            (fun u => (u - 26) :: cs.getD (u - 26) []) := by
        rw [hConesEq, hConesLt _ _ j (by rw [hConeStep]; simp [hcsLen]), hConeStep]
        rw [List.getD_append_right _ _ _ _ (by omega), hcsLen, Nat.sub_self]
        rfl
      have hGetW : cs.getD (w - 26) [] = (cones 26 C).getD (w - 26) [] := by
        rw [hConesEq]
        symm
        rw [hConesLt _ _ (w - 26) (by rw [hConeStep]; simp [hcsLen]; omega), hConeStep]
        exact List.getD_append cs _ [] (w - 26) (by omega)
      have hwFilt : w ∈ C.gates[j].inputs.filter (fun u => decide (26 ≤ u ∧ u < 26 + j)) := by
        rw [List.mem_filter]
        exact ⟨by rw [← hGateAtEq j hj]; exact hw, by simp [hw26, hwLt]⟩
      constructor
      · unfold InCone
        rw [hGetJ, List.mem_flatMap]
        exact ⟨w, hwFilt, by simp⟩
      · intro i hi
        unfold InCone at hi ⊢
        rw [hGetJ, List.mem_flatMap]
        exact ⟨w, hwFilt, List.mem_cons_of_mem _ (by rw [hGetW]; exact hi)⟩
    let andFree : ℕ → Prop := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then True
      else if hlt : w < 26 + C.gates.length then
        (gateAt C (w - 26)).op = GateOp.or ∧
          ih (in0 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).1; change _ < w; omega) ∧
          ih (in1 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).2; change _ < w; omega)
      else False
    have hAF_lt26 : ∀ w < 26, andFree w := by
      intro w hw; dsimp only [andFree]; rw [WellFounded.fix_eq, dif_pos hw]; trivial
    have hAF_gate : ∀ j < C.gates.length, andFree (26 + j) ↔
        (gateAt C j).op = GateOp.or ∧ andFree (in0 j) ∧ andFree (in1 j) := by
      intro j hj
      dsimp only [andFree]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
    have hNoAndInCone : ∀ w < 26 + C.gates.length, ¬ andFree w →
        26 ≤ w ∧ ∃ i < C.gates.length, (gateAt C i).op = GateOp.and ∧
          (i = w - 26 ∨ InCone 26 C i (w - 26)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hnaf
        have hw26 : 26 ≤ w := by
          by_contra hlt; exact hnaf (hAF_lt26 w (by omega))
        refine ⟨hw26, ?_⟩
        let j := w - 26
        have hj : j < C.gates.length := by omega
        have hwj : w = 26 + j := by omega
        rw [hwj] at hnaf
        rcases (hGateInfo j hj).1 with hop | hop
        · exact ⟨j, hj, hop, Or.inl rfl⟩
        · have hnotboth : ¬ andFree (in0 j) ∨ ¬ andFree (in1 j) := by
            by_contra hboth
            push Not at hboth
            exact hnaf ((hAF_gate j hj).mpr ⟨hop, hboth.1, hboth.2⟩)
          obtain ⟨hlt0, hlt1⟩ := hInLt j hj
          rcases hnotboth with h0 | h1
          · obtain ⟨h26, i, hi, hiop, hic⟩ := ih (in0 j) (by omega) (by omega) h0
            obtain ⟨hm1, hm2⟩ := hConeMem j hj (in0 j) (by rw [hInsEq j hj]; simp) h26
            rcases hic with rfl | hic
            · exact ⟨in0 j - 26, hi, hiop, Or.inr hm1⟩
            · exact ⟨i, hi, hiop, Or.inr (hm2 i hic)⟩
          · obtain ⟨h26, i, hi, hiop, hic⟩ := ih (in1 j) (by omega) (by omega) h1
            obtain ⟨hm1, hm2⟩ := hConeMem j hj (in1 j) (by rw [hInsEq j hj]; simp) h26
            rcases hic with rfl | hic
            · exact ⟨in1 j - 26, hi, hiop, Or.inr hm1⟩
            · exact ⟨i, hi, hiop, Or.inr (hm2 i hic)⟩
    have hAndChildAF : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        andFree (in0 j) ∧ andFree (in1 j) := by
      intro j hj hop
      have hOne : ∀ w ∈ (gateAt C j).inputs, andFree w := by
        intro w hw
        by_contra hnaf
        have hwLt : w < 26 + j := hRB j hj w hw
        obtain ⟨hw26, i, hi, hiop, hic⟩ := hNoAndInCone w (by omega) hnaf
        obtain ⟨hm1, hm2⟩ := hConeMem j hj w hw hw26
        have hinc : InCone 26 C i j := by
          rcases hic with rfl | hic
          · exact hm1
          · exact hm2 i hic
        have hpos : 0 < andPairs 26 C := by
          unfold andPairs
          refine Finset.card_pos.mpr ⟨(i, j), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨hi, hj⟩, hiop, hop, hinc⟩
        omega
      exact ⟨hOne _ (by rw [hInsEq j hj]; simp), hOne _ (by rw [hInsEq j hj]; simp)⟩
    let orVars : ℕ → Finset (Fin 26) := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then {⟨w, h26⟩}
      else if hlt : w < 26 + C.gates.length then
        if (gateAt C (w - 26)).op = GateOp.or then
          ih (in0 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).1; change _ < w; omega) ∪
          ih (in1 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).2; change _ < w; omega)
        else ∅
      else ∅
    have hOV_lt26 : ∀ u : Fin 26, orVars u.val = {u} := by
      intro u; dsimp only [orVars]; rw [WellFounded.fix_eq, dif_pos u.isLt]
    have hOV_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        orVars (26 + j) = orVars (in0 j) ∪ orVars (in1 j) := by
      intro j hj hop
      dsimp only [orVars]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
    have hAF_eval : ∀ w < 26 + C.gates.length, andFree w →
        ∀ x : Fin 26 → Bool, W x w = decide (∃ u ∈ orVars w, x u = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf x
        by_cases h26 : w < 26
        · rw [show w = (⟨w, h26⟩ : Fin 26).val from rfl, hOV_lt26, hWireInp]
          simp
        · let j := w - 26
          have hj : j < C.gates.length := by omega
          have hwj : w = 26 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
          rw [hOV_or j hj hop, hWireGate x j hj, hop, hInsEq j hj]
          obtain ⟨hlt0, hlt1⟩ := hInLt j hj
          have ih0 := ih (in0 j) (by omega) (by omega) haf0 x
          have ih1 := ih (in1 j) (by omega) (by omega) haf1 x
          simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, ih0, ih1]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
          constructor
          · rintro (⟨u, hu, hx⟩ | ⟨u, hu, hx⟩)
            · exact ⟨u, Or.inl hu, hx⟩
            · exact ⟨u, Or.inr hu, hx⟩
          · rintro ⟨u, hu | hu, hx⟩
            · exact Or.inl ⟨u, hu, hx⟩
            · exact Or.inr ⟨u, hu, hx⟩
    have hOV_nonempty : ∀ w < 26 + C.gates.length, andFree w → (orVars w).Nonempty := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h26 : w < 26
        · rw [show w = (⟨w, h26⟩ : Fin 26).val from rfl, hOV_lt26]; exact Finset.singleton_nonempty _
        · let j := w - 26
          have hj : j < C.gates.length := by omega
          have hwj : w = 26 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, _⟩ := (hAF_gate j hj).mp haf
          obtain ⟨hlt0, _⟩ := hInLt j hj
          rw [hOV_or j hj hop]
          exact (ih (in0 j) (by omega) (by omega) haf0).mono Finset.subset_union_left
    have hAF_card_ge_2 : ∀ j < C.gates.length, andFree (26 + j) → 2 ≤ (orVars (26 + j)).card := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hj haf
        obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
        rw [hOV_or j hj hop]
        obtain ⟨hlt0, hlt1⟩ := hInLt j hj
        by_cases h0 : in0 j < 26
        · by_cases h1 : in1 j < 26
          · rw [show in0 j = (⟨in0 j, h0⟩ : Fin 26).val from rfl, hOV_lt26,
                show in1 j = (⟨in1 j, h1⟩ : Fin 26).val from rfl, hOV_lt26]
            have hne : (⟨in0 j, h0⟩ : Fin 26) ≠ ⟨in1 j, h1⟩ := fun heq => hInNe j hj (congrArg Fin.val heq)
            rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_pair hne.symm]
          · have hge := ih (in1 j - 26) (by omega) (by omega) (by rwa [show 26 + (in1 j - 26) = in1 j by omega])
            rw [show 26 + (in1 j - 26) = in1 j by omega] at hge
            exact hge.trans (Finset.card_le_card Finset.subset_union_right)
        · have hge := ih (in0 j - 26) (by omega) (by omega) (by rwa [show 26 + (in0 j - 26) = in0 j by omega])
          rw [show 26 + (in0 j - 26) = in0 j by omega] at hge
          exact hge.trans (Finset.card_le_card Finset.subset_union_left)
    let topAndsOf : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then ∅
      else if hlt : w < 26 + C.gates.length then
        if (gateAt C (w - 26)).op = GateOp.and then {w - 26}
        else
          ih (in0 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).1; change _ < w; omega) ∪
          ih (in1 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).2; change _ < w; omega)
      else ∅
    let topOrsOf : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then ∅
      else if hlt : w < 26 + C.gates.length then
        if (gateAt C (w - 26)).op = GateOp.and then ∅
        else
          insert (w - 26) (
            ih (in0 (w - 26)) (by
              have hj : w - 26 < C.gates.length := by omega
              have := (hInLt (w - 26) hj).1; change _ < w; omega) ∪
            ih (in1 (w - 26)) (by
              have hj : w - 26 < C.gates.length := by omega
              have := (hInLt (w - 26) hj).2; change _ < w; omega))
      else ∅
    let reachesInp : ℕ → Prop := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then True
      else if hlt : w < 26 + C.gates.length then
        if (gateAt C (w - 26)).op = GateOp.and then False
        else
          ih (in0 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).1; change _ < w; omega) ∨
          ih (in1 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).2; change _ < w; omega)
      else False
    have hRI_lt26 : ∀ w < 26, reachesInp w := by
      intro w hw; dsimp only [reachesInp]; rw [WellFounded.fix_eq, dif_pos hw]; trivial
    have hRI_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ reachesInp (26 + j) := by
      intro j hj hop
      dsimp only [reachesInp]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      simp [hop]
    have hRI_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        (reachesInp (26 + j) ↔ reachesInp (in0 j) ∨ reachesInp (in1 j)) := by
      intro j hj hop
      dsimp only [reachesInp]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
    have hTA_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → topAndsOf (26 + j) = {j} := by
      intro j hj hop
      dsimp only [topAndsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      simp [hop]
    have hTA_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        topAndsOf (26 + j) = topAndsOf (in0 j) ∪ topAndsOf (in1 j) := by
      intro j hj hop
      dsimp only [topAndsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
    have hTO_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → topOrsOf (26 + j) = ∅ := by
      intro j hj hop
      dsimp only [topOrsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      simp [hop]
    have hTO_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        topOrsOf (26 + j) = insert j (topOrsOf (in0 j) ∪ topOrsOf (in1 j)) := by
      intro j hj hop
      dsimp only [topOrsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
    have hRI_single : ∀ w < 26 + C.gates.length, reachesInp w →
        ∃ u : Fin 26, W (fun v => decide (v = u)) w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hri
        by_cases h26 : w < 26
        · refine ⟨⟨w, h26⟩, ?_⟩
          have := hWireInp (fun v => decide (v = ⟨w, h26⟩)) ⟨w, h26⟩
          simpa using this
        · let j := w - 26
          have hj : j < C.gates.length := by omega
          have hwj : w = 26 + j := by omega
          rw [hwj] at hri ⊢
          rcases (hGateInfo j hj).1 with hop | hop
          · exact absurd hri (hRI_and j hj hop)
          · obtain ⟨hlt0, hlt1⟩ := hInLt j hj
            rcases (hRI_or j hj hop).mp hri with h0 | h1
            · obtain ⟨u, hu⟩ := ih (in0 j) (by omega) (by omega) h0
              refine ⟨u, ?_⟩
              rw [hWireGate _ j hj, hop, hInsEq j hj]
              simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_eq_true]
              exact Or.inl hu
            · obtain ⟨u, hu⟩ := ih (in1 j) (by omega) (by omega) h1
              refine ⟨u, ?_⟩
              rw [hWireGate _ j hj, hop, hInsEq j hj]
              simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_eq_true]
              exact Or.inr hu
    have hOutNRI : ¬ reachesInp C.output := by
      intro hri
      obtain ⟨u, hu⟩ := hRI_single C.output hOutHi hri
      rw [hCompSingle u] at hu
      exact Bool.false_ne_true hu
    have hTopProps : ∀ w < 26 + C.gates.length, ¬ reachesInp w →
        (∀ j ∈ topAndsOf w, j < C.gates.length ∧ (gateAt C j).op = GateOp.and) ∧
        (∀ j ∈ topOrsOf w, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ reachesInp (26 + j)) ∧
        (∀ x : Fin 26 → Bool, W x w = true ↔ ∃ j ∈ topAndsOf w, W x (26 + j) = true) ∧
        (∀ u ∈ topAndsOf w ∪ topOrsOf w, 26 + u = w ∨
          ∃ k ∈ topOrsOf w, 26 + u ∈ (gateAt C k).inputs) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hnri
        have hw26 : 26 ≤ w := by
          by_contra hlt; exact hnri (hRI_lt26 w (by omega))
        let j := w - 26
        have hj : j < C.gates.length := by omega
        have hwj : w = 26 + j := by omega
        rw [hwj] at hnri ⊢
        rcases (hGateInfo j hj).1 with hop | hop
        · rw [hTA_and j hj hop, hTO_and j hj hop]
          refine ⟨fun k hk => by rw [Finset.mem_singleton.mp hk]; exact ⟨hj, hop⟩,
            fun k hk => by simp at hk,
            fun x => by simp,
            fun u hu => by simp at hu; subst hu; exact Or.inl rfl⟩
        · have hn0 : ¬ reachesInp (in0 j) := fun h => hnri ((hRI_or j hj hop).mpr (Or.inl h))
          have hn1 : ¬ reachesInp (in1 j) := fun h => hnri ((hRI_or j hj hop).mpr (Or.inr h))
          obtain ⟨hlt0, hlt1⟩ := hInLt j hj
          obtain ⟨hA0, hO0, hE0, hP0⟩ := ih (in0 j) (by omega) (by omega) hn0
          obtain ⟨hA1, hO1, hE1, hP1⟩ := ih (in1 j) (by omega) (by omega) hn1
          rw [hTA_or j hj hop, hTO_or j hj hop]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro k hk
            rcases Finset.mem_union.mp hk with h | h
            · exact hA0 k h
            · exact hA1 k h
          · intro k hk
            rcases Finset.mem_insert.mp hk with rfl | h
            · exact ⟨hj, hop, hnri⟩
            · rcases Finset.mem_union.mp h with h | h
              · exact hO0 k h
              · exact hO1 k h
          · intro x
            rw [hWireGate x j hj, hop, hInsEq j hj]
            simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true, hE0 x, hE1 x, Finset.mem_union]
            constructor
            · rintro (⟨k, hk, ht⟩ | ⟨k, hk, ht⟩)
              · exact ⟨k, Or.inl hk, ht⟩
              · exact ⟨k, Or.inr hk, ht⟩
            · rintro ⟨k, hk | hk, ht⟩
              · exact Or.inl ⟨k, hk, ht⟩
              · exact Or.inr ⟨k, hk, ht⟩
          · intro u hu
            by_cases huj : u = j
            · exact Or.inl (by omega)
            · right
              have hu01 : u ∈ topAndsOf (in0 j) ∪ topOrsOf (in0 j) ∨
                  u ∈ topAndsOf (in1 j) ∪ topOrsOf (in1 j) := by
                simp only [Finset.mem_union, Finset.mem_insert] at hu ⊢
                rcases hu with (h | h) | (rfl | h | h)
                · exact Or.inl (Or.inl h)
                · exact Or.inr (Or.inl h)
                · exact absurd rfl huj
                · exact Or.inl (Or.inr h)
                · exact Or.inr (Or.inr h)
              rcases hu01 with h0 | h1
              · rcases hP0 u h0 with heq | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj, heq]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
              · rcases hP1 u h1 with heq | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj, heq]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
    let A := topAndsOf C.output
    let T := topOrsOf C.output
    obtain ⟨hA_prop, hT_prop, hOutEval, hTopParent⟩ := hTopProps C.output hOutHi hOutNRI
    have hAT_disj : Disjoint A T := by
      rw [Finset.disjoint_left]
      intro j hjA hjT
      have h1 := (hA_prop j hjA).2
      have h2 := (hT_prop j hjT).2.1
      rw [h1] at h2
      exact GateOp.noConfusion h2
    have hA_le_T : A.card ≤ T.card + 1 := by
      by_cases hTe : T = ∅
      · have hA1 : A.card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro u hu v hv
          have hu' : 26 + u = C.output := by
            rcases hTopParent u (Finset.mem_union_left _ hu) with heq | ⟨k, hk, _⟩
            · exact heq
            · change k ∈ T at hk; rw [hTe] at hk; simp at hk
          have hv' : 26 + v = C.output := by
            rcases hTopParent v (Finset.mem_union_left _ hv) with heq | ⟨k, hk, _⟩
            · exact heq
            · change k ∈ T at hk; rw [hTe] at hk; simp at hk
          omega
        omega
      · let outG := C.output - 26
        have houtEq : C.output = 26 + outG := by omega
        have houtLt : outG < C.gates.length := by omega
        have houtMem : outG ∈ A ∪ T := by
          rcases (hGateInfo outG houtLt).1 with hop | hop
          · apply Finset.mem_union_left
            change outG ∈ topAndsOf C.output
            rw [houtEq, hTA_and outG houtLt hop]; simp
          · apply Finset.mem_union_right
            change outG ∈ topOrsOf C.output
            rw [houtEq, hTO_or outG houtLt hop]; simp
        let rem := (A ∪ T).erase outG
        have hRemSub : rem.image (· + 26) ⊆ T.biUnion (fun k => (gateAt C k).inputs.toFinset) := by
          intro w hw
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
          have hne : u ≠ outG := (Finset.mem_erase.mp hu).1
          have hum : u ∈ A ∪ T := (Finset.mem_erase.mp hu).2
          rcases hTopParent u hum with heq | ⟨k, hk, hkin⟩
          · exact absurd (by omega) hne
          · exact Finset.mem_biUnion.mpr ⟨k, hk, List.mem_toFinset.mpr (by rwa [Nat.add_comm])⟩
        have hCard1 : rem.card ≤ (T.biUnion (fun k => (gateAt C k).inputs.toFinset)).card := by
          calc rem.card = (rem.image (· + 26)).card :=
                (Finset.card_image_of_injective rem (fun a b h => by omega)).symm
            _ ≤ _ := Finset.card_le_card hRemSub
        have hCard2 : (T.biUnion (fun k => (gateAt C k).inputs.toFinset)).card ≤ 2 * T.card := by
          calc _ ≤ ∑ k ∈ T, ((gateAt C k).inputs.toFinset).card := Finset.card_biUnion_le
            _ ≤ ∑ k ∈ T, 2 := by
                apply Finset.sum_le_sum
                intro k hk
                have hlt := (hT_prop k hk).1
                have h2 : (gateAt C k).inputs.length = 2 := by rw [hInsEq k hlt]; rfl
                exact (List.toFinset_card_le _).trans (le_of_eq h2)
            _ = 2 * T.card := by simp [Nat.mul_comm]
        have hRemCard : rem.card + 1 = A.card + T.card := by
          rw [Finset.card_erase_add_one houtMem, Finset.card_union_of_disjoint hAT_disj]
        omega
    have hAndStar : ∀ j ∈ A,
        (∀ u ∈ orVars (in0 j), ∀ v ∈ orVars (in1 j), adj u v = true) ∧
        ((orVars (in0 j)).card = 1 ∨ (orVars (in1 j)).card = 1) := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      obtain ⟨hlt0, hlt1⟩ := hInLt j hj
      have hadj : ∀ u ∈ orVars (in0 j), ∀ v ∈ orVars (in1 j), adj u v = true := by
        intro u hu v hv
        let x : Fin 26 → Bool := fun w => decide (w = u ∨ w = v)
        have hjT : W x (26 + j) = true := by
          rw [hWireGate x j hj, hop, hInsEq j hj]
          simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true,
            hAF_eval (in0 j) (by omega) haf0 x, hAF_eval (in1 j) (by omega) haf1 x, decide_eq_true_eq]
          exact ⟨⟨u, hu, by simp [x]⟩, ⟨v, hv, by simp [x]⟩⟩
        have houtT : W x C.output = true := (hOutEval x).mpr ⟨j, hjA, hjT⟩
        rw [hCompPair u v] at houtT
        exact houtT
      refine ⟨hadj, ?_⟩
      by_contra hboth
      push Not at hboth
      have hne0 := hOV_nonempty (in0 j) (by omega) haf0
      have hne1 := hOV_nonempty (in1 j) (by omega) haf1
      have hc0 : 2 ≤ (orVars (in0 j)).card := by have := hne0.card_pos; omega
      have hc1 : 2 ≤ (orVars (in1 j)).card := by have := hne1.card_pos; omega
      obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (in0 j)).card)
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (in1 j)).card)
      exact hNoC4 u1 u2 v1 v2 hune hvne (hadj u1 hu1 v1 hv1) (hadj u1 hu1 v2 hv2)
        (hadj u2 hu2 v1 hv1) (hadj u2 hu2 v2 hv2)
    let center : ℕ → Fin 26 := fun j =>
      if h : (orVars (in0 j)).Nonempty ∧ (orVars (in0 j)).card = 1 then h.1.choose
      else if h2 : (orVars (in1 j)).Nonempty then h2.choose
      else 0
    let leafWire : ℕ → ℕ := fun j =>
      if (orVars (in0 j)).card = 1 then in1 j else in0 j
    have hStarProp : ∀ j ∈ A,
        andFree (leafWire j) ∧ leafWire j < 26 + C.gates.length ∧
        (∀ v ∈ orVars (leafWire j), adj (center j) v = true) ∧
        (∀ u v : Fin 26,
          W (fun w => decide (w = u ∨ w = v)) (26 + j) = true →
          (u = center j ∧ v ∈ orVars (leafWire j)) ∨ (v = center j ∧ u ∈ orVars (leafWire j))) := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      obtain ⟨hlt0, hlt1⟩ := hInLt j hj
      have hne0 := hOV_nonempty (in0 j) (by omega) haf0
      have hne1 := hOV_nonempty (in1 j) (by omega) haf1
      obtain ⟨hadj, hcard⟩ := hAndStar j hjA
      by_cases hc0 : (orVars (in0 j)).card = 1
      · have hcen : center j = hne0.choose := by simp [center, hne0, hc0]
        have hcenMem : center j ∈ orVars (in0 j) := by rw [hcen]; exact hne0.choose_spec
        have hsing : orVars (in0 j) = {center j} := by
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc0
          have : center j = a := Finset.mem_singleton.mp (ha ▸ hcenMem)
          rw [ha, this]
        have hlw : leafWire j = in1 j := by simp [leafWire, hc0]
        refine ⟨by rw [hlw]; exact haf1, by rw [hlw]; omega,
          fun v hv => hadj (center j) hcenMem v (by rw [← hlw]; exact hv), ?_⟩
        intro u v hjT
        rw [hWireGate _ j hj, hop, hInsEq j hj] at hjT
        simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true,
          hAF_eval (in0 j) (by omega) haf0 _, hAF_eval (in1 j) (by omega) haf1 _,
          decide_eq_true_eq, hsing, Finset.mem_singleton] at hjT
        obtain ⟨⟨a, rfl, ha⟩, ⟨b, hb, hbuv⟩⟩ := hjT
        rw [hlw]
        rcases ha with hcu | hcv
        · rcases hbuv with rfl | rfl
          · exfalso; have := hadj (center j) hcenMem (center j) (hcu ▸ hb); rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
          · exact Or.inl ⟨hcu.symm, hb⟩
        · rcases hbuv with rfl | rfl
          · exact Or.inr ⟨hcv.symm, hb⟩
          · exfalso; have := hadj (center j) hcenMem (center j) (hcv ▸ hb); rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
      · have hc1 : (orVars (in1 j)).card = 1 := hcard.resolve_left hc0
        have hcen : center j = hne1.choose := by simp [center, hc0, hne1]
        have hcenMem : center j ∈ orVars (in1 j) := by rw [hcen]; exact hne1.choose_spec
        have hsing : orVars (in1 j) = {center j} := by
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
          have : center j = a := Finset.mem_singleton.mp (ha ▸ hcenMem)
          rw [ha, this]
        have hlw : leafWire j = in0 j := by simp [leafWire, hc0]
        refine ⟨by rw [hlw]; exact haf0, by rw [hlw]; omega,
          fun v hv => by rw [hAdjSymm]; exact hadj v (by rw [← hlw]; exact hv) (center j) hcenMem, ?_⟩
        intro u v hjT
        rw [hWireGate _ j hj, hop, hInsEq j hj] at hjT
        simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true,
          hAF_eval (in0 j) (by omega) haf0 _, hAF_eval (in1 j) (by omega) haf1 _,
          decide_eq_true_eq, hsing, Finset.mem_singleton] at hjT
        obtain ⟨⟨b, hb, hbuv⟩, ⟨a, rfl, ha⟩⟩ := hjT
        rw [hlw]
        rcases ha with hcu | hcv
        · rcases hbuv with rfl | rfl
          · exfalso; have := hadj (center j) (hcu ▸ hb) (center j) hcenMem; rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
          · exact Or.inl ⟨hcu.symm, hb⟩
        · rcases hbuv with rfl | rfl
          · exact Or.inr ⟨hcv.symm, hb⟩
          · exfalso; have := hadj (center j) (hcv ▸ hb) (center j) hcenMem; rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
    have hEdgeCov : ∀ u v : Fin 26, adj u v = true →
        ∃ j ∈ A, (u = center j ∧ v ∈ orVars (leafWire j)) ∨
          (v = center j ∧ u ∈ orVars (leafWire j)) := by
      intro u v huv
      have houtT : W (fun w => decide (w = u ∨ w = v)) C.output = true := by
        rw [hCompPair u v]; exact huv
      obtain ⟨j, hjA, hjT⟩ := (hOutEval _).mp houtT
      exact ⟨j, hjA, (hStarProp j hjA).2.2.2 u v hjT⟩
    let edges : Finset (Fin 26 × Fin 26) :=
      Finset.univ.filter fun p => p.1 < p.2 ∧ adj p.1 p.2 = true
    have hA_ge_13 : 13 ≤ A.card := by
      let inc : Fin 26 → Finset (Fin 26 × Fin 26) := fun c =>
        edges.filter fun p => p.1 = c ∨ p.2 = c
      have hIncLe : ∀ c : Fin 26, (inc c).card ≤ 4 := by
        intro c
        let otherV : Fin 26 × Fin 26 → Fin 26 := fun p => if p.1 = c then p.2 else p.1
        have hSub : (inc c).image otherV ⊆ Finset.univ.filter fun v : Fin 26 => adj c v = true := by
          intro v hv
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
          simp only [inc, edges, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨_, hadj⟩, h1 | h2⟩ := hp
          · simp only [otherV, h1, ite_true]; rwa [← h1]
          · have hne : p.1 ≠ c := by intro h; rw [h, h2, hAdjIrrefl] at hadj; exact Bool.false_ne_true hadj
            simp only [otherV, hne, ite_false]; rw [hAdjSymm, ← h2]; exact hadj
        have hInj : Set.InjOn otherV (inc c : Set (Fin 26 × Fin 26)) := by
          intro p hp q hq heq
          simp only [Finset.mem_coe, inc, edges, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          rcases hp with ⟨⟨hpLt, _⟩, hp1 | hp2⟩
          · rcases hq with ⟨⟨hqLt, _⟩, hq1 | hq2⟩
            · have hpe : otherV p = p.2 := by simp [otherV, hp1]
              have hqe : otherV q = q.2 := by simp [otherV, hq1]
              rw [hpe, hqe] at heq; exact Prod.ext (hp1.trans hq1.symm) heq
            · have hpe : otherV p = p.2 := by simp [otherV, hp1]
              have hne : q.1 ≠ c := ne_of_lt (hq2 ▸ hqLt)
              have hqe : otherV q = q.1 := by simp [otherV, hne]
              rw [hpe, hqe] at heq
              exact absurd (lt_trans (hp1 ▸ hpLt) (heq ▸ hq2 ▸ hqLt)) (lt_irrefl _)
          · rcases hq with ⟨⟨hqLt, _⟩, hq1 | hq2⟩
            · have hne : p.1 ≠ c := ne_of_lt (hp2 ▸ hpLt)
              have hpe : otherV p = p.1 := by simp [otherV, hne]
              have hqe : otherV q = q.2 := by simp [otherV, hq1]
              rw [hpe, hqe] at heq
              exact absurd (lt_trans (hq1 ▸ hqLt) (heq.symm ▸ hp2 ▸ hpLt)) (lt_irrefl _)
            · have hnep : p.1 ≠ c := ne_of_lt (hp2 ▸ hpLt)
              have hneq : q.1 ≠ c := ne_of_lt (hq2 ▸ hqLt)
              have hpe : otherV p = p.1 := by simp [otherV, hnep]
              have hqe : otherV q = q.1 := by simp [otherV, hneq]
              rw [hpe, hqe] at heq; exact Prod.ext heq (hp2.trans hq2.symm)
        calc (inc c).card = ((inc c).image otherV).card := (Finset.card_image_of_injOn hInj).symm
          _ ≤ (Finset.univ.filter fun v : Fin 26 => adj c v = true).card := Finset.card_le_card hSub
          _ = 4 := hDeg4 c
      have hSub : edges ⊆ (A.image center).biUnion inc := by
        intro p hp
        have hadj : adj p.1 p.2 = true := (Finset.mem_filter.mp hp).2.2
        obtain ⟨j, hjA, ⟨h1, _⟩ | ⟨h2, _⟩⟩ := hEdgeCov p.1 p.2 hadj
        · exact Finset.mem_biUnion.mpr ⟨center j, Finset.mem_image_of_mem _ hjA,
            Finset.mem_filter.mpr ⟨hp, Or.inl h1⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨center j, Finset.mem_image_of_mem _ hjA,
            Finset.mem_filter.mpr ⟨hp, Or.inr h2⟩⟩
      have h52 : 52 ≤ 4 * A.card := by
        calc 52 = edges.card := hEdgeCard.symm
          _ ≤ ((A.image center).biUnion inc).card := Finset.card_le_card hSub
          _ ≤ ∑ c ∈ A.image center, (inc c).card := Finset.card_biUnion_le
          _ ≤ ∑ c ∈ A.image center, 4 := Finset.sum_le_sum fun c _ => hIncLe c
          _ = 4 * (A.image center).card := by simp [Nat.mul_comm]
          _ ≤ 4 * A.card := Nat.mul_le_mul_left 4 Finset.card_image_le
      omega
    let orCone : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then ∅
      else if hlt : w < 26 + C.gates.length then
        if (gateAt C (w - 26)).op = GateOp.or then
          insert (w - 26) (
            ih (in0 (w - 26)) (by
              have hj : w - 26 < C.gates.length := by omega
              have := (hInLt (w - 26) hj).1; change _ < w; omega) ∪
            ih (in1 (w - 26)) (by
              have hj : w - 26 < C.gates.length := by omega
              have := (hInLt (w - 26) hj).2; change _ < w; omega))
        else ∅
      else ∅
    let baseIn : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then {w}
      else if hlt : w < 26 + C.gates.length then
        if (gateAt C (w - 26)).op = GateOp.or then
          ih (in0 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).1; change _ < w; omega) ∪
          ih (in1 (w - 26)) (by
            have hj : w - 26 < C.gates.length := by omega
            have := (hInLt (w - 26) hj).2; change _ < w; omega)
        else ∅
      else ∅
    have hOC_lt26 : ∀ w < 26, orCone w = ∅ := by
      intro w hw; dsimp only [orCone]; rw [WellFounded.fix_eq, dif_pos hw]
    have hOC_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        orCone (26 + j) = insert j (orCone (in0 j) ∪ orCone (in1 j)) := by
      intro j hj hop
      dsimp only [orCone]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
    have hBI_lt26 : ∀ w < 26, baseIn w = {w} := by
      intro w hw; dsimp only [baseIn]; rw [WellFounded.fix_eq, dif_pos hw]
    have hBI_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        baseIn (26 + j) = baseIn (in0 j) ∪ baseIn (in1 j) := by
      intro j hj hop
      dsimp only [baseIn]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
    have hBotProps : ∀ w < 26 + C.gates.length, andFree w →
        (∀ k ∈ orCone w, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
          andFree (26 + k) ∧ orVars (26 + k) ⊆ orVars w) ∧
        (∀ i ∈ baseIn w, i < 26) ∧
        (orVars w = (baseIn w).biUnion fun i => orVars i) ∧
        (w ∈ baseIn w ∪ (orCone w).image (· + 26)) ∧
        (∀ u ∈ baseIn w ∪ (orCone w).image (· + 26), u = w ∨
          ∃ k ∈ orCone w, u ∈ (gateAt C k).inputs) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h26 : w < 26
        · rw [hOC_lt26 w h26, hBI_lt26 w h26]
          refine ⟨fun k hk => by simp at hk, fun i hi => by simp at hi; omega,
            by simp, by simp, fun u hu => by simp at hu; exact Or.inl hu⟩
        · let j := w - 26
          have hj : j < C.gates.length := by omega
          have hwj : w = 26 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
          obtain ⟨hlt0, hlt1⟩ := hInLt j hj
          obtain ⟨hC0, hB0, hV0, hM0, hP0⟩ := ih (in0 j) (by omega) (by omega) haf0
          obtain ⟨hC1, hB1, hV1, hM1, hP1⟩ := ih (in1 j) (by omega) (by omega) haf1
          rw [hOC_or j hj hop, hBI_or j hj hop]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro k hk
            rcases Finset.mem_insert.mp hk with rfl | h
            · exact ⟨hj, hop, haf, Finset.Subset.rfl⟩
            · rcases Finset.mem_union.mp h with h | h
              · obtain ⟨a, b, c, d⟩ := hC0 k h
                exact ⟨a, b, c, d.trans (by rw [hOV_or j hj hop]; exact Finset.subset_union_left)⟩
              · obtain ⟨a, b, c, d⟩ := hC1 k h
                exact ⟨a, b, c, d.trans (by rw [hOV_or j hj hop]; exact Finset.subset_union_right)⟩
          · intro i hi
            rcases Finset.mem_union.mp hi with h | h
            · exact hB0 i h
            · exact hB1 i h
          · rw [hOV_or j hj hop, hV0, hV1, Finset.union_biUnion]
          · apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨j, Finset.mem_insert_self _ _, Nat.add_comm j 26⟩
          · intro u hu
            by_cases huj : u = 26 + j
            · exact Or.inl huj
            · right
              have hu01 : u ∈ baseIn (in0 j) ∪ (orCone (in0 j)).image (· + 26) ∨
                  u ∈ baseIn (in1 j) ∪ (orCone (in1 j)).image (· + 26) := by
                simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert] at hu ⊢
                rcases hu with (h | h) | ⟨k, rfl | h | h, rfl⟩
                · exact Or.inl (Or.inl h)
                · exact Or.inr (Or.inl h)
                · exact absurd (Nat.add_comm j 26) huj
                · exact Or.inl (Or.inr ⟨k, h, rfl⟩)
                · exact Or.inr (Or.inr ⟨k, h, rfl⟩)
              rcases hu01 with h0 | h1
              · rcases hP0 u h0 with rfl | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
              · rcases hP1 u h1 with rfl | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
    let Ac : Fin 26 → Finset ℕ := fun c => A.filter (fun j => center j = c)
    let Bc : Fin 26 → Finset ℕ := fun c => (Ac c).biUnion (fun j => orCone (leafWire j))
    let Ic : Fin 26 → Finset ℕ := fun c => (Ac c).biUnion (fun j => baseIn (leafWire j))
    let Ec : Fin 26 → Finset (Fin 26) := fun c => (Ac c).biUnion (fun j => orVars (leafWire j))
    have hAF_reaches : ∀ w < 26 + C.gates.length, andFree w → reachesInp w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h26 : w < 26
        · exact hRI_lt26 w h26
        · let j := w - 26
          have hj : j < C.gates.length := by omega
          have hwj : w = 26 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, _⟩ := (hAF_gate j hj).mp haf
          obtain ⟨hlt0, _⟩ := hInLt j hj
          exact (hRI_or j hj hop).mpr (Or.inl (ih (in0 j) (by omega) (by omega) haf0))
    have hBc_props : ∀ c : Fin 26, ∀ k ∈ Bc c,
        k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ andFree (26 + k) ∧
        (∀ v ∈ orVars (26 + k), adj c v = true) := by
      intro c k hk
      obtain ⟨j, hjAc, hkj⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨hjA, hcen⟩ := Finset.mem_filter.mp hjAc
      obtain ⟨haf, hlt, hadj, _⟩ := hStarProp j hjA
      obtain ⟨hkLt, hkop, hkAF, hkSub⟩ := (hBotProps (leafWire j) hlt haf).1 k hkj
      exact ⟨hkLt, hkop, hkAF, fun v hv => hcen ▸ hadj v (hkSub hv)⟩
    have hBc_disj : ∀ c1 c2 : Fin 26, c1 ≠ c2 → Disjoint (Bc c1) (Bc c2) := by
      intro c1 c2 hne
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨hkLt, _, hkAF, hadj1⟩ := hBc_props c1 k hk1
      obtain ⟨_, _, _, hadj2⟩ := hBc_props c2 k hk2
      have hge2 := hAF_card_ge_2 k hkLt hkAF
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (26 + k)).card)
      exact hNoC4 c1 c2 v1 v2 hne hvne (hadj1 v1 hv1) (hadj1 v2 hv2) (hadj2 v1 hv1) (hadj2 v2 hv2)
    let Ball := Finset.univ.biUnion Bc
    have hBall_sub : Ball ⊆ Finset.range C.gates.length := by
      intro k hk
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hk
      exact Finset.mem_range.mpr (hBc_props c k hkc).1
    have hBall_disj_A : Disjoint Ball A := by
      rw [Finset.disjoint_left]
      intro k hkB hkA
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hkB
      have h1 := (hBc_props c k hkc).2.1
      have h2 := (hA_prop k hkA).2
      rw [h1] at h2; exact GateOp.noConfusion h2
    have hBall_disj_T : Disjoint Ball T := by
      rw [Finset.disjoint_left]
      intro k hkB hkT
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hkB
      obtain ⟨hkLt, _, hkAF, _⟩ := hBc_props c k hkc
      exact (hT_prop k hkT).2.2 (hAF_reaches (26 + k) (by omega) hkAF)
    have hIc_bound : ∀ c : Fin 26, (Ic c).card ≤ (Bc c).card + (Ac c).card := by
      intro c
      let R : Finset ℕ := (Ac c).image leafWire
      have hRcard : R.card ≤ (Ac c).card := Finset.card_image_le
      let Wc : Finset ℕ := Ic c ∪ (Bc c).image (· + 26)
      have hIcDisj : Disjoint (Ic c) ((Bc c).image (· + 26)) := by
        rw [Finset.disjoint_left]
        intro u hu1 hu2
        obtain ⟨j, hjAc, huj⟩ := Finset.mem_biUnion.mp hu1
        obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
        obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
        have huLt := (hBotProps (leafWire j) hlt haf).2.1 u huj
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu2
        omega
      have hWcCard : Wc.card = (Ic c).card + (Bc c).card := by
        rw [Finset.card_union_of_disjoint hIcDisj,
          Finset.card_image_of_injective _ (fun a b h => by omega)]
      have hSub : Wc \ R ⊆ (Bc c).biUnion (fun k => (gateAt C k).inputs.toFinset) := by
        intro u hu
        have hnotR : u ∉ R := (Finset.mem_sdiff.mp hu).2
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hu).1 with huI | huG
        · obtain ⟨j, hjAc, huij⟩ := Finset.mem_biUnion.mp huI
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          rcases (hBotProps (leafWire j) hlt haf).2.2.2.2 u (Finset.mem_union_left _ huij) with rfl | ⟨k, hk, hkin⟩
          · exact absurd (Finset.mem_image_of_mem leafWire hjAc) hnotR
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_biUnion.mpr ⟨j, hjAc, hk⟩, List.mem_toFinset.mpr hkin⟩
        · obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp huG
          obtain ⟨j, hjAc, hkj⟩ := Finset.mem_biUnion.mp hk0
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          rcases (hBotProps (leafWire j) hlt haf).2.2.2.2 (k0 + 26)
              (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkj)) with heq | ⟨k, hk, hkin⟩
          · exact absurd (heq ▸ Finset.mem_image_of_mem leafWire hjAc) hnotR
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_biUnion.mpr ⟨j, hjAc, hk⟩, List.mem_toFinset.mpr hkin⟩
      have hDiffLe : (Wc \ R).card ≤ 2 * (Bc c).card := by
        calc (Wc \ R).card ≤ ((Bc c).biUnion (fun k => (gateAt C k).inputs.toFinset)).card := Finset.card_le_card hSub
          _ ≤ ∑ k ∈ Bc c, ((gateAt C k).inputs.toFinset).card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ Bc c, 2 := by
              apply Finset.sum_le_sum
              intro k hk
              have hkLt := (hBc_props c k hk).1
              have h2 : (gateAt C k).inputs.length = 2 := by rw [hInsEq k hkLt]; rfl
              exact (List.toFinset_card_le _).trans (le_of_eq h2)
          _ = 2 * (Bc c).card := by simp [Nat.mul_comm]
      have hWcLe : Wc.card ≤ (Wc \ R).card + R.card := by
        have h1 : Wc ⊆ (Wc \ R) ∪ R := fun x hx => by
          by_cases hxR : x ∈ R
          · exact Finset.mem_union_right _ hxR
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxR⟩)
        exact (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      omega
    have hEc_le_Ic : ∀ c : Fin 26, (Ec c).card ≤ (Ic c).card := by
      intro c
      have hEq : Ec c = (Ic c).biUnion orVars := by
        ext v
        simp only [Ec, Ic, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hjAc, hv⟩
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          rw [(hBotProps (leafWire j) hlt haf).2.2.1] at hv
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
          exact ⟨i, ⟨j, hjAc, hi⟩, hvi⟩
        · rintro ⟨i, ⟨j, hjAc, hi⟩, hvi⟩
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          exact ⟨j, hjAc, by rw [(hBotProps (leafWire j) hlt haf).2.2.1]; exact Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩⟩
      rw [hEq]
      calc ((Ic c).biUnion orVars).card ≤ ∑ i ∈ Ic c, (orVars i).card := Finset.card_biUnion_le
        _ ≤ ∑ i ∈ Ic c, 1 := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨j, hjAc, hij⟩ := Finset.mem_biUnion.mp hi
            obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
            obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
            have hiLt : i < 26 := (hBotProps (leafWire j) hlt haf).2.1 i hij
            rw [show i = (⟨i, hiLt⟩ : Fin 26).val from rfl, hOV_lt26]
            simp
        _ = (Ic c).card := by simp
    have hSumEc : 52 ≤ ∑ c : Fin 26, (Ec c).card := by
      let covPairs : Finset (Σ c : Fin 26, Fin 26) := Finset.univ.sigma Ec
      have hCovCard : covPairs.card = ∑ c : Fin 26, (Ec c).card := Finset.card_sigma Finset.univ Ec
      let toEdge : (Σ _ : Fin 26, Fin 26) → Fin 26 × Fin 26 := fun x =>
        if x.1 < x.2 then (x.1, x.2) else (x.2, x.1)
      have hSub : edges ⊆ covPairs.image toEdge := by
        intro p hp
        obtain ⟨hlt, hadj⟩ := (Finset.mem_filter.mp hp).2
        obtain ⟨j, hjA, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hEdgeCov p.1 p.2 hadj
        · apply Finset.mem_image.mpr
          refine ⟨⟨p.1, p.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjA, h1.symm⟩, h2⟩
          · simp [toEdge, hlt]
        · apply Finset.mem_image.mpr
          refine ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjA, h1.symm⟩, h2⟩
          · have hnot : ¬ (p.2 < p.1) := not_lt.mpr (le_of_lt hlt)
            simp [toEdge, hnot]
      rw [← hCovCard, ← hEdgeCard]
      exact (Finset.card_le_card hSub).trans Finset.card_image_le
    have hSumAc : ∑ c : Fin 26, (Ac c).card = A.card := by
      have hPart : Finset.univ.biUnion Ac = A := by
        ext j
        simp only [Ac, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun h => by obtain ⟨_, hj, _⟩ := h; exact hj, fun h => ⟨center j, h, rfl⟩⟩
      rw [← hPart, Finset.card_biUnion]
      intro c1 _ c2 _ hne
      change Disjoint (Ac c1) (Ac c2)
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      exact hne ((Finset.mem_filter.mp hj1).2.symm.trans (Finset.mem_filter.mp hj2).2)
    have hSumBc : ∑ c : Fin 26, (Bc c).card = Ball.card := by
      rw [Finset.card_biUnion]
      intro c1 _ c2 _ hne
      exact hBc_disj c1 c2 hne
    have hStep1 : 52 ≤ Ball.card + A.card := by
      calc 52 ≤ ∑ c : Fin 26, (Ec c).card := hSumEc
        _ ≤ ∑ c : Fin 26, (Ic c).card := Finset.sum_le_sum fun c _ => hEc_le_Ic c
        _ ≤ ∑ c : Fin 26, ((Bc c).card + (Ac c).card) := Finset.sum_le_sum fun c _ => hIc_bound c
        _ = Ball.card + A.card := by rw [Finset.sum_add_distrib, hSumBc, hSumAc]
    have hAllSub : Ball ∪ A ∪ T ⊆ Finset.range C.gates.length := by
      intro k hk
      rcases Finset.mem_union.mp hk with hk1 | hkT
      · rcases Finset.mem_union.mp hk1 with hkB | hkA
        · exact hBall_sub hkB
        · exact Finset.mem_range.mpr (hA_prop k hkA).1
      · exact Finset.mem_range.mpr (hT_prop k hkT).1
    have hCardAll : (Ball ∪ A ∪ T).card = Ball.card + A.card + T.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hBall_disj_T, hAT_disj⟩),
        Finset.card_union_of_disjoint hBall_disj_A]
    have hSizeGe : Ball.card + A.card + T.card ≤ C.size := by
      have := Finset.card_le_card hAllSub
      rw [hCardAll, Finset.card_range] at this
      exact this
    omega
  · by_cases hAP1 : andPairs 26 C = 1
    · exact h_one C W hFanLe hAP1 hLegal hSz hVal hComp
    · exact h_ge_two C W hFanLe (by omega) hLegal hSz hVal hComp
