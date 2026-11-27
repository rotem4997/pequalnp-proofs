import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5232_1
    (h_one :
      let f : (Fin 10 → Bool) → Bool := fun x =>
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
      ∀ (C : Circuit), IsAO2 11 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        C.size ≤ 18 → 11 ≤ C.output → C.output < 11 + C.size →
        andPairs 11 C = 1 →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ w ∈ (gateAt C j).inputs,
            ∃ x : Fin 10 → Bool, (C.wires (List.ofFn x ++ [x 0 || x 2])).getD w false = true ∧ f x = false) →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ f x)
    (h_ge_two :
      let f : (Fin 10 → Bool) → Bool := fun x =>
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
      ∀ (C : Circuit), IsAO2 11 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        C.size ≤ 18 → 11 ≤ C.output → C.output < 11 + C.size →
        2 ≤ andPairs 11 C →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ w ∈ (gateAt C j).inputs,
            ∃ x : Fin 10 → Bool, (C.wires (List.ofFn x ++ [x 0 || x 2])).getD w false = true ∧ f x = false) →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  let fP10 : (Fin 10 → Bool) → Bool := fun x =>
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
     x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
     x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  let adj : Fin 10 → Fin 10 → Bool := fun u v =>
    let e := fun a b => (u == a && v == b) || (u == b && v == a)
    e 0 1 || e 1 2 || e 2 3 || e 3 4 || e 4 0 ||
    e 0 5 || e 1 6 || e 2 7 || e 3 8 || e 4 9 ||
    e 5 7 || e 7 9 || e 9 6 || e 6 8 || e 8 5
  have hFP_single : ∀ u : Fin 10, fP10 (fun w => decide (w = u)) = false := by decide +kernel
  have hFP_pair : ∀ u v : Fin 10, fP10 (fun w => decide (w = u ∨ w = v)) = adj u v := by decide +kernel
  have hFP_false : fP10 (fun _ => false) = false := by decide +kernel
  have hFP_true : fP10 (fun _ => true) = true := by decide +kernel
  have hAdjSymm : ∀ u v : Fin 10, adj u v = adj v u := by decide +kernel
  have hAdjIrrefl : ∀ u : Fin 10, adj u u = false := by decide +kernel
  have hCommon02 : ∀ c : Fin 10, adj c 0 = true → adj c 2 = true → c = 1 := by decide +kernel
  have hNoC4List : ∀ u1 u2 : Fin 10, u1 ≠ u2 →
      ((List.finRange 10).filter fun v => adj u1 v && adj u2 v).length ≤ 1 := by decide +kernel
  have hNoC4 : ∀ u1 u2 v1 v2 : Fin 10, u1 ≠ u2 → v1 ≠ v2 →
      adj u1 v1 = true → adj u1 v2 = true → adj u2 v1 = true → adj u2 v2 = true → False := by
    intro u1 u2 v1 v2 hune hvne h11 h12 h21 h22
    have hle := hNoC4List u1 u2 hune
    have hnd : ((List.finRange 10).filter fun v => adj u1 v && adj u2 v).Nodup :=
      (List.nodup_finRange 10).filter _
    have hm1 : v1 ∈ (List.finRange 10).filter fun v => adj u1 v && adj u2 v := by
      rw [List.mem_filter]; exact ⟨List.mem_finRange v1, by simp [h11, h21]⟩
    have hm2 : v2 ∈ (List.finRange 10).filter fun v => adj u1 v && adj u2 v := by
      rw [List.mem_filter]; exact ⟨List.mem_finRange v2, by simp [h12, h22]⟩
    have hsub : ({v1, v2} : Finset (Fin 10)) ⊆ ((List.finRange 10).filter fun v => adj u1 v && adj u2 v).toFinset := by
      intro w hw
      rw [List.mem_toFinset]
      rcases Finset.mem_insert.mp hw with rfl | hw2
      · exact hm1
      · rw [Finset.mem_singleton.mp hw2]; exact hm2
    have hc2 : 2 ≤ ((List.finRange 10).filter fun v => adj u1 v && adj u2 v).length := by
      calc 2 = ({v1, v2} : Finset (Fin 10)).card := (Finset.card_pair hvne).symm
        _ ≤ ((List.finRange 10).filter fun v => adj u1 v && adj u2 v).toFinset.card := Finset.card_le_card hsub
        _ ≤ _ := List.toFinset_card_le _
    omega
  have hC5_out : adj 0 1 = true ∧ adj 1 2 = true ∧ adj 2 3 = true ∧ adj 3 4 = true ∧ adj 4 0 = true := by decide +kernel
  have hC5_in : adj 5 7 = true ∧ adj 7 9 = true ∧ adj 9 6 = true ∧ adj 6 8 = true ∧ adj 8 5 = true := by decide +kernel
  have hUniv10 : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide +kernel
  have hEdgesCard : (Finset.univ.filter fun p : Fin 10 × Fin 10 => p.1 < p.2 ∧ adj p.1 p.2 = true).card = 15 := by
    decide +kernel
  classical
  let inp : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 2]
  let Good : Circuit → Prop := fun C =>
    Monotone2 C ∧ ReadsBack 11 C ∧ 11 ≤ C.output ∧ C.output < 11 + C.size ∧
      ∀ x : Fin 10 → Bool, C.eval (inp x) = fP10 x
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wF : List Gate → List Bool → List Bool := fun gs w => gs.foldl stepW w
  let R : Bool → Bool → Prop := fun a b => a = true → b = true
  have hInpLen : ∀ x : Fin 10 → Bool, (inp x).length = 11 := by
    intro x; simp [inp]
  have hInpGet : ∀ (x : Fin 10 → Bool) (i : Fin 10), (inp x).getD i.val false = x i := by
    intro x i
    rw [show inp x = List.ofFn x ++ [x 0 || x 2] from rfl]
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  have hInp10 : ∀ x : Fin 10 → Bool, (inp x).getD 10 false = (x 0 || x 2) := by
    intro x
    rw [show inp x = List.ofFn x ++ [x 0 || x 2] from rfl]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hLenWF : ∀ (gs : List Gate) (w : List Bool), (wF gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wF]
    | cons g gs ih =>
      intro w
      change (wF gs (stepW w g)).length = w.length + (gs.length + 1)
      rw [ih]; simp [stepW]; omega
  have hWFAppend : ∀ (gs1 gs2 : List Gate) (w : List Bool), wF (gs1 ++ gs2) w = wF gs2 (wF gs1 w) := by
    intro gs1 gs2 w; exact List.foldl_append
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
  have hReadMono : ∀ {w1 w2 : List Bool}, List.Forall₂ R w1 w2 →
      ∀ i : ℕ, R (w1.getD i false) (w2.getD i false) := by
    intro w1 w2 hrel
    induction hrel with
    | nil => intro i h; simp at h
    | cons h _ ih =>
      intro i
      cases i with
      | zero => exact h
      | succ j => exact ih j
  have hMonoWF : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ {w1 w2 : List Bool}, List.Forall₂ R w1 w2 →
      List.Forall₂ R (wF gs w1) (wF gs w2) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; exact h
    | cons g gs ih =>
      intro hops w1 w2 hrel
      apply ih (fun h hh => hops h (List.mem_cons_of_mem _ hh))
      apply List.rel_append hrel
      apply List.Forall₂.cons _ List.Forall₂.nil
      rcases hops g (by simp) with hand | hor
      · rw [hand]
        change (g.inputs.map (fun i => w1.getD i false)).all id = true →
          (g.inputs.map (fun i => w2.getD i false)).all id = true
        simp only [List.all_map, Function.comp_def, List.all_eq_true, id_eq]
        intro h1 i hi
        exact hReadMono hrel i (h1 i hi)
      · rw [hor]
        change (g.inputs.map (fun i => w1.getD i false)).any id = true →
          (g.inputs.map (fun i => w2.getD i false)).any id = true
        simp only [List.any_map, Function.comp_def, List.any_eq_true, id_eq]
        rintro ⟨i, hi, h1⟩
        exact ⟨i, hi, hReadMono hrel i h1⟩
  have hEvalAnd : ∀ ls : List Bool, GateOp.and.eval ls = ls.all id := fun _ => rfl
  have hEvalOr : ∀ ls : List Bool, GateOp.or.eval ls = ls.any id := fun _ => rfl
  have hGateAt : ∀ (C : Circuit) (j : ℕ), gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have hGateAtEq : ∀ (C : Circuit) (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro C j hj
    rw [hGateAt, List.getD_eq_getElem C.gates _ hj]
  have hWireGate : ∀ (C : Circuit) (x : List Bool) (j : ℕ),
      ReadsBack x.length C → j < C.gates.length →
      (C.wires x).getD (x.length + j) false =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
    intro C x j hRB hj
    have hSplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hTakeLen : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
    have hPreLen : (wF (C.gates.take j) x).length = x.length + j := by
      rw [hLenWF, hTakeLen]
    have hWires : C.wires x = wF (C.gates.drop (j + 1)) (stepW (wF (C.gates.take j) x) C.gates[j]) := by
      change wF C.gates x = _
      conv_lhs => rw [hSplit]
      rw [hWFAppend]
      rfl
    have hStepVal : (C.wires x).getD (x.length + j) false =
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => (wF (C.gates.take j) x).getD i false) := by
      rw [hWires, hWFLt _ _ _ (by dsimp only [stepW]; simp [hPreLen])]
      dsimp only [stepW]
      rw [List.getD_append_right _ _ _ _ (by omega), hPreLen, Nat.sub_self]
      rfl
    rw [hStepVal, hGateAtEq C j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiLt : i < x.length + j := hRB j hj i (by rw [hGateAtEq C j hj]; exact hi)
    rw [hWires]
    symm
    rw [hWFLt _ _ _ (by dsimp only [stepW]; simp [hPreLen]; omega)]
    dsimp only [stepW]
    exact List.getD_append _ _ _ _ (by omega)
  have hMonoOps : ∀ (C : Circuit), Monotone2 C → ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro C hM g hg
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hNoInpEq : ∀ r < 11, ∃ x : Fin 10 → Bool, (inp x).getD r false = true ∧ fP10 x = false := by
    intro r hr
    by_cases h10 : r < 10
    · refine ⟨fun z => decide (z = ⟨r, h10⟩), ?_, hFP_single ⟨r, h10⟩⟩
      rw [hInpGet _ ⟨r, h10⟩]
      simp
    · have hr10 : r = 10 := by omega
      subst hr10
      refine ⟨fun z => decide (z = 0), ?_, hFP_single 0⟩
      rw [hInp10]
      simp
  have hVC6 : ∀ T : Finset (Fin 10), (∀ u v : Fin 10, adj u v = true → u ∈ T ∨ v ∈ T) → 6 ≤ T.card := by
    intro T hT
    have hc : ∀ a b c d e : Fin 10,
        adj a b = true → adj b c = true → adj c d = true → adj d e = true → adj e a = true →
        3 ≤ (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) + (if c ∈ T then 1 else 0) +
            (if d ∈ T then 1 else 0) + (if e ∈ T then 1 else 0) := by
      intro a b c d e hab hbc hcd hde hea
      have h1 : 1 ≤ (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) := by
        rcases hT a b hab with h | h <;> simp [h]
      have h2 : 1 ≤ (if b ∈ T then 1 else 0) + (if c ∈ T then 1 else 0) := by
        rcases hT b c hbc with h | h <;> simp [h]
      have h3 : 1 ≤ (if c ∈ T then 1 else 0) + (if d ∈ T then 1 else 0) := by
        rcases hT c d hcd with h | h <;> simp [h]
      have h4 : 1 ≤ (if d ∈ T then 1 else 0) + (if e ∈ T then 1 else 0) := by
        rcases hT d e hde with h | h <;> simp [h]
      have h5 : 1 ≤ (if e ∈ T then 1 else 0) + (if a ∈ T then 1 else 0) := by
        rcases hT e a hea with h | h <;> simp [h]
      omega
    have hOut := hc 0 1 2 3 4 hC5_out.1 hC5_out.2.1 hC5_out.2.2.1 hC5_out.2.2.2.1 hC5_out.2.2.2.2
    have hIn := hc 5 7 9 6 8 hC5_in.1 hC5_in.2.1 hC5_in.2.2.1 hC5_in.2.2.2.1 hC5_in.2.2.2.2
    have hCard : T.card = ∑ i ∈ (Finset.univ : Finset (Fin 10)), if i ∈ T then 1 else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, smul_eq_mul, mul_one]
    rw [hCard, hUniv10]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      Fin.isValue, Fin.reduceEq, or_self, not_false_eq_true]
    omega
  have hErase : ∀ (C : Circuit), Good C → ∀ (d r : ℕ), d < C.gates.length → r < 11 + d →
      ((∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + d) false = (C.wires (inp x)).getD r false) ∨
       (∀ x : Fin 10 → Bool,
         ((C.wires (inp x)).getD (11 + d) false = true → (C.wires (inp x)).getD r false = true) ∧
         ((C.wires (inp x)).getD r false = true → fP10 x = true))) →
      ∃ C' : Circuit, Good C' ∧ C'.size < C.size := by
    intro C hG d r hd hr hCond
    obtain ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ := hG
    let rn : ℕ → ℕ := fun w => if w < 11 + d then w else if w = 11 + d then r else w - 1
    let rnG : Gate → Gate := fun g => ⟨g.op, g.inputs.map rn⟩
    let pre : List Gate := C.gates.take d
    let gd : Gate := C.gates[d]
    let post : List Gate := C.gates.drop (d + 1)
    have hPreLen : pre.length = d := List.length_take_of_le (le_of_lt hd)
    have hSplit : C.gates = pre ++ gd :: post := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hPostLen : post.length = C.gates.length - d - 1 := by simp [post]; omega
    let C' : Circuit := ⟨pre ++ post.map rnG, rn C.output⟩
    have hSize' : C'.size = C.size - 1 := by
      change (pre ++ post.map rnG).length = C.gates.length - 1
      rw [List.length_append, List.length_map, hPreLen, hPostLen]
      omega
    have hM' : Monotone2 C' := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hM g (List.mem_of_mem_take h1)
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp h2
        have hhC : h ∈ C.gates := List.mem_of_mem_drop hh
        obtain ⟨hop, hlen⟩ := hM h hhC
        exact ⟨hop, by simp [rnG, hlen]⟩
    have hRB' : ReadsBack 11 C' := by
      intro j hj w hw
      have hgat : gateAt C' j = C'.gates[j] := hGateAtEq C' j hj
      rw [hgat] at hw
      by_cases hjd : j < d
      · have hjeq : C'.gates[j] = C.gates[j] := by
          change (pre ++ post.map rnG)[j] = C.gates[j]
          rw [List.getElem_append_left (by omega)]
          exact List.getElem_take
        rw [hjeq] at hw
        exact hRB j (by omega) w (by rw [hGateAtEq C j (by omega)]; exact hw)
      · have hjpost : j - d < post.length := by
          have : C'.gates.length = d + post.length := by
            change (pre ++ post.map rnG).length = _
            rw [List.length_append, List.length_map, hPreLen]
          omega
        have hjeq : C'.gates[j] = rnG post[j - d] := by
          change (pre ++ post.map rnG)[j] = _
          rw [List.getElem_append_right (by omega : pre.length ≤ j)]
          simp only [hPreLen, List.getElem_map]
        rw [hjeq] at hw
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
        have hposteq : post[j - d] = C.gates[j + 1]'(by omega) := by
          simp only [post, List.getElem_drop]
          congr 1; omega
        have hw0lt : w0 < 11 + (j + 1) :=
          hRB (j + 1) (by omega) w0 (by rw [hGateAtEq C (j + 1) (by omega), ← hposteq]; exact hw0)
        dsimp only [rn]
        split_ifs <;> omega
    have hGetRn : ∀ (A E : List Bool) (b : Bool), A.length = 11 + d → A.getD r false = b →
        ∀ i : ℕ, (A ++ E).getD (rn i) false = (A ++ b :: E).getD i false := by
      intro A E b hAlen hAr i
      dsimp only [rn]
      by_cases h1 : i < 11 + d
      · rw [if_pos h1, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      · rw [if_neg h1]
        by_cases h2 : i = 11 + d
        · rw [if_pos h2, h2, List.getD_append _ _ _ _ (by omega), hAr,
            List.getD_append_right _ _ _ _ (by omega), hAlen, Nat.sub_self]
          rfl
        · rw [if_neg h2, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), hAlen]
          have hsub : i - (11 + d) = (i - 1 - (11 + d)) + 1 := by omega
          rw [hsub]
          rfl
    have hRunRn : ∀ (A : List Bool) (b : Bool), A.length = 11 + d → A.getD r false = b →
        ∀ (gs : List Gate) (E : List Bool),
        ∃ E2 : List Bool, wF gs (A ++ b :: E) = A ++ b :: E2 ∧ wF (gs.map rnG) (A ++ E) = A ++ E2 := by
      intro A b hAlen hAr gs
      induction gs with
      | nil => intro E; exact ⟨E, rfl, rfl⟩
      | cons h gs ih =>
        intro E
        have hev : h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false) =
            (rnG h).op.eval ((rnG h).inputs.map fun i => (A ++ E).getD i false) := by
          dsimp only [rnG]
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact (hGetRn A E b hAlen hAr i).symm
        obtain ⟨E2, h1, h2⟩ := ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        refine ⟨E2, ?_, ?_⟩
        · change wF gs ((A ++ b :: E) ++ _) = _
          rw [List.append_assoc, List.cons_append]
          exact h1
        · change wF (gs.map rnG) ((A ++ E) ++ _) = _
          rw [← hev, List.append_assoc]
          exact h2
    have hComp' : ∀ x : Fin 10 → Bool, C'.eval (inp x) = fP10 x := by
      intro x
      let A := wF pre (inp x)
      have hAlen : A.length = 11 + d := by rw [hLenWF, hInpLen, hPreLen]
      let bd := gd.op.eval (gd.inputs.map fun i => A.getD i false)
      let br := A.getD r false
      have hWiresC : C.wires (inp x) = wF post (A ++ [bd]) := by
        change wF C.gates (inp x) = _
        conv_lhs => rw [hSplit]
        rw [hWFAppend]
        rfl
      have hValD : (C.wires (inp x)).getD (11 + d) false = bd := by
        rw [hWiresC, hWFLt _ _ _ (by simp [hAlen]), List.getD_append_right _ _ _ _ (by omega),
          hAlen, Nat.sub_self]
        rfl
      have hValR : (C.wires (inp x)).getD r false = br := by
        rw [hWiresC, hWFLt _ _ _ (by simp [hAlen]; omega), List.getD_append _ _ _ _ (by omega)]
      obtain ⟨E2, hEold, hEnew⟩ := hRunRn A br hAlen rfl post []
      have hEvalNew : C'.eval (inp x) = (wF post (A ++ [br])).getD C.output false := by
        change (wF (pre ++ post.map rnG) (inp x)).getD (rn C.output) false = _
        rw [hWFAppend]
        change (wF (post.map rnG) A).getD (rn C.output) false = _
        have hAnil : A = A ++ [] := (List.append_nil A).symm
        conv_lhs => rw [hAnil]
        rw [hEnew, hGetRn A E2 br hAlen rfl C.output, ← hEold]
      have hEvalOld : C.eval (inp x) = (wF post (A ++ [bd])).getD C.output false := by
        change (C.wires (inp x)).getD C.output false = _
        rw [hWiresC]
      rw [hEvalNew]
      rcases hCond with hEq | hLe
      · have hbrbd : br = bd := by rw [← hValR, ← hValD, hEq x]
        rw [hbrbd, ← hEvalOld, hComp x]
      · obtain ⟨hle, hbel⟩ := hLe x
        rw [hValD, hValR] at hle
        rw [hValR] at hbel
        cases hbr : br with
        | false =>
          have hbd : bd = false := by
            cases hbd' : bd with
            | false => rfl
            | true => exfalso; have := hle hbd'; rw [hbr] at this; exact Bool.false_ne_true this
          have hstep : (wF post (A ++ [false])).getD C.output false = (wF post (A ++ [bd])).getD C.output false := by
            rw [hbd]
          rw [hstep, ← hEvalOld, hComp x]
        | true =>
          have hf : fP10 x = true := hbel hbr
          rw [hf]
          have hrel : List.Forall₂ R (A ++ [bd]) (A ++ [true]) := by
            apply List.rel_append
            · exact List.forall₂_iff_get.mpr ⟨rfl, fun _ _ _ h => h⟩
            · exact List.Forall₂.cons (fun _ => rfl) List.Forall₂.nil
          have hpostOps : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
            fun g hg => hMonoOps C hM g (List.mem_of_mem_drop hg)
          have hmono := hReadMono (hMonoWF post hpostOps hrel) C.output
          exact hmono (by rw [← hEvalOld, hComp x, hf])
    have hOutLo' : 11 ≤ C'.output := by
      by_contra hlt
      have hlt' : C'.output < 11 := by omega
      obtain ⟨x, hx1, hx2⟩ := hNoInpEq C'.output hlt'
      have hce : C'.eval (inp x) = (inp x).getD C'.output false := by
        change (wF C'.gates (inp x)).getD C'.output false = _
        exact hWFLt C'.gates (inp x) C'.output (by rw [hInpLen]; exact hlt')
      rw [hComp' x] at hce
      rw [hx1, hx2] at hce
      exact Bool.false_ne_true hce
    have hOutHi' : C'.output < 11 + C'.size := by
      have hCsz : C.size = C.gates.length := rfl
      rw [hSize']
      change rn C.output < 11 + (C.size - 1)
      dsimp only [rn]
      split_ifs <;> omega
    exact ⟨C', ⟨hM', hRB', hOutLo', hOutHi', hComp'⟩, by have : C.size = C.gates.length := rfl; omega⟩
  have hEraseConst : ∀ (C : Circuit), Good C → ∀ d < C.gates.length,
      (gateAt C d).inputs = [] → ∃ C' : Circuit, Good C' ∧ C'.size < C.size := by
    intro C hG d hd hEmpty
    obtain ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ := hG
    let gd : Gate := C.gates[d]
    have hgdEmpty : gd.inputs = [] := by
      change C.gates[d].inputs = []
      rw [← hGateAtEq C d hd]
      exact hEmpty
    let b : Bool := gd.op.eval []
    let sk : ℕ → ℕ := fun w => if w < 11 + d then w else w - 1
    let simpG : Gate → Gate := fun g =>
      if (11 + d) ∈ g.inputs then
        if g.op = GateOp.and then
          if b = false then ⟨GateOp.or, []⟩
          else ⟨GateOp.and, (g.inputs.filter (fun i => i != 11 + d)).map sk⟩
        else
          if b = true then ⟨GateOp.and, []⟩
          else ⟨GateOp.or, (g.inputs.filter (fun i => i != 11 + d)).map sk⟩
      else ⟨g.op, g.inputs.map sk⟩
    let pre : List Gate := C.gates.take d
    let post : List Gate := C.gates.drop (d + 1)
    have hPreLen : pre.length = d := List.length_take_of_le (le_of_lt hd)
    have hSplit : C.gates = pre ++ gd :: post := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hPostLen : post.length = C.gates.length - d - 1 := by simp [post]; omega
    have hOutNe : C.output ≠ 11 + d := by
      intro heq
      have hconst : ∀ x : Fin 10 → Bool, C.eval (inp x) = b := by
        intro x
        change (wF C.gates (inp x)).getD C.output false = b
        rw [heq]
        conv_lhs => rw [hSplit, hWFAppend]
        have hPL : (wF pre (inp x)).length = 11 + d := by rw [hLenWF, hInpLen, hPreLen]
        change (wF post (wF pre (inp x) ++ [gd.op.eval (gd.inputs.map _)])).getD (11 + d) false = b
        rw [hWFLt _ _ _ (by simp [hPL]), List.getD_append_right _ _ _ _ (by omega), hPL, Nat.sub_self, hgdEmpty]
        rfl
      have h0 := hconst (fun _ => false)
      have h1 := hconst (fun _ => true)
      rw [hComp, hFP_false] at h0
      rw [hComp, hFP_true] at h1
      rw [← h0] at h1
      exact Bool.false_ne_true h1.symm
    let C' : Circuit := ⟨pre ++ post.map simpG, sk C.output⟩
    have hSize' : C'.size = C.size - 1 := by
      change (pre ++ post.map simpG).length = C.gates.length - 1
      rw [List.length_append, List.length_map, hPreLen, hPostLen]
      omega
    have hM' : Monotone2 C' := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hM g (List.mem_of_mem_take h1)
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp h2
        obtain ⟨hop, hlen⟩ := hM h (List.mem_of_mem_drop hh)
        dsimp only [simpG]
        split_ifs
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inl rfl, by
            rw [List.length_map]
            exact (List.length_filter_le _ _).trans hlen⟩
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr rfl, by
            rw [List.length_map]
            exact (List.length_filter_le _ _).trans hlen⟩
        · exact ⟨hop, by rw [List.length_map]; exact hlen⟩
    have hRB' : ReadsBack 11 C' := by
      intro j hj w hw
      rw [hGateAtEq C' j hj] at hw
      by_cases hjd : j < d
      · have hjeq : C'.gates[j] = C.gates[j] := by
          change (pre ++ post.map simpG)[j] = C.gates[j]
          rw [List.getElem_append_left (by omega)]
          exact List.getElem_take
        rw [hjeq] at hw
        exact hRB j (by omega) w (by rw [hGateAtEq C j (by omega)]; exact hw)
      · have hjpost : j - d < post.length := by
          have : C'.gates.length = d + post.length := by
            change (pre ++ post.map simpG).length = _
            rw [List.length_append, List.length_map, hPreLen]
          omega
        have hjeq : C'.gates[j] = simpG post[j - d] := by
          change (pre ++ post.map simpG)[j] = _
          rw [List.getElem_append_right (by omega : pre.length ≤ j)]
          simp only [hPreLen, List.getElem_map]
        have hposteq : post[j - d] = C.gates[j + 1]'(by omega) := by
          simp only [post, List.getElem_drop]
          congr 1; omega
        rw [hjeq] at hw
        have hmem_sk : ∀ (l : List ℕ), (∀ x ∈ l, x < 11 + (j + 1) ∧ x ≠ 11 + d) →
            w ∈ l.map sk → w < 11 + j := by
          intro l hl hwm
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hwm
          obtain ⟨hxl, hxn⟩ := hl x hx
          dsimp only [sk]
          split_ifs <;> omega
        dsimp only [simpG] at hw
        split_ifs at hw with h1 h2 h3 h4
        · simp at hw
        · exact hmem_sk _ (fun x hx => by
            obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
            exact ⟨hRB (j + 1) (by omega) x (by rw [hGateAtEq C (j + 1) (by omega), ← hposteq]; exact hx1),
              by simpa using hx2⟩) hw
        · simp at hw
        · exact hmem_sk _ (fun x hx => by
            obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
            exact ⟨hRB (j + 1) (by omega) x (by rw [hGateAtEq C (j + 1) (by omega), ← hposteq]; exact hx1),
              by simpa using hx2⟩) hw
        · exact hmem_sk _ (fun x hx =>
            ⟨hRB (j + 1) (by omega) x (by rw [hGateAtEq C (j + 1) (by omega), ← hposteq]; exact hx),
              fun hEq => h1 (hEq ▸ hx)⟩) hw
    have hGetSk : ∀ (A E : List Bool), A.length = 11 + d → ∀ i : ℕ, i ≠ 11 + d →
        (A ++ E).getD (sk i) false = (A ++ b :: E).getD i false := by
      intro A E hAlen i hne
      dsimp only [sk]
      by_cases h1 : i < 11 + d
      · rw [if_pos h1, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      · rw [if_neg h1, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hAlen]
        have hsub : i - (11 + d) = (i - 1 - (11 + d)) + 1 := by omega
        rw [hsub]
        rfl
    have hGetMid : ∀ (A E : List Bool), A.length = 11 + d → (A ++ b :: E).getD (11 + d) false = b := by
      intro A E hAlen
      rw [List.getD_append_right _ _ _ _ (by omega), hAlen, Nat.sub_self]
      rfl
    have hSimpEval : ∀ (A E : List Bool), A.length = 11 + d →
        ∀ h : Gate, (h.op = GateOp.and ∨ h.op = GateOp.or) →
        h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false) =
        (simpG h).op.eval ((simpG h).inputs.map fun i => (A ++ E).getD i false) := by
      intro A E hAlen h hop
      dsimp only [simpG]
      by_cases hmem : 11 + d ∈ h.inputs
      · rw [if_pos hmem]
        rcases hop with hand | hor
        · rw [hand, if_pos rfl]
          cases hb : b with
          | false =>
            rw [if_pos rfl]
            simp only [hEvalAnd, hEvalOr, List.map_nil, List.any_nil]
            rw [List.all_eq_false]
            exact ⟨false, List.mem_map.mpr ⟨11 + d, hmem, by
              have hm := hGetMid A E hAlen
              rw [hb] at hm; exact hm⟩, by simp⟩
          | true =>
            rw [if_neg (by decide)]
            simp only [hEvalAnd]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, id_eq]
            constructor
            · intro h1 v hv
              obtain ⟨w, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩ := hv
              have hsk := hGetSk A E hAlen i hne
              rw [hb] at hsk; rw [hsk]
              exact h1 _ ⟨i, hi, rfl⟩
            · intro h2 v hv
              obtain ⟨i, hi, rfl⟩ := hv
              by_cases hne : i = 11 + d
              · have hm := hGetMid A E hAlen
                rw [hb] at hm; rw [hne, hm]
              · have hsk := hGetSk A E hAlen i hne
                rw [hb] at hsk; rw [← hsk]
                exact h2 _ ⟨sk i, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩
        · rw [hor, if_neg (fun heq => GateOp.noConfusion heq)]
          cases hb : b with
          | true =>
            rw [if_pos rfl]
            simp only [hEvalAnd, hEvalOr, List.map_nil, List.all_nil]
            rw [List.any_eq_true]
            exact ⟨true, List.mem_map.mpr ⟨11 + d, hmem, by
              have hm := hGetMid A E hAlen
              rw [hb] at hm; exact hm⟩, by simp⟩
          | false =>
            rw [if_neg (by decide)]
            simp only [hEvalOr]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, id_eq]
            constructor
            · rintro ⟨_, ⟨i, hi, rfl⟩, ht⟩
              by_cases hne : i = 11 + d
              · have hm := hGetMid A E hAlen
                rw [hb] at hm; rw [hne, hm] at ht; exact absurd ht (by decide)
              · have hsk := hGetSk A E hAlen i hne
                rw [hb] at hsk
                exact ⟨_, ⟨sk i, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩, by rw [hsk]; exact ht⟩
            · rintro ⟨_, ⟨_, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩, ht⟩
              have hsk := hGetSk A E hAlen i hne
              rw [hb] at hsk
              exact ⟨_, ⟨i, hi, rfl⟩, by rw [← hsk]; exact ht⟩
      · rw [if_neg hmem]
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact (hGetSk A E hAlen i (fun hEq => hmem (hEq ▸ hi))).symm
    have hRunSimp : ∀ (A : List Bool), A.length = 11 + d →
        ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ (E : List Bool),
        ∃ E2 : List Bool, wF gs (A ++ b :: E) = A ++ b :: E2 ∧ wF (gs.map simpG) (A ++ E) = A ++ E2 := by
      intro A hAlen gs
      induction gs with
      | nil => intro _ E; exact ⟨E, rfl, rfl⟩
      | cons h gs ih =>
        intro hops E
        have hev := hSimpEval A E hAlen h (hops h (by simp))
        obtain ⟨E2, h1, h2⟩ := ih (fun g hg => hops g (List.mem_cons_of_mem _ hg))
          (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        refine ⟨E2, ?_, ?_⟩
        · change wF gs ((A ++ b :: E) ++ _) = _
          rw [List.append_assoc, List.cons_append]
          exact h1
        · change wF (gs.map simpG) ((A ++ E) ++ _) = _
          rw [← hev, List.append_assoc]
          exact h2
    have hComp' : ∀ x : Fin 10 → Bool, C'.eval (inp x) = fP10 x := by
      intro x
      let A := wF pre (inp x)
      have hAlen : A.length = 11 + d := by rw [hLenWF, hInpLen, hPreLen]
      have hpostOps : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg => hMonoOps C hM g (List.mem_of_mem_drop hg)
      obtain ⟨E2, hEold, hEnew⟩ := hRunSimp A hAlen post hpostOps []
      have hEvalC : C.eval (inp x) = (A ++ b :: E2).getD C.output false := by
        change (wF C.gates (inp x)).getD C.output false = _
        conv_lhs => rw [hSplit, hWFAppend]
        change (wF post (A ++ [gd.op.eval (gd.inputs.map _)])).getD C.output false = _
        rw [hgdEmpty]
        change (wF post (A ++ b :: [])).getD C.output false = _
        rw [hEold]
      have hEvalC' : C'.eval (inp x) = (A ++ E2).getD (sk C.output) false := by
        change (wF (pre ++ post.map simpG) (inp x)).getD (sk C.output) false = _
        rw [hWFAppend]
        change (wF (post.map simpG) A).getD (sk C.output) false = _
        have hAnil : A = A ++ [] := (List.append_nil A).symm
        conv_lhs => rw [hAnil]
        rw [hEnew]
      rw [hEvalC', hGetSk A E2 hAlen C.output hOutNe, ← hEvalC, hComp x]
    have hOutLo' : 11 ≤ C'.output := by
      change 11 ≤ sk C.output
      dsimp only [sk]
      split_ifs <;> omega
    have hOutHi' : C'.output < 11 + C'.size := by
      have hCsz : C.size = C.gates.length := rfl
      rw [hSize']
      change sk C.output < 11 + (C.size - 1)
      dsimp only [sk]
      split_ifs <;> omega
    exact ⟨C', ⟨hM', hRB', hOutLo', hOutHi', hComp'⟩, by have : C.size = C.gates.length := rfl; omega⟩
  intro C0 hM0 hRB0 hSz0 hOutLo0 hOutHi0
  by_contra hContra0
  push Not at hContra0
  have hEx : ∃ s : ℕ, ∃ C : Circuit, Good C ∧ C.size = s :=
    ⟨C0.size, C0, ⟨hM0, hRB0, hOutLo0, hOutHi0, hContra0⟩, rfl⟩
  let sMin := Nat.find hEx
  obtain ⟨C, hGood, hCsz⟩ := Nat.find_spec hEx
  have hMin : ∀ C' : Circuit, Good C' → C.size ≤ C'.size := by
    intro C' hG'
    rw [hCsz]
    exact Nat.find_min' hEx ⟨C', hG', rfl⟩
  have hSzLe : C.size ≤ 18 := by
    have := hMin C0 ⟨hM0, hRB0, hOutLo0, hOutHi0, hContra0⟩
    omega
  obtain ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ := hGood
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := by
    intro g hg
    obtain ⟨d, hd, hgd⟩ := List.mem_iff_getElem.mp hg
    have hle := (hM g hg).2
    rcases hlen : g.inputs.length with _ | _ | k
    · have hemp : (gateAt C d).inputs = [] := by
        rw [hGateAtEq C d hd, hgd]
        exact List.eq_nil_of_length_eq_zero hlen
      obtain ⟨C', hG', hlt⟩ := hEraseConst C ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ d hd hemp
      exact absurd (hMin C' hG') (by omega)
    · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
      have hga : (gateAt C d).inputs = [a] := by rw [hGateAtEq C d hd, hgd, ha]
      have haLt : a < 11 + d := hRB d hd a (by rw [hga]; simp)
      have heq : ∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + d) false = (C.wires (inp x)).getD a false := by
        intro x
        rw [show (11 : ℕ) = (inp x).length from (hInpLen x).symm]
        rw [hWireGate C (inp x) d (by rw [hInpLen]; exact hRB) hd, hga]
        rcases hMonoOps C hM (gateAt C d) (by rw [hGateAtEq C d hd]; exact List.getElem_mem hd) with hop | hop
        · rw [hop, hEvalAnd]; simp
        · rw [hop, hEvalOr]; simp
      obtain ⟨C', hG', hlt⟩ := hErase C ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ d a hd haLt (Or.inl heq)
      exact absurd (hMin C' hG') (by omega)
    · omega
  have hAO2 : IsAO2 11 C := ⟨hMonoOps C hM, hRB, hLen2⟩
  have hDist : ∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by
    intro g hg heq
    obtain ⟨d, hd, hgd⟩ := List.mem_iff_getElem.mp hg
    have hl2 : g.inputs.length = 2 := hLen2 g hg
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl2
    rw [hab] at heq
    have habEq : a = b := heq
    subst habEq
    have hga : (gateAt C d).inputs = [a, a] := by rw [hGateAtEq C d hd, hgd, hab]
    have haLt : a < 11 + d := hRB d hd a (by rw [hga]; simp)
    have hweq : ∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + d) false = (C.wires (inp x)).getD a false := by
      intro x
      rw [show (11 : ℕ) = (inp x).length from (hInpLen x).symm]
      rw [hWireGate C (inp x) d (by rw [hInpLen]; exact hRB) hd, hga]
      rcases hMonoOps C hM (gateAt C d) (by rw [hGateAtEq C d hd]; exact List.getElem_mem hd) with hop | hop
      · rw [hop, hEvalAnd]; simp
      · rw [hop, hEvalOr]; simp
    obtain ⟨C', hG', hlt⟩ := hErase C ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ d a hd haLt (Or.inl hweq)
    exact absurd (hMin C' hG') (by omega)
  have hTopForm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs,
        ∃ x : Fin 10 → Bool, (C.wires (inp x)).getD w false = true ∧ fP10 x = false := by
    intro j hj hop w hw
    by_contra hno
    push Not at hno
    have hwLt : w < 11 + j := hRB j hj w hw
    have hCond : ∀ x : Fin 10 → Bool,
        ((C.wires (inp x)).getD (11 + j) false = true → (C.wires (inp x)).getD w false = true) ∧
        ((C.wires (inp x)).getD w false = true → fP10 x = true) := by
      intro x
      constructor
      · intro hjT
        rw [show (11 : ℕ) = (inp x).length from (hInpLen x).symm] at hjT
        rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop] at hjT
        change ((gateAt C j).inputs.map fun i => (C.wires (inp x)).getD i false).all id = true at hjT
        simp only [List.all_map, Function.comp_def, List.all_eq_true, id_eq] at hjT
        exact hjT w hw
      · intro hwT
        cases hf : fP10 x with
        | true => rfl
        | false => exact absurd hf (hno x hwT)
    obtain ⟨C', hG', hlt⟩ := hErase C ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ j w hj hwLt (Or.inr hCond)
    exact absurd (hMin C' hG') (by omega)
  by_cases hAP0 : andPairs 11 C = 0
  · have hConeStep : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 11 cs g =
        cs ++ [(g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
          (fun w => (w - 11) :: cs.getD (w - 11) [])] := fun _ _ => rfl
    have hConesLen : ∀ gs : List Gate, ∀ cs : List (List ℕ),
        (gs.foldl (coneStep 11) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih, hConeStep]
        simp; omega
    have hConesLt : ∀ gs : List Gate, ∀ cs : List (List ℕ), ∀ i < cs.length,
        (gs.foldl (coneStep 11) cs).getD i [] = cs.getD i [] := by
      intro gs
      induction gs with
      | nil => intro cs i _; rfl
      | cons g gs ih =>
        intro cs i hi
        rw [List.foldl_cons, ih _ i (by rw [hConeStep]; simp; omega), hConeStep]
        exact List.getD_append cs _ [] i hi
    have hConeMem : ∀ (j : ℕ) (hj : j < C.gates.length) (w : ℕ),
        w ∈ (gateAt C j).inputs → 11 ≤ w →
        InCone 11 C (w - 11) j ∧ ∀ i : ℕ, InCone 11 C i (w - 11) → InCone 11 C i j := by
      intro j hj w hw hw11
      have hwLt : w < 11 + j := hRB j hj w hw
      have hSplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      let cs := (C.gates.take j).foldl (coneStep 11) []
      have hcsLen : cs.length = j := by
        rw [hConesLen, List.length_nil, Nat.zero_add, List.length_take_of_le (le_of_lt hj)]
      have hConesEq : cones 11 C = (C.gates.drop (j + 1)).foldl (coneStep 11) (coneStep 11 cs C.gates[j]) := by
        unfold cones
        conv_lhs => rw [hSplit]
        rw [List.foldl_append, List.foldl_cons]
      have hGetJ : (cones 11 C).getD j [] =
          (C.gates[j].inputs.filter (fun u => decide (11 ≤ u ∧ u < 11 + j))).flatMap
            (fun u => (u - 11) :: cs.getD (u - 11) []) := by
        rw [hConesEq, hConesLt _ _ j (by rw [hConeStep]; simp [hcsLen]), hConeStep]
        rw [List.getD_append_right _ _ _ _ (by omega), hcsLen, Nat.sub_self]
        rfl
      have hGetW : cs.getD (w - 11) [] = (cones 11 C).getD (w - 11) [] := by
        rw [hConesEq]
        symm
        rw [hConesLt _ _ (w - 11) (by rw [hConeStep]; simp [hcsLen]; omega), hConeStep]
        exact List.getD_append cs _ [] (w - 11) (by omega)
      have hwFilt : w ∈ C.gates[j].inputs.filter (fun u => decide (11 ≤ u ∧ u < 11 + j)) := by
        rw [List.mem_filter]
        exact ⟨by rw [← hGateAtEq C j hj]; exact hw, by simp [hw11, hwLt]⟩
      constructor
      · unfold InCone
        rw [hGetJ, List.mem_flatMap]
        exact ⟨w, hwFilt, by simp⟩
      · intro i hi
        unfold InCone at hi ⊢
        rw [hGetJ, List.mem_flatMap]
        exact ⟨w, hwFilt, List.mem_cons_of_mem _ (by rw [hGetW]; exact hi)⟩
    let in0 : ℕ → ℕ := fun j => (gateAt C j).inputs.getD 0 0
    let in1 : ℕ → ℕ := fun j => (gateAt C j).inputs.getD 1 0
    have hInsEq : ∀ j < C.gates.length, (gateAt C j).inputs = [in0 j, in1 j] := by
      intro j hj
      have hl := hLen2 (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
      simp [in0, in1, hab]
    let andFree : ℕ → Prop := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if hw : w < 11 then True
      else if hlt : w < 11 + C.gates.length then
        (gateAt C (w - 11)).op = GateOp.or ∧
          ih (in0 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have hmem : in0 (w - 11) ∈ (gateAt C (w - 11)).inputs := by rw [hInsEq _ hj]; simp
            have := hRB (w - 11) hj _ hmem; change _ < w; omega) ∧
          ih (in1 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have hmem : in1 (w - 11) ∈ (gateAt C (w - 11)).inputs := by rw [hInsEq _ hj]; simp
            have := hRB (w - 11) hj _ hmem; change _ < w; omega)
      else False
    have hAF_lt11 : ∀ w < 11, andFree w := by
      intro w hw
      dsimp only [andFree]
      rw [WellFounded.fix_eq, dif_pos hw]
      trivial
    have hAF_gate : ∀ j < C.gates.length, andFree (11 + j) ↔
        (gateAt C j).op = GateOp.or ∧ andFree (in0 j) ∧ andFree (in1 j) := by
      intro j hj
      dsimp only [andFree]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
    have hNoAndInCone : ∀ w < 11 + C.gates.length, ¬ andFree w →
        11 ≤ w ∧ ∃ i < C.gates.length, (gateAt C i).op = GateOp.and ∧
          (i = w - 11 ∨ InCone 11 C i (w - 11)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hnaf
        have hw11 : 11 ≤ w := by
          by_contra hlt
          exact hnaf (hAF_lt11 w (by omega))
        refine ⟨hw11, ?_⟩
        let j := w - 11
        have hj : j < C.gates.length := by omega
        have hwj : w = 11 + j := by omega
        rw [hwj] at hnaf
        rcases hMonoOps C hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj) with hop | hop
        · exact ⟨j, hj, hop, Or.inl rfl⟩
        · have hnotboth : ¬ andFree (in0 j) ∨ ¬ andFree (in1 j) := by
            by_contra hboth
            push Not at hboth
            exact hnaf ((hAF_gate j hj).mpr ⟨hop, hboth.1, hboth.2⟩)
          rcases hnotboth with h0 | h1
          · have hlt0 : in0 j < w := by
              have := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp); omega
            obtain ⟨h11, i, hi, hiop, hic⟩ := ih (in0 j) hlt0 (by omega) h0
            obtain ⟨hm1, hm2⟩ := hConeMem j hj (in0 j) (by rw [hInsEq j hj]; simp) h11
            rcases hic with rfl | hic
            · exact ⟨in0 j - 11, hi, hiop, Or.inr hm1⟩
            · exact ⟨i, hi, hiop, Or.inr (hm2 i hic)⟩
          · have hlt1 : in1 j < w := by
              have := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp); omega
            obtain ⟨h11, i, hi, hiop, hic⟩ := ih (in1 j) hlt1 (by omega) h1
            obtain ⟨hm1, hm2⟩ := hConeMem j hj (in1 j) (by rw [hInsEq j hj]; simp) h11
            rcases hic with rfl | hic
            · exact ⟨in1 j - 11, hi, hiop, Or.inr hm1⟩
            · exact ⟨i, hi, hiop, Or.inr (hm2 i hic)⟩
    have hAndChildAF : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        andFree (in0 j) ∧ andFree (in1 j) := by
      intro j hj hop
      have hOne : ∀ w ∈ (gateAt C j).inputs, andFree w := by
        intro w hw
        by_contra hnaf
        have hwLt : w < 11 + j := hRB j hj w hw
        obtain ⟨hw11, i, hi, hiop, hic⟩ := hNoAndInCone w (by omega) hnaf
        obtain ⟨hm1, hm2⟩ := hConeMem j hj w hw hw11
        have hinc : InCone 11 C i j := by
          rcases hic with rfl | hic
          · exact hm1
          · exact hm2 i hic
        have hpos : 0 < andPairs 11 C := by
          unfold andPairs
          refine Finset.card_pos.mpr ⟨(i, j), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨hi, hj⟩, hiop, hop, hinc⟩
        omega
      exact ⟨hOne _ (by rw [hInsEq j hj]; simp), hOne _ (by rw [hInsEq j hj]; simp)⟩
    let orVars : ℕ → Finset (Fin 10) := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h10 : w < 10 then {⟨w, h10⟩}
      else if hw10 : w = 10 then {0, 2}
      else if hlt : w < 11 + C.gates.length then
        if (gateAt C (w - 11)).op = GateOp.or then
          ih (in0 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in0 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega) ∪
          ih (in1 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in1 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega)
        else ∅
      else ∅
    have hOV_lt10 : ∀ (u : Fin 10), orVars u.val = {u} := by
      intro u
      dsimp only [orVars]
      rw [WellFounded.fix_eq, dif_pos u.isLt]
    have hOV_10 : orVars 10 = {0, 2} := by
      dsimp only [orVars]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos rfl]
    have hOV_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        orVars (11 + j) = orVars (in0 j) ∪ orVars (in1 j) := by
      intro j hj hop
      dsimp only [orVars]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
    have hAF_eval : ∀ w < 11 + C.gates.length, andFree w →
        ∀ x : Fin 10 → Bool, (C.wires (inp x)).getD w false = decide (∃ u ∈ orVars w, x u = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf x
        by_cases h10 : w < 10
        · rw [show w = (⟨w, h10⟩ : Fin 10).val from rfl, hOV_lt10]
          change (wF C.gates (inp x)).getD w false = _
          rw [hWFLt _ _ _ (by rw [hInpLen]; omega), hInpGet x ⟨w, h10⟩]
          simp
        · by_cases hw10 : w = 10
          · subst hw10
            rw [hOV_10]
            change (wF C.gates (inp x)).getD 10 false = _
            rw [hWFLt _ _ _ (by rw [hInpLen]; omega), hInp10]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton,
              exists_eq_or_imp, exists_eq_left]
          · let j := w - 11
            have hj : j < C.gates.length := by omega
            have hwj : w = 11 + j := by omega
            rw [hwj] at haf ⊢
            obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
            rw [hOV_or j hj hop]
            rw [show (11 : ℕ) = (inp x).length from (hInpLen x).symm]
            rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
            have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
            have hlt1 : in1 j < 11 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
            have ih0 := ih (in0 j) (by omega) (by omega) haf0 x
            have ih1 := ih (in1 j) (by omega) (by omega) haf1 x
            simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
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
    have hOV_nonempty : ∀ w < 11 + C.gates.length, andFree w → (orVars w).Nonempty := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h10 : w < 10
        · rw [show w = (⟨w, h10⟩ : Fin 10).val from rfl, hOV_lt10]; simp
        · by_cases hw10 : w = 10
          · subst hw10; rw [hOV_10]; simp
          · let j := w - 11
            have hj : j < C.gates.length := by omega
            have hwj : w = 11 + j := by omega
            rw [hwj] at haf ⊢
            obtain ⟨hop, haf0, _⟩ := (hAF_gate j hj).mp haf
            rw [hOV_or j hj hop]
            have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
            exact (ih (in0 j) (by omega) (by omega) haf0).mono Finset.subset_union_left
    have hAF_card_ge_2 : ∀ j < C.gates.length, andFree (11 + j) → 2 ≤ (orVars (11 + j)).card := by
      intro j hj haf
      have hne := hOV_nonempty (11 + j) (by omega) haf
      by_contra hlt
      have hcard1 : (orVars (11 + j)).card = 1 := by
        have := hne.card_pos; omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard1
      have heq : ∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + j) false = (C.wires (inp x)).getD u.val false := by
        intro x
        rw [hAF_eval (11 + j) (by omega) haf x, hu]
        change _ = (wF C.gates (inp x)).getD u.val false
        rw [hWFLt _ _ _ (by rw [hInpLen]; omega), hInpGet x u]
        simp
      obtain ⟨C', hG', hlt'⟩ := hErase C ⟨hM, hRB, hOutLo, hOutHi, hComp⟩ j u.val hj (by omega) (Or.inl heq)
      exact absurd (hMin C' hG') (by omega)
    let topAndsOf : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h11 : w < 11 then ∅
      else if hlt : w < 11 + C.gates.length then
        if (gateAt C (w - 11)).op = GateOp.and then {w - 11}
        else
          ih (in0 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in0 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega) ∪
          ih (in1 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in1 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega)
      else ∅
    let topOrsOf : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h11 : w < 11 then ∅
      else if hlt : w < 11 + C.gates.length then
        if (gateAt C (w - 11)).op = GateOp.and then ∅
        else insert (w - 11) (
          ih (in0 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in0 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega) ∪
          ih (in1 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in1 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega))
      else ∅
    let reachesInp : ℕ → Prop := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h11 : w < 11 then True
      else if hlt : w < 11 + C.gates.length then
        if (gateAt C (w - 11)).op = GateOp.and then False
        else
          ih (in0 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in0 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega) ∨
          ih (in1 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in1 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega)
      else False
    have hRI_lt11 : ∀ w < 11, reachesInp w := by
      intro w hw; dsimp only [reachesInp]; rw [WellFounded.fix_eq, dif_pos hw]; trivial
    have hRI_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ reachesInp (11 + j) := by
      intro j hj hop
      dsimp only [reachesInp]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      simp [hop]
    have hRI_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        (reachesInp (11 + j) ↔ reachesInp (in0 j) ∨ reachesInp (in1 j)) := by
      intro j hj hop
      dsimp only [reachesInp]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
    have hTA_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → topAndsOf (11 + j) = {j} := by
      intro j hj hop
      dsimp only [topAndsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      simp [hop]
    have hTA_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        topAndsOf (11 + j) = topAndsOf (in0 j) ∪ topAndsOf (in1 j) := by
      intro j hj hop
      dsimp only [topAndsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
    have hTO_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → topOrsOf (11 + j) = ∅ := by
      intro j hj hop
      dsimp only [topOrsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      simp [hop]
    have hTO_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        topOrsOf (11 + j) = insert j (topOrsOf (in0 j) ∪ topOrsOf (in1 j)) := by
      intro j hj hop
      dsimp only [topOrsOf]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
    have hRI_single : ∀ w < 11 + C.gates.length, reachesInp w →
        ∃ u : Fin 10, (C.wires (inp (fun v => decide (v = u)))).getD w false = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hri
        by_cases h11 : w < 11
        · obtain ⟨x, hx1, _⟩ := hNoInpEq w h11
          by_cases h10 : w < 10
          · refine ⟨⟨w, h10⟩, ?_⟩
            change (wF C.gates _).getD w false = true
            rw [hWFLt _ _ _ (by rw [hInpLen]; omega), hInpGet _ ⟨w, h10⟩]; simp
          · refine ⟨0, ?_⟩
            have hw10 : w = 10 := by omega
            subst hw10
            change (wF C.gates _).getD 10 false = true
            rw [hWFLt _ _ _ (by rw [hInpLen]; omega), hInp10]; simp
        · let j := w - 11
          have hj : j < C.gates.length := by omega
          have hwj : w = 11 + j := by omega
          rw [hwj] at hri ⊢
          rcases hMonoOps C hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj) with hop | hop
          · exact absurd hri (hRI_and j hj hop)
          · rcases (hRI_or j hj hop).mp hri with h0 | h1
            · have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
              obtain ⟨u, hu⟩ := ih (in0 j) (by omega) (by omega) h0
              refine ⟨u, ?_⟩
              let xu : Fin 10 → Bool := fun v => decide (v = u)
              have hlenu : (inp xu).length = 11 := hInpLen xu
              rw [show (11 : ℕ) = (inp xu).length from hlenu.symm]
              rw [hWireGate C (inp xu) j (by rw [hlenu]; exact hRB) hj, hop, hInsEq j hj]
              simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_eq_true, xu]
              exact Or.inl hu
            · have hlt1 : in1 j < 11 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
              obtain ⟨u, hu⟩ := ih (in1 j) (by omega) (by omega) h1
              refine ⟨u, ?_⟩
              let xu : Fin 10 → Bool := fun v => decide (v = u)
              have hlenu : (inp xu).length = 11 := hInpLen xu
              rw [show (11 : ℕ) = (inp xu).length from hlenu.symm]
              rw [hWireGate C (inp xu) j (by rw [hlenu]; exact hRB) hj, hop, hInsEq j hj]
              simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_eq_true, xu]
              exact Or.inr hu
    have hOutNRI : ¬ reachesInp C.output := by
      intro hri
      obtain ⟨u, hu⟩ := hRI_single C.output hOutHi hri
      have hev : C.eval (inp (fun v => decide (v = u))) = true := hu
      rw [hComp, hFP_single] at hev
      exact Bool.false_ne_true hev
    have hTopProps : ∀ w < 11 + C.gates.length, ¬ reachesInp w →
        (∀ j ∈ topAndsOf w, j < C.gates.length ∧ (gateAt C j).op = GateOp.and) ∧
        (∀ j ∈ topOrsOf w, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ reachesInp (11 + j)) ∧
        (∀ x : Fin 10 → Bool, (C.wires (inp x)).getD w false = true ↔
          ∃ j ∈ topAndsOf w, (C.wires (inp x)).getD (11 + j) false = true) ∧
        (∀ u ∈ topAndsOf w ∪ topOrsOf w, 11 + u = w ∨
          ∃ k ∈ topOrsOf w, 11 + u ∈ (gateAt C k).inputs) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hnri
        have hw11 : 11 ≤ w := by
          by_contra hlt; exact hnri (hRI_lt11 w (by omega))
        let j := w - 11
        have hj : j < C.gates.length := by omega
        have hwj : w = 11 + j := by omega
        rw [hwj] at hnri ⊢
        rcases hMonoOps C hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj) with hop | hop
        · rw [hTA_and j hj hop, hTO_and j hj hop]
          refine ⟨fun k hk => by simp at hk; subst hk; exact ⟨hj, hop⟩,
            fun k hk => by simp at hk,
            fun x => by simp,
            fun u hu => by simp at hu; subst hu; exact Or.inl rfl⟩
        · have hn0 : ¬ reachesInp (in0 j) := fun h => hnri ((hRI_or j hj hop).mpr (Or.inl h))
          have hn1 : ¬ reachesInp (in1 j) := fun h => hnri ((hRI_or j hj hop).mpr (Or.inr h))
          have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
          have hlt1 : in1 j < 11 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
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
            rw [show (11 : ℕ) = (inp x).length from (hInpLen x).symm]
            rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
            simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
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
          have hsub : A ⊆ {C.output - 11} := by
            intro u hu
            rcases hTopParent u (Finset.mem_union_left _ hu) with heq | ⟨k, hk, _⟩
            · simp; omega
            · change k ∈ T at hk; rw [hTe] at hk; simp at hk
          exact (Finset.card_le_card hsub).trans (by simp)
        omega
      · let outG := C.output - 11
        have houtMem : outG ∈ A ∪ T := by
          have hCsz' : C.size = C.gates.length := rfl
          have houtLt : outG < C.gates.length := by omega
          have hCo : C.output = 11 + outG := by omega
          rcases hMonoOps C hM (gateAt C outG) (by rw [hGateAtEq C outG houtLt]; exact List.getElem_mem houtLt) with hop | hop
          · exact Finset.mem_union_left _ (by dsimp only [A]; rw [hCo, hTA_and outG houtLt hop]; simp)
          · exact Finset.mem_union_right _ (by dsimp only [T]; rw [hCo, hTO_or outG houtLt hop]; simp)
        let U := (A ∪ T).erase outG
        let Rset := T.biUnion fun k => ((gateAt C k).inputs.filter (· ≥ 11)).toFinset.image (· - 11)
        have hUR : U ⊆ Rset := by
          intro u hu
          have hune : u ≠ outG := (Finset.mem_erase.mp hu).1
          have hum : u ∈ A ∪ T := (Finset.mem_erase.mp hu).2
          rcases hTopParent u hum with heq | ⟨k, hk, hkin⟩
          · exact absurd (by omega) hune
          · rw [Finset.mem_biUnion]
            refine ⟨k, hk, Finset.mem_image.mpr ⟨11 + u, ?_, by omega⟩⟩
            rw [List.mem_toFinset, List.mem_filter]
            exact ⟨hkin, by simp⟩
        have hRle : Rset.card ≤ 2 * T.card := by
          calc Rset.card ≤ ∑ k ∈ T, (((gateAt C k).inputs.filter (· ≥ 11)).toFinset.image (· - 11)).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ k ∈ T, 2 := by
                apply Finset.sum_le_sum
                intro k hk
                have hkl := (hT_prop k hk).1
                calc (((gateAt C k).inputs.filter (· ≥ 11)).toFinset.image (· - 11)).card
                    ≤ ((gateAt C k).inputs.filter (· ≥ 11)).toFinset.card := Finset.card_image_le
                  _ ≤ ((gateAt C k).inputs.filter (· ≥ 11)).length := List.toFinset_card_le _
                  _ ≤ (gateAt C k).inputs.length := List.length_filter_le _ _
                  _ = 2 := hLen2 (gateAt C k) (by rw [hGateAtEq C k hkl]; exact List.getElem_mem hkl)
            _ = 2 * T.card := by simp [Nat.mul_comm]
        have hUcard : U.card + 1 = A.card + T.card := by
          rw [Finset.card_erase_add_one houtMem, Finset.card_union_of_disjoint hAT_disj]
        have hUle := (Finset.card_le_card hUR).trans hRle
        omega
    have hAndStar : ∀ j ∈ A,
        (∀ u ∈ orVars (in0 j), ∀ v ∈ orVars (in1 j), adj u v = true) ∧
        ((orVars (in0 j)).card = 1 ∨ (orVars (in1 j)).card = 1) := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
      have hlt1 : in1 j < 11 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
      have hadj : ∀ u ∈ orVars (in0 j), ∀ v ∈ orVars (in1 j), adj u v = true := by
        intro u hu v hv
        let x : Fin 10 → Bool := fun w => decide (w = u ∨ w = v)
        have hjT : (C.wires (inp x)).getD (11 + j) false = true := by
          rw [show (11 : ℕ) = (inp x).length from (hInpLen x).symm]
          rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
          simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true,
            hAF_eval (in0 j) (by omega) haf0 x, hAF_eval (in1 j) (by omega) haf1 x, decide_eq_true_eq]
          exact ⟨⟨u, hu, by simp [x]⟩, ⟨v, hv, by simp [x]⟩⟩
        have houtT : C.eval (inp x) = true := (hOutEval x).mpr ⟨j, hjA, hjT⟩
        rw [hComp x, hFP_pair u v] at houtT
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
    let center : ℕ → Fin 10 := fun j =>
      if h : (orVars (in0 j)).Nonempty ∧ (orVars (in0 j)).card = 1 then h.1.choose
      else if h2 : (orVars (in1 j)).Nonempty then h2.choose
      else 0
    let leafWire : ℕ → ℕ := fun j =>
      if (orVars (in0 j)).card = 1 then in1 j else in0 j
    have hStarProp : ∀ j ∈ A,
        andFree (leafWire j) ∧ leafWire j < 11 + C.gates.length ∧
        (∀ v ∈ orVars (leafWire j), adj (center j) v = true) ∧
        (∀ u v : Fin 10,
          (C.wires (inp (fun w => decide (w = u ∨ w = v)))).getD (11 + j) false = true →
          (u = center j ∧ v ∈ orVars (leafWire j)) ∨ (v = center j ∧ u ∈ orVars (leafWire j))) := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
      have hlt1 : in1 j < 11 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
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
        rw [show (11 : ℕ) = (inp _).length from (hInpLen _).symm] at hjT
        rw [hWireGate C _ j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj] at hjT
        simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
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
        rw [show (11 : ℕ) = (inp _).length from (hInpLen _).symm] at hjT
        rw [hWireGate C _ j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj] at hjT
        simp only [hEvalAnd, hEvalOr, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
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
    have hEdgeCov : ∀ u v : Fin 10, adj u v = true →
        ∃ j ∈ A, (u = center j ∧ v ∈ orVars (leafWire j)) ∨ (v = center j ∧ u ∈ orVars (leafWire j)) := by
      intro u v huv
      let x : Fin 10 → Bool := fun w => decide (w = u ∨ w = v)
      have hout : C.eval (inp x) = true := by rw [hComp x, hFP_pair u v, huv]
      obtain ⟨j, hjA, hjT⟩ := (hOutEval x).mp hout
      exact ⟨j, hjA, (hStarProp j hjA).2.2.2 u v hjT⟩
    have hA_ge_6 : 6 ≤ A.card := by
      have hvc : 6 ≤ (A.image center).card := by
        apply hVC6
        intro u v huv
        obtain ⟨j, hjA, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := hEdgeCov u v huv
        · exact Or.inl (Finset.mem_image_of_mem _ hjA)
        · exact Or.inr (Finset.mem_image_of_mem _ hjA)
      exact hvc.trans Finset.card_image_le
    let orCone : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h11 : w < 11 then ∅
      else if hlt : w < 11 + C.gates.length then
        if (gateAt C (w - 11)).op = GateOp.or then
          insert (w - 11) (
            ih (in0 (w - 11)) (by
              have hj : w - 11 < C.gates.length := by omega
              have := hRB (w - 11) hj (in0 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega) ∪
            ih (in1 (w - 11)) (by
              have hj : w - 11 < C.gates.length := by omega
              have := hRB (w - 11) hj (in1 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega))
        else ∅
      else ∅
    let baseIn : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h11 : w < 11 then {w}
      else if hlt : w < 11 + C.gates.length then
        if (gateAt C (w - 11)).op = GateOp.or then
          ih (in0 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in0 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega) ∪
          ih (in1 (w - 11)) (by
            have hj : w - 11 < C.gates.length := by omega
            have := hRB (w - 11) hj (in1 (w - 11)) (by rw [hInsEq _ hj]; simp); change _ < w; omega)
        else ∅
      else ∅
    have hOC_lt11 : ∀ w < 11, orCone w = ∅ := by
      intro w hw; dsimp only [orCone]; rw [WellFounded.fix_eq, dif_pos hw]
    have hOC_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        orCone (11 + j) = insert j (orCone (in0 j) ∪ orCone (in1 j)) := by
      intro j hj hop
      dsimp only [orCone]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
    have hBI_lt11 : ∀ w < 11, baseIn w = {w} := by
      intro w hw; dsimp only [baseIn]; rw [WellFounded.fix_eq, dif_pos hw]
    have hBI_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        baseIn (11 + j) = baseIn (in0 j) ∪ baseIn (in1 j) := by
      intro j hj hop
      dsimp only [baseIn]
      rw [WellFounded.fix_eq, dif_neg (by omega), dif_pos (by omega)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
    have hBotProps : ∀ w < 11 + C.gates.length, andFree w →
        (∀ k ∈ orCone w, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
          andFree (11 + k) ∧ orVars (11 + k) ⊆ orVars w) ∧
        (∀ i ∈ baseIn w, i < 11) ∧
        (orVars w = (baseIn w).biUnion fun i => orVars i) ∧
        (w ∈ baseIn w ∪ (orCone w).image (· + 11)) ∧
        (∀ u ∈ baseIn w ∪ (orCone w).image (· + 11), u = w ∨
          ∃ k ∈ orCone w, u ∈ (gateAt C k).inputs) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h11 : w < 11
        · rw [hOC_lt11 w h11, hBI_lt11 w h11]
          refine ⟨fun k hk => by simp at hk, fun i hi => by simp at hi; omega,
            by simp, by simp, fun u hu => by simp at hu; exact Or.inl hu⟩
        · let j := w - 11
          have hj : j < C.gates.length := by omega
          have hwj : w = 11 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
          have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
          have hlt1 : in1 j < 11 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
          obtain ⟨hC0, hB0, hV0, hM0, hP0⟩ := ih (in0 j) (by omega) (by omega) haf0
          obtain ⟨hC1, hB1, hV1, hM1, hP1⟩ := ih (in1 j) (by omega) (by omega) haf1
          rw [hOC_or j hj hop, hBI_or j hj hop, hOV_or j hj hop]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro k hk
            rcases Finset.mem_insert.mp hk with rfl | h
            · exact ⟨hj, hop, haf, by rw [hOV_or j hj hop]⟩
            · rcases Finset.mem_union.mp h with h | h
              · obtain ⟨a, b, c, d⟩ := hC0 k h
                exact ⟨a, b, c, d.trans Finset.subset_union_left⟩
              · obtain ⟨a, b, c, d⟩ := hC1 k h
                exact ⟨a, b, c, d.trans Finset.subset_union_right⟩
          · intro i hi
            rcases Finset.mem_union.mp hi with h | h
            · exact hB0 i h
            · exact hB1 i h
          · rw [Finset.union_biUnion, ← hV0, ← hV1]
          · apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨j, Finset.mem_insert_self _ _, by omega⟩
          · intro u hu
            by_cases huj : u = 11 + j
            · exact Or.inl huj
            · right
              have hu01 : u ∈ baseIn (in0 j) ∪ (orCone (in0 j)).image (· + 11) ∨
                  u ∈ baseIn (in1 j) ∪ (orCone (in1 j)).image (· + 11) := by
                simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert] at hu ⊢
                rcases hu with (h | h) | ⟨k, rfl | h | h, rfl⟩
                · exact Or.inl (Or.inl h)
                · exact Or.inr (Or.inl h)
                · exact absurd (by omega) huj
                · exact Or.inl (Or.inr ⟨k, h, rfl⟩)
                · exact Or.inr (Or.inr ⟨k, h, rfl⟩)
              rcases hu01 with h0 | h1
              · rcases hP0 u h0 with rfl | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
              · rcases hP1 u h1 with rfl | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
    let Ac : Fin 10 → Finset ℕ := fun c => A.filter (fun j => center j = c)
    let Bc : Fin 10 → Finset ℕ := fun c => (Ac c).biUnion (fun j => orCone (leafWire j))
    let Ec : Fin 10 → Finset (Fin 10) := fun c => (Ac c).biUnion (fun j => orVars (leafWire j))
    let Ic : Fin 10 → Finset ℕ := fun c => (Ac c).biUnion (fun j => baseIn (leafWire j))
    have hBc_disj : ∀ c1 c2 : Fin 10, c1 ≠ c2 → Disjoint (Bc c1) (Bc c2) := by
      intro c1 c2 hne
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨j1, hj1, hk1'⟩ := Finset.mem_biUnion.mp hk1
      obtain ⟨j2, hj2, hk2'⟩ := Finset.mem_biUnion.mp hk2
      have hj1A := (Finset.mem_filter.mp hj1).1
      have hc1 := (Finset.mem_filter.mp hj1).2
      have hj2A := (Finset.mem_filter.mp hj2).1
      have hc2 := (Finset.mem_filter.mp hj2).2
      obtain ⟨haf1, hlt1, hadj1, _⟩ := hStarProp j1 hj1A
      obtain ⟨haf2, hlt2, hadj2, _⟩ := hStarProp j2 hj2A
      obtain ⟨hklt, _, hkaf, hsub1⟩ := (hBotProps (leafWire j1) hlt1 haf1).1 k hk1'
      obtain ⟨_, _, _, hsub2⟩ := (hBotProps (leafWire j2) hlt2 haf2).1 k hk2'
      have hcard2 := hAF_card_ge_2 k hklt hkaf
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (11 + k)).card)
      exact hNoC4 c1 c2 v1 v2 hne hvne
        (hc1 ▸ hadj1 v1 (hsub1 hv1)) (hc1 ▸ hadj1 v2 (hsub1 hv2))
        (hc2 ▸ hadj2 v1 (hsub2 hv1)) (hc2 ▸ hadj2 v2 (hsub2 hv2))
    have hAF_reachesInp : ∀ w < 11 + C.gates.length, andFree w → reachesInp w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h11 : w < 11
        · exact hRI_lt11 w h11
        · let j := w - 11
          have hj : j < C.gates.length := by omega
          have hwj : w = 11 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, _⟩ := (hAF_gate j hj).mp haf
          have hlt0 : in0 j < 11 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
          exact (hRI_or j hj hop).mpr (Or.inl (ih (in0 j) (by omega) (by omega) haf0))
    let Ball := Finset.univ.biUnion Bc
    have hBall_sub : Ball ⊆ Finset.range C.gates.length := by
      intro k hk
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hkc
      obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
      exact Finset.mem_range.mpr ((hBotProps (leafWire j) hlt haf).1 k hkj).1
    have hBall_disj_A : Disjoint Ball A := by
      rw [Finset.disjoint_left]
      intro k hkB hkA
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hkB
      obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hkc
      obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
      have h1 := ((hBotProps (leafWire j) hlt haf).1 k hkj).2.1
      have h2 := (hA_prop k hkA).2
      rw [h1] at h2
      exact GateOp.noConfusion h2
    have hBall_disj_T : Disjoint Ball T := by
      rw [Finset.disjoint_left]
      intro k hkB hkT
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hkB
      obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hkc
      obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
      obtain ⟨hklt, _, hkaf, _⟩ := (hBotProps (leafWire j) hlt haf).1 k hkj
      exact (hT_prop k hkT).2.2 (hAF_reachesInp (11 + k) (by omega) hkaf)
    have hIc_bound : ∀ c : Fin 10, (Ic c).card ≤ (Bc c).card + (Ac c).card := by
      intro c
      let Gc := (Bc c).image (· + 11)
      let Rc := (Ac c).image leafWire
      have hDisjIG : Disjoint (Ic c) Gc := by
        rw [Finset.disjoint_left]
        intro w hwI hwG
        obtain ⟨j, hj, hwi⟩ := Finset.mem_biUnion.mp hwI
        obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
        have hw11 := (hBotProps (leafWire j) hlt haf).2.1 w hwi
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hwG
        omega
      have hReadSub : (Ic c ∪ Gc) \ Rc ⊆ (Bc c).biUnion fun k => (gateAt C k).inputs.toFinset := by
        intro u hu
        have hunR : u ∉ Rc := (Finset.mem_sdiff.mp hu).2
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hu).1 with huI | huG
        · obtain ⟨j, hj, huij⟩ := Finset.mem_biUnion.mp huI
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
          rcases (hBotProps (leafWire j) hlt haf).2.2.2.2 u (Finset.mem_union_left _ huij) with rfl | ⟨k, hk, hkin⟩
          · exact absurd (Finset.mem_image_of_mem _ hj) hunR
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_biUnion.mpr ⟨j, hj, hk⟩, List.mem_toFinset.mpr hkin⟩
        · obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp huG
          obtain ⟨j, hj, hk0j⟩ := Finset.mem_biUnion.mp hk0
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
          rcases (hBotProps (leafWire j) hlt haf).2.2.2.2 (k0 + 11)
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k0, hk0j, rfl⟩)) with heq | ⟨k, hk, hkin⟩
          · exact absurd (heq ▸ Finset.mem_image_of_mem _ hj) hunR
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_biUnion.mpr ⟨j, hj, hk⟩, List.mem_toFinset.mpr hkin⟩
      have hReadCard : ((Bc c).biUnion fun k => (gateAt C k).inputs.toFinset).card ≤ 2 * (Bc c).card := by
        calc ((Bc c).biUnion fun k => (gateAt C k).inputs.toFinset).card
            ≤ ∑ k ∈ Bc c, (gateAt C k).inputs.toFinset.card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ Bc c, 2 := by
              apply Finset.sum_le_sum
              intro k hk
              obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk
              obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
              have hklt := ((hBotProps (leafWire j) hlt haf).1 k hkj).1
              exact (List.toFinset_card_le _).trans (le_of_eq (hLen2 (gateAt C k) (by rw [hGateAtEq C k hklt]; exact List.getElem_mem hklt)))
          _ = 2 * (Bc c).card := by simp [Nat.mul_comm]
      have hGcCard : Gc.card = (Bc c).card :=
        Finset.card_image_of_injective _ (fun a b h => by omega)
      have hRcLe : Rc.card ≤ (Ac c).card := Finset.card_image_le
      have hSdiff : (Ic c ∪ Gc).card - Rc.card ≤ ((Ic c ∪ Gc) \ Rc).card := Finset.le_card_sdiff _ _
      have hUnion : (Ic c ∪ Gc).card = (Ic c).card + (Bc c).card := by
        rw [Finset.card_union_of_disjoint hDisjIG, hGcCard]
      have hStep := hSdiff.trans ((Finset.card_le_card hReadSub).trans hReadCard)
      omega
    have hEc_bound : ∀ c : Fin 10, (Ec c).card ≤ (Ic c).card + (if c = 1 then 1 else 0) := by
      intro c
      have hEcEq : Ec c = (Ic c).biUnion orVars := by
        ext v
        simp only [Ec, Ic, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hj, hv⟩
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
          rw [(hBotProps (leafWire j) hlt haf).2.2.1] at hv
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
          exact ⟨i, ⟨j, hj, hi⟩, hvi⟩
        · rintro ⟨i, ⟨j, hj, hi⟩, hvi⟩
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
          exact ⟨j, hj, by rw [(hBotProps (leafWire j) hlt haf).2.2.1]; exact Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩⟩
      rw [hEcEq]
      have hNo10 : c ≠ 1 → 10 ∉ Ic c := by
        intro hc1 h10
        obtain ⟨j, hj, h10j⟩ := Finset.mem_biUnion.mp h10
        have hjA := (Finset.mem_filter.mp hj).1
        have hcj := (Finset.mem_filter.mp hj).2
        obtain ⟨haf, hlt, hadj, _⟩ := hStarProp j hjA
        have hsub : orVars 10 ⊆ orVars (leafWire j) := by
          rw [(hBotProps (leafWire j) hlt haf).2.2.1]
          exact Finset.subset_biUnion_of_mem _ h10j
        have h0 : (0 : Fin 10) ∈ orVars (leafWire j) := hsub (by rw [hOV_10]; simp)
        have h2 : (2 : Fin 10) ∈ orVars (leafWire j) := hsub (by rw [hOV_10]; simp)
        exact hc1 (hCommon02 c (hcj ▸ hadj 0 h0) (hcj ▸ hadj 2 h2))
      have hSum : ((Ic c).biUnion orVars).card ≤ ∑ i ∈ Ic c, (orVars i).card := Finset.card_biUnion_le
      have hCardI : ∀ i ∈ Ic c, (orVars i).card = if i = 10 then 2 else 1 := by
        intro i hi
        obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨haf, hlt, _, _⟩ := hStarProp j (Finset.mem_filter.mp hj).1
        have hi11 := (hBotProps (leafWire j) hlt haf).2.1 i hij
        by_cases h10 : i = 10
        · subst h10; rw [if_pos rfl, hOV_10]; decide
        · rw [if_neg h10, show i = (⟨i, by omega⟩ : Fin 10).val from rfl, hOV_lt10]; simp
      calc ((Ic c).biUnion orVars).card
          ≤ ∑ i ∈ Ic c, (orVars i).card := hSum
        _ = ∑ i ∈ Ic c, (if i = 10 then 2 else 1) := Finset.sum_congr rfl hCardI
        _ = ∑ i ∈ Ic c, (1 + if i = 10 then 1 else 0) := by
            apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
        _ = (Ic c).card + ∑ i ∈ Ic c, (if i = 10 then 1 else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ (Ic c).card + (if c = 1 then 1 else 0) := by
            apply Nat.add_le_add_left
            by_cases hc1 : c = 1
            · rw [if_pos hc1, Finset.sum_ite_eq']
              split_ifs <;> omega
            · rw [if_neg hc1, Finset.sum_ite_eq', if_neg (hNo10 hc1)]
    have hSumEc : 15 ≤ ∑ c : Fin 10, (Ec c).card := by
      let Edges := Finset.univ.filter fun p : Fin 10 × Fin 10 => p.1 < p.2 ∧ adj p.1 p.2 = true
      have hEdgesEq : Edges.card = 15 := by convert hEdgesCard
      let Cov := Finset.univ.sigma Ec
      have hCovCard : Cov.card = ∑ c : Fin 10, (Ec c).card := by simp [Cov]
      let toEdge : (Σ _ : Fin 10, Fin 10) → Fin 10 × Fin 10 := fun s =>
        if s.1 < s.2 then (s.1, s.2) else (s.2, s.1)
      have hSub : Edges ⊆ Cov.image toEdge := by
        intro p hp
        obtain ⟨hlt, huv⟩ := (Finset.mem_filter.mp hp).2
        obtain ⟨j, hjA, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hEdgeCov p.1 p.2 huv
        · apply Finset.mem_image.mpr
          refine ⟨⟨p.1, p.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjA, h1.symm⟩, h2⟩
          · simp [toEdge, hlt]
        · apply Finset.mem_image.mpr
          refine ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjA, h1.symm⟩, h2⟩
          · have hnot : ¬ (p.2 < p.1) := not_lt.mpr (le_of_lt hlt)
            simp [toEdge, hnot]
      rw [← hCovCard, ← hEdgesEq]
      exact (Finset.card_le_card hSub).trans Finset.card_image_le
    have hSumAc : ∑ c : Fin 10, (Ac c).card = A.card := by
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
    have hSumBc : ∑ c : Fin 10, (Bc c).card = Ball.card := by
      rw [Finset.card_biUnion]
      intro c1 _ c2 _ hne
      exact hBc_disj c1 c2 hne
    have hStep1 : 15 ≤ Ball.card + A.card + 1 := by
      calc 15 ≤ ∑ c : Fin 10, (Ec c).card := hSumEc
        _ ≤ ∑ c : Fin 10, ((Ic c).card + (if c = 1 then 1 else 0)) :=
            Finset.sum_le_sum fun c _ => hEc_bound c
        _ = (∑ c : Fin 10, (Ic c).card) + 1 := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
            simp
        _ ≤ (∑ c : Fin 10, ((Bc c).card + (Ac c).card)) + 1 := by
            apply Nat.add_le_add_right
            exact Finset.sum_le_sum fun c _ => hIc_bound c
        _ = Ball.card + A.card + 1 := by
            rw [Finset.sum_add_distrib, hSumBc, hSumAc]
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
  · by_cases hAP1 : andPairs 11 C = 1
    · obtain ⟨x, hx⟩ := h_one C hAO2 hDist hSzLe hOutLo hOutHi hAP1 hTopForm
      exact hx (hComp x)
    · have hAP2 : 2 ≤ andPairs 11 C := by omega
      obtain ⟨x, hx⟩ := h_ge_two C hAO2 hDist hSzLe hOutLo hOutHi hAP2 hTopForm
      exact hx (hComp x)
