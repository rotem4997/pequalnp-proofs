import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Gate erasure is proved below using the index-shift construction of L-meta-7295.
-- The remaining two cases distinguish a single lost minimal edge from two lost edges.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8145_314
    (punctured :
      let d : Finset (Fin 13) := {0,1,3,9}
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, p-l ∈ d ∧
        x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
      let edge := fun (p l : Fin 13) (v : Fin 26) =>
        decide (v=Fin.castAdd 13 p ∨ v=Fin.natAdd 13 l)
      ∀ (p0 l0 : Fin 13) (D : Circuit), p0-l0 ∈ d → Monotone2 D → ReadsBack 26 D →
        D.eval (List.ofFn (edge p0 l0))=false →
        (∀ x : Fin 26 → Bool, D.eval (List.ofFn x)=true → F x) →
        (∀ p l : Fin 13, p-l ∈ d → (p≠p0 ∨ l≠l0) → D.eval (List.ofFn (edge p l))=true) →
        63 ≤ D.size)
    (multiple :
      let d : Finset (Fin 13) := {0,1,3,9}
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, p-l ∈ d ∧
        x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
      let good := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧
        ∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ F x
      let edge := fun (p l : Fin 13) (v : Fin 26) =>
        decide (v=Fin.castAdd 13 p ∨ v=Fin.natAdd 13 l)
      let two := fun v : Fin 26 => decide (v=0 ∨ v=1)
      ∀ (C : Circuit), good C → (∀ A : Circuit, good A → C.size ≤ A.size) →
        ∀ i : Fin C.gates.length, (C.gates.get i).op = .and →
        (C.wires (List.ofFn two)).getD (26+i.val) false = true →
        let cut : Circuit := ⟨C.gates.set i.val ⟨.or,[]⟩,C.output⟩
        let lost := fun e : Fin 13 × Fin 13 =>
          e.1-e.2 ∈ d ∧ cut.eval (List.ofFn (edge e.1 e.2)) = false
        (∃ u v : Fin 13 × Fin 13, u ≠ v ∧ lost u ∧ lost v) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) => ∃ (x8 : Fin x5.gates.length), (x5.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5.wires (List.ofFn (x4 x6 x7))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 → x6.size ≤ x8.size) → x5 x6 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ)) → (64 : ℕ) ≤ x6.size := by
  classical
  let wireStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
      (gs.foldl wireStep acc).length = acc.length + gs.length := by
    induction gs generalizing acc with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
      (gs.foldl wireStep acc).getD w false = acc.getD w false := by
    induction gs generalizing acc with
    | nil => rfl
    | cons g gs ih =>
      have hw' : w < (wireStep acc g).length := by
        simp only [wireStep, List.length_append, List.length_singleton]
        omega
      rw [List.foldl_cons, ih (wireStep acc g) hw']
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp only [wireStep, List.getElem?_append_left hw]
  have gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
      gateAt C k = C.gates[k] := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  have wires_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
      (C.wires x).getD w false = x.getD w false :=
    foldl_wireStep_prefix C.gates x w hw
  have wires_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (k : ℕ)
      (hk : k < C.gates.length) (hRB : ReadsBack n C) :
      (C.wires x).getD (n + k) false =
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => (C.wires x).getD u false) := by
    have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k C.gates
      have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
      rw [h2] at h1
      simp only [List.append_assoc, List.singleton_append, h1]
    set acc := (C.gates.take k).foldl wireStep x with hacc
    have hacc_len : acc.length = n + k := by
      rw [hacc, foldl_wireStep_length, hx, List.length_take]
      omega
    have hpref : ∀ u < n + k, (C.wires x).getD u false = acc.getD u false := by
      intro u hu
      change (C.gates.foldl wireStep x).getD u false = acc.getD u false
      conv_lhs => rw [← List.take_append_drop k C.gates]
      rw [List.foldl_append, ← hacc]
      exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
    have hval : (C.wires x).getD (n + k) false =
        C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
      change (C.gates.foldl wireStep x).getD (n + k) false = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
      have hlen : n + k < (wireStep acc C.gates[k]).length := by
        simp only [wireStep, List.length_append, List.length_singleton]
        omega
      rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
      rw [List.getD_eq_getElem?_getD]
      simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
        hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rw [hval, gateAt_eq_getElem C k hk]
    congr 1
    apply List.map_congr_left
    intro u hu
    rw [← gateAt_eq_getElem C k hk] at hu
    exact (hpref u (hRB k hk u hu)).symm
  have monotone2_op_or (C : Circuit) (hM : Monotone2 C) (g : Gate) (hg : g ∈ C.gates) :
      g.op = GateOp.and ∨ g.op = GateOp.or := by
    have h := (hM g hg).1
    simpa using h
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l1 l2 : List Bool) (hlen : l1.length = l2.length)
      (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
      op.eval l1 = true → op.eval l2 = true := by
    rcases hop with rfl | rfl
    · intro h1
      simp only [andEval, orEval, List.all_eq_true, id_eq] at h1 ⊢
      intro b hb
      rw [List.mem_iff_getElem] at hb
      obtain ⟨p, hp2, rfl⟩ := hb
      have hp1 : p < l1.length := by omega
      exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
    · intro h1
      simp only [andEval, orEval, List.any_eq_true, id_eq] at h1 ⊢
      obtain ⟨b, hb, rfl⟩ := h1
      rw [List.mem_iff_getElem] at hb
      obtain ⟨p, hp1, hbp⟩ := hb
      have hp2 : p < l2.length := by omega
      exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩
  let shiftW (n k w : ℕ) : ℕ :=
    if w < n + k then w else w - 1
  let unshiftW (n k w : ℕ) : ℕ :=
    if w < n + k then w else w + 1
  let unshiftG (k j : ℕ) : ℕ :=
    if j < k then j else j + 1
  have unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
      unshiftW n k (shiftW n k w) = w := by
    unfold unshiftW shiftW
    split_ifs <;> omega
  let constGate (b : Bool) : Gate :=
    if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩
  let isAbsorbOp (b : Bool) (op : GateOp) : Bool :=
    if b then decide (op = GateOp.or) else decide (op = GateOp.and)
  let rewriteGateConst (n k : ℕ) (b : Bool) (g : Gate) : Gate :=
    if n + k ∈ g.inputs then
      if isAbsorbOp b g.op then constGate b
      else ⟨g.op, (g.inputs.filter (fun w => decide (w ≠ n + k))).map (shiftW n k)⟩
    else
      ⟨g.op, g.inputs.map (shiftW n k)⟩
  let elimConst (n k : ℕ) (b : Bool) (C : Circuit) : Circuit :=
    ⟨(C.gates.eraseIdx k).map (rewriteGateConst n k b), shiftW n k C.output⟩
  have elimConst_length (n k : ℕ) (b : Bool) (C : Circuit) (hk : k < C.gates.length) :
      (elimConst n k b C).gates.length = C.gates.length - 1 := by
    simp [elimConst, List.length_eraseIdx_of_lt hk]
  have elimConst_gateAt (n k : ℕ) (b : Bool) (C : Circuit) (hk : k < C.gates.length)
      (j : ℕ) (hj : j < (elimConst n k b C).gates.length) :
      gateAt (elimConst n k b C) j = rewriteGateConst n k b (gateAt C (unshiftG k j)) := by
    have hj_lt : j < C.gates.length - 1 := by
      rw [← elimConst_length n k b C hk]; exact hj
    have hj_e : j < (C.gates.eraseIdx k).length := by
      rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
    rw [gateAt_eq_getElem (elimConst n k b C) j hj]
    simp only [elimConst, List.getElem_map, unshiftG]
    split_ifs with hjk
    · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq_getElem C j (by omega)]
    · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq_getElem C (j + 1) (by omega)]
  have elimConst_monotone2 (n k : ℕ) (b : Bool) (C : Circuit) (hM : Monotone2 C) :
      Monotone2 (elimConst n k b C) := by
    intro g hg
    simp only [elimConst, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have h0 := hM g0 (List.mem_of_mem_eraseIdx hg0)
    unfold rewriteGateConst
    split_ifs with hmem habs
    · cases b <;> simp [constGate]
    · refine ⟨h0.1, ?_⟩
      simp only [List.length_map]
      exact (List.length_filter_le _ _).trans h0.2
    · exact ⟨h0.1, by simp [h0.2]⟩
  have elimConst_readsBack (n k : ℕ) (b : Bool) (C : Circuit) (hRB : ReadsBack n C)
      (hk : k < C.gates.length) :
      ReadsBack n (elimConst n k b C) := by
    intro j hj w' hw'
    rw [elimConst_gateAt n k b C hk j hj] at hw'
    have hj_lt : j < C.gates.length - 1 := by
      rw [← elimConst_length n k b C hk]; exact hj
    have hj0_lt : unshiftG k j < C.gates.length := by
      unfold unshiftG; split_ifs <;> omega
    unfold rewriteGateConst at hw'
    split_ifs at hw' with hmem habs
    · cases b <;> simp [constGate] at hw'
    · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw'
      obtain ⟨w, ⟨hw_in, hw_ne⟩, rfl⟩ := hw'
      have hw_lt := hRB (unshiftG k j) hj0_lt w hw_in
      unfold shiftW
      unfold unshiftG at hw_lt
      split_ifs at hw_lt ⊢ <;> omega
    · simp only [List.mem_map] at hw'
      obtain ⟨w, hw_in, rfl⟩ := hw'
      have hw_lt := hRB (unshiftG k j) hj0_lt w hw_in
      have hw_ne : w ≠ n + k := fun heq => hmem (heq ▸ hw_in)
      unfold shiftW
      unfold unshiftG at hw_lt
      split_ifs at hw_lt ⊢ <;> omega
  have elimConst_wires_eq (n k : ℕ) (b : Bool) (C : Circuit) (x : List Bool) (hx : x.length = n)
      (hM : Monotone2 C) (hRB : ReadsBack n C) (hk : k < C.gates.length)
      (hval_k : (C.wires x).getD (n + k) false = b) :
      ∀ w < n + (elimConst n k b C).gates.length,
        ((elimConst n k b C).wires x).getD w false = (C.wires x).getD (unshiftW n k w) false := by
    have hRB' : ReadsBack n (elimConst n k b C) := elimConst_readsBack n k b C hRB hk
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw, wires_input _ x w (by omega), wires_input _ x w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (elimConst n k b C).gates.length := by omega
        have hlen' : (elimConst n k b C).gates.length = C.gates.length - 1 :=
          elimConst_length n k b C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [wires_gate n (elimConst n k b C) x hx j hj_lt hRB']
        rw [wires_gate n C x hx (unshiftG k j) hj0_lt hRB]
        rw [elimConst_gateAt n k b C hk j hj_lt]
        set g := gateAt C (unshiftG k j) with hg_def
        have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
          rw [hg_def, gateAt_eq_getElem C (unshiftG k j) hj0_lt]
          exact monotone2_op_or C hM C.gates[unshiftG k j] (List.getElem_mem hj0_lt)
        unfold rewriteGateConst
        split_ifs with hmem habs
        · rcases b with _ | _ <;> rcases hg_op with hop | hop
          · simp [constGate, hop, andEval, orEval]
            exact ⟨n + k, hmem, hval_k⟩
          · simp [isAbsorbOp, hop] at habs
          · simp [isAbsorbOp, hop] at habs
          · simp [constGate, hop, andEval, orEval]
            exact ⟨n + k, hmem, hval_k⟩
        · have hmap : ((g.inputs.filter (fun u => decide (u ≠ n + k))).map (shiftW n k)).map
              (fun u' => ((elimConst n k b C).wires x).getD u' false) =
              (g.inputs.filter (fun u => decide (u ≠ n + k))).map
              (fun u => (C.wires x).getD u false) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro u hu
            rw [List.mem_filter] at hu
            have hu_ne : u ≠ n + k := by simpa using hu.2
            have hsu_lt : shiftW n k u < n + j := by
              have hmem' : shiftW n k u ∈ (gateAt (elimConst n k b C) j).inputs := by
                rw [elimConst_gateAt n k b C hk j hj_lt]
                change shiftW n k u ∈ (rewriteGateConst n k b g).inputs
                unfold rewriteGateConst
                simp only [hmem, habs, ↓reduceIte, Bool.false_eq_true, List.mem_map, List.mem_filter,
                  decide_eq_true_eq]
                exact ⟨u, ⟨hu.1, hu_ne⟩, rfl⟩
              exact hRB' j hj_lt (shiftW n k u) hmem'
            simp only [Function.comp_apply]
            rw [ih (shiftW n k u) (by omega) (by omega), unshiftW_shiftW n k u hu_ne]
          rw [hmap]
          rcases b with _ | _ <;> rcases hg_op with hop | hop
          · simp [isAbsorbOp, hop] at habs
          · rw [hop]
            rw [Bool.eq_iff_iff]
            simp only [andEval, orEval, List.any_eq_true, List.mem_map,
              List.mem_filter, decide_eq_true_eq, id_eq]
            constructor
            · rintro ⟨_, ⟨u, ⟨hu_in, _⟩, rfl⟩, hu_t⟩
              exact ⟨_, ⟨u, hu_in, rfl⟩, hu_t⟩
            · rintro ⟨_, ⟨u, hu_in, rfl⟩, hu_t⟩
              have hu_ne : u ≠ n + k := by
                intro hEq; rw [hEq, hval_k] at hu_t; cases hu_t
              exact ⟨_, ⟨u, ⟨hu_in, hu_ne⟩, rfl⟩, hu_t⟩
          · rw [hop]
            rw [Bool.eq_iff_iff]
            simp only [andEval, orEval, List.all_eq_true, List.mem_map,
              List.mem_filter, decide_eq_true_eq, id_eq]
            constructor
            · rintro hall _ ⟨u, hu_in, rfl⟩
              by_cases hu_ne : u = n + k
              · rw [hu_ne, hval_k]
              · exact hall _ ⟨u, ⟨hu_in, hu_ne⟩, rfl⟩
            · rintro hall _ ⟨u, ⟨hu_in, _⟩, rfl⟩
              exact hall _ ⟨u, hu_in, rfl⟩
          · simp [isAbsorbOp, hop] at habs
        · simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hu_ne : u ≠ n + k := fun heq => hmem (heq ▸ hu)
          have hsu_lt : shiftW n k u < n + j := by
            have hmem' : shiftW n k u ∈ (gateAt (elimConst n k b C) j).inputs := by
              rw [elimConst_gateAt n k b C hk j hj_lt]
              change shiftW n k u ∈ (rewriteGateConst n k b g).inputs
              unfold rewriteGateConst
              simp only [hmem, ↓reduceIte, List.mem_map]
              exact ⟨u, hu, rfl⟩
            exact hRB' j hj_lt (shiftW n k u) hmem'
          simp only [Function.comp_apply]
          rw [ih (shiftW n k u) (by omega) (by omega), unshiftW_shiftW n k u hu_ne]
  have elimConst_eval_eq (n k : ℕ) (b : Bool) (C : Circuit) (x : List Bool) (hx : x.length = n)
      (hM : Monotone2 C) (hRB : ReadsBack n C) (hk : k < C.gates.length)
      (hout : C.output < n + C.gates.length) (hout_ne : C.output ≠ n + k)
      (hval_k : (C.wires x).getD (n + k) false = b) :
      (elimConst n k b C).eval x = C.eval x := by
    unfold Circuit.eval
    have hlen' := elimConst_length n k b C hk
    have hout' : (elimConst n k b C).output < n + (elimConst n k b C).gates.length := by
      rw [hlen']
      simp only [elimConst, shiftW]
      split_ifs <;> omega
    rw [elimConst_wires_eq n k b C x hx hM hRB hk hval_k (elimConst n k b C).output hout']
    simp only [elimConst, unshiftW_shiftW n k C.output hout_ne]
  let bit (C : Circuit) (x : List Bool) (w : ℕ) := (C.wires x).getD w false
  let off (C : Circuit) (k : ℕ) : Circuit := ⟨C.gates.set k (constGate false),C.output⟩
  have len (C : Circuit) (k : ℕ) : (off C k).gates.length = C.gates.length := by simp [off]
  have shape (C : Circuit) (k j : ℕ) (hj : j<C.gates.length) :
      gateAt (off C k) j = if k=j then constGate false else gateAt C j := by
    rw [gateAt_eq_getElem _ _ (by simpa only [len] using hj),gateAt_eq_getElem _ _ hj]
    simp [off,List.getElem_set]
  have off_legal (C : Circuit) (k : ℕ) (m : Monotone2 C) : Monotone2 (off C k) := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    rw [←gateAt_eq_getElem _ _ hj,shape C k j (by simpa only [len] using hj)]
    split
    · simp [constGate]
    · rw [gateAt_eq_getElem _ _ (by simpa only [len] using hj)]
      exact m _ (List.getElem_mem _)
  have off_back (n : ℕ) (C : Circuit) (k : ℕ) (rb : ReadsBack n C) : ReadsBack n (off C k) := by
    intro j hj r mem
    rw [len] at hj
    rw [shape C k j hj] at mem
    split at mem
    · simp [constGate] at mem
    · exact rb j hj r mem
  have wire_compare (n : ℕ) (C : Circuit) (k : ℕ) (m : Monotone2 C) (rb : ReadsBack n C)
      (x : List Bool) (hx : x.length = n) (R : Bool → Bool → Prop)
      (reflR : ∀ b, R b b) (zero : R false (bit C x (n+k)))
      (gateR : ∀ (g : Gate), g ∈ C.gates → ∀ (a b : ℕ → Bool),
        (∀ r ∈ g.inputs, R (a r) (b r)) →
        R (g.op.eval (g.inputs.map a)) (g.op.eval (g.inputs.map b))) :
      ∀ w < n + C.gates.length, R (bit (off C k) x w) (bit C x w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases input : w < n
      · simp only [bit,wires_input _ x w (by omega)]
        exact reflR _
      · let j := w-n
        have eq : w=n+j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        rw [eq]
        by_cases deleted : k=j
        · subst k
          dsimp only [bit]
          rw [wires_gate n _ x hx j (by simpa only [len] using hj) (off_back n C j rb),
            shape C j j hj,if_pos rfl]
          exact zero
        · simp only [bit,wires_gate n _ x hx j (by simpa only [len] using hj) (off_back n C k rb),
            wires_gate n C x hx j hj rb,shape C k j hj,if_neg deleted]
          apply gateR _ (by rw [gateAt_eq_getElem _ _ hj]; exact List.getElem_mem _)
          intro r hr
          have bound := rb j hj r hr
          exact ih r (by omega) (by omega)
  have erase (n : ℕ) (C : Circuit) (i : Fin C.gates.length) (mono : Monotone2 C)
      (back : ReadsBack n C) (_and : (C.gates.get i).op = .and)
      (out : C.output < n+C.size) (nonOut : C.output ≠ n+i.val) :
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = (off C i.val).eval (List.ofFn x) ∧
          (D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true) ∧
          ((C.wires (List.ofFn x)).getD (n+i.val) false = false →
            D.eval (List.ofFn x) = C.eval (List.ofFn x)) := by
    let B := off C i.val
    let D := elimConst n i.val false B
    have hm := off_legal C i.val mono
    have rb := off_back n C i.val back
    have hi : i.val<B.gates.length := by simpa only [B,len] using i.isLt
    have ho : B.output<n+B.gates.length := by change C.output < n + (off C i.val).gates.length; rw [len]; exact out
    have sz : D.gates.length = C.gates.length-1 := (elimConst_length n _ false B hi).trans (by change (off C i.val).gates.length-1=C.gates.length-1; rw [len])
    refine ⟨D,elimConst_monotone2 _ _ _ B hm,elimConst_readsBack _ _ _ B rb hi,?_,?_⟩
    · change D.gates.length<C.gates.length; have := i.isLt; omega
    intro x
    let z := List.ofFn x
    have zl : z.length=n := List.length_ofFn
    have zero : bit B z (n+i.val) = false := by
      dsimp only [bit]
      rw [wires_gate n B z zl _ hi rb]
      change (gateAt (off C i.val) i.val).op.eval _ = false
      rw [shape C i.val i.val i.isLt,if_pos rfl]
      rfl
    have sim : D.eval z = B.eval z := elimConst_eval_eq n _ false B _ zl hm rb hi ho nonOut zero
    refine ⟨sim,?_⟩
    change (D.eval z = true → C.eval z = true) ∧ (bit C z (n+i.val)=false → D.eval z=C.eval z)
    rw [sim]
    constructor
    · apply wire_compare n C i.val mono back z zl (fun u v => u=true → v=true)
        (fun _ h => h) (by simp) _ C.output out
      intro g hg a b rel on
      apply gateOp_eval_mono _ (monotone2_op_or C mono g hg) _ _ (by simp) _ on
      intro j h1 h2 h
      simp only [List.getElem_map] at h ⊢
      exact rel _ (List.getElem_mem _) h
    · intro h
      apply wire_compare n C i.val mono back z zl Eq (fun _ => rfl) h.symm _ C.output out
      intro g _ a b rel
      rw [List.map_congr_left (fun j hj => rel j hj)]
  dsimp only
  intro C good minimal fired
  obtain ⟨i,op,hit⟩ := fired
  let d : Finset (Fin 13) := {0,1,3,9}
  let two := fun v : Fin 26 => decide (v=0 ∨ v=1)
  let edge := fun (p l : Fin 13) (v : Fin 26) =>
    decide (v=Fin.castAdd 13 p ∨ v=Fin.natAdd 13 l)
  have on (p l : Fin 13) (inc : p-l ∈ d) : C.eval (List.ofFn (edge p l)) = true := by
    apply (good.2.2 _).2
    exact ⟨p,l,inc,by simp [edge],by simp [edge]⟩
  have off : C.eval (List.ofFn two) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨p,l,_,_,line⟩ := (good.2.2 _).1 yes
    have no : ∀ j : Fin 13, two (Fin.natAdd 13 j) = false := by decide +kernel
    exact Bool.noConfusion ((no l).symm.trans line)
  have wire_ne : C.output ≠ 26 + i.val := by
    intro same
    change (C.wires (List.ofFn two)).getD C.output false = false at off
    rw [same] at off
    exact Bool.noConfusion (off.symm.trans hit)
  have size_wires (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun j => a.getD j false)]) w).length =
        w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]; omega
  have within : C.output < 26 + C.size := by
    by_contra! ge
    have yes := on 0 0 (by decide)
    change (C.wires (List.ofFn (edge 0 0))).getD C.output false = true at yes
    have len : (C.wires (List.ofFn (edge 0 0))).length = 26 + C.size := by
      unfold Circuit.wires; rw [size_wires, List.length_ofFn]; rfl
    rw [List.getD_eq_default _ _ (len ▸ ge)] at yes
    contradiction
  obtain ⟨D,hm,hr,sm,sim⟩ := erase 26 C i good.1 good.2.1 op within wire_ne
  have sound (x : Fin 26 → Bool) (h : D.eval (List.ofFn x) = true) := (good.2.2 x).1 ((sim x).2.1 h)
  by_cases first : ∃ p l : Fin 13, p-l ∈ d ∧ D.eval (List.ofFn (edge p l))=false
  · obtain ⟨p,l,ep,loss⟩ := first
    by_cases more : ∃ q m : Fin 13, q-m ∈ d ∧ (p≠q ∨ l≠m) ∧ D.eval (List.ofFn (edge q m))=false
    · obtain ⟨q,m,eq,ne,loss2⟩ := more
      apply multiple C good minimal i op hit
      refine ⟨(p,l),(q,m),?_,⟨ep,((sim _).1).symm.trans loss⟩,⟨eq,((sim _).1).symm.trans loss2⟩⟩
      intro pairEq
      rcases ne with hp|hl
      · exact hp (congrArg Prod.fst pairEq)
      · exact hl (congrArg Prod.snd pairEq)
    · have bound := punctured p l D ep hm hr loss sound (by
        intro q m eq ne
        cases h : D.eval (List.ofFn (edge q m)) with
        | true => rfl
        | false => exact (more ⟨q,m,eq,ne.imp Ne.symm Ne.symm,h⟩).elim)
      omega
  · have allOn (p l : Fin 13) (e : p-l ∈ d) : D.eval (List.ofFn (edge p l))=true := by
      cases v : D.eval (List.ofFn (edge p l)) with
      | true => rfl
      | false => exact (first ⟨p,l,e,v⟩).elim
    have getD_append_singleton_lt (l : List Bool) (v dflt : Bool) {i : ℕ} (h : i < l.length) :
        (l ++ [v]).getD i dflt = l.getD i dflt := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

    have getD_append_singleton_eq (l : List Bool) (v dflt : Bool) :
        (l ++ [v]).getD l.length dflt = v := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
      simp

    have getD_append_singleton_gt (l : List Bool) (v dflt : Bool) {i : ℕ} (h : l.length < i) :
        (l ++ [v]).getD i dflt = dflt := by
      rw [List.getD_eq_getElem?_getD]
      have hge : (l ++ [v]).length ≤ i := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [List.getElem?_eq_none hge]
      rfl


    have append_mono (a b : List Bool) (ha : a.length = b.length) (v z : Bool)
        (hab : ∀ i, a.getD i false = true → b.getD i false = true)
        (hvz : v = true → z = true) :
        ∀ i, (a ++ [v]).getD i false = true → (b ++ [z]).getD i false = true := by
      intro i
      rcases Nat.lt_trichotomy i a.length with hi | rfl | hi
      · have hib : i < b.length := ha ▸ hi
        rw [getD_append_singleton_lt _ _ _ hi, getD_append_singleton_lt _ _ _ hib]
        exact hab i
      · rw [getD_append_singleton_eq]
        conv => rhs; lhs; rw [ha, getD_append_singleton_eq]
        exact hvz
      · have hib : b.length < i := ha ▸ hi
        rw [getD_append_singleton_gt _ _ _ hi, getD_append_singleton_gt _ _ _ hib]
        exact id

    have gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (a b : List Bool) (h : ∀ i, a.getD i false = true → b.getD i false = true) :
        g.op.eval (g.inputs.map fun i => a.getD i false) = true →
        g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
      have hop : g.op = .and ∨ g.op = .or := by simpa using hg
      rcases hop with hop | hop
      · simp only [hop, andEval, orEval, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
        intro ha i hi
        exact h i (ha i hi)
      · simp only [hop, andEval, orEval, List.any_map, List.any_eq_true, Function.comp_def, id_eq]
        rintro ⟨i, hi, ha⟩
        exact ⟨i, hi, h i ha⟩

    have fold_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (a b : List Bool) (hlen : a.length = b.length)
        (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
        ∀ i, (gs.foldl wireStep a).getD i false = true → (gs.foldl wireStep b).getD i false = true := by
      induction gs generalizing a b with
      | nil => exact hab
      | cons g gs ih =>
        simp only [List.foldl_cons]
        exact ih (fun g hg => hm g (List.mem_cons_of_mem _ hg)) _ _
          (by simp [wireStep, hlen])
          (append_mono a b hlen _ _ hab (gate_mono g (hm g (by simp)) a b hab))

    have wires_mono (C : Circuit) (hm : Monotone2 C) (x y : Fin 26 → Bool)
        (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
        (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
      apply fold_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp) _ w
      intro i
      by_cases hi : i < 26
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] using hxy ⟨i, hi⟩
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_none]
        exact id
    have exactD (x : Fin 26 → Bool) : D.eval (List.ofFn x)=true ↔
        ∃ p l : Fin 13, p-l ∈ d ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
      refine ⟨sound x,?_⟩
      rintro ⟨p,l,e,xp,xl⟩
      apply wires_mono D hm (edge p l) x _ D.output (allOn p l e)
      intro j active
      change decide (j=Fin.castAdd 13 p ∨ j=Fin.natAdd 13 l)=true at active
      rcases of_decide_eq_true active with h|h
      · simpa only [h] using xp
      · simpa only [h] using xl
    exact (Nat.not_le_of_lt sm (minimal D ⟨hm,hr,exactD⟩)).elim
