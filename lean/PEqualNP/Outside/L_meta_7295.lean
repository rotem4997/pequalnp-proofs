import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
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

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wires_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false :=
  foldl_wireStep_prefix C.gates x w hw

lemma wires_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (k : ℕ)
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

lemma wires_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : List Bool)
    (hx : x.length = n) (w : ℕ) (hw : w < n + C.gates.length) :
    ((⟨C.gates ++ [g], out⟩ : Circuit).wires x).getD w false = (C.wires x).getD w false := by
  change ((C.gates ++ [g]).foldl wireStep x).getD w false = (C.gates.foldl wireStep x).getD w false
  rw [List.foldl_append]
  have hw' : w < (C.gates.foldl wireStep x).length := by
    rw [foldl_wireStep_length, hx]
    exact hw
  exact foldl_wireStep_prefix [g] (C.gates.foldl wireStep x) w hw'

lemma wires_append_last (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : List Bool)
    (hx : x.length = n) :
    ((⟨C.gates ++ [g], out⟩ : Circuit).wires x).getD (n + C.gates.length) false =
      g.op.eval (g.inputs.map fun u => (C.wires x).getD u false) := by
  change ((C.gates ++ [g]).foldl wireStep x).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set acc := C.gates.foldl wireStep x with hacc
  have hlen : acc.length = n + C.gates.length := by
    rw [hacc, foldl_wireStep_length, hx]
  rw [List.getD_eq_getElem?_getD]
  simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + C.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rfl

lemma monotone2_op_or (C : Circuit) (hM : Monotone2 C) (g : Gate) (hg : g ∈ C.gates) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h := (hM g hg).1
  simpa using h

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp2, rfl⟩ := hb
    have hp1 : p < l1.length := by omega
    exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp1, hbp⟩ := hb
    have hp2 : p < l2.length := by omega
    exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩

def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega

lemma unshiftG_inj (k a b : ℕ) (h : unshiftG k a = unshiftG k b) : a = b := by
  unfold unshiftG at h
  split_ifs at h <;> omega

lemma unshiftG_ne (k j : ℕ) : unshiftG k j ≠ k := by
  unfold unshiftG
  split_ifs <;> omega

def constGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

def isAbsorbOp : Bool → GateOp → Bool
  | true, GateOp.or => true
  | false, GateOp.and => true
  | _, _ => false

def rewriteGateConst (n k : ℕ) (b : Bool) (g : Gate) : Gate :=
  if n + k ∈ g.inputs then
    if isAbsorbOp b g.op then constGate b
    else ⟨g.op, (g.inputs.filter (fun w => decide (w ≠ n + k))).map (shiftW n k)⟩
  else
    ⟨g.op, g.inputs.map (shiftW n k)⟩

def elimConst (n k : ℕ) (b : Bool) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (rewriteGateConst n k b), shiftW n k C.output⟩

lemma elimConst_length (n k : ℕ) (b : Bool) (C : Circuit) (hk : k < C.gates.length) :
    (elimConst n k b C).gates.length = C.gates.length - 1 := by
  simp [elimConst, List.length_eraseIdx_of_lt hk]

lemma elimConst_gateAt (n k : ℕ) (b : Bool) (C : Circuit) (hk : k < C.gates.length)
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

lemma elimConst_monotone2 (n k : ℕ) (b : Bool) (C : Circuit) (hM : Monotone2 C) :
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

lemma elimConst_readsBack (n k : ℕ) (b : Bool) (C : Circuit) (hRB : ReadsBack n C)
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

lemma elimConst_wires_eq (n k : ℕ) (b : Bool) (C : Circuit) (x : List Bool) (hx : x.length = n)
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
        · simp [constGate, hop, GateOp.eval]
          exact ⟨n + k, hmem, hval_k⟩
        · simp [isAbsorbOp, hop] at habs
        · simp [isAbsorbOp, hop] at habs
        · simp [constGate, hop, GateOp.eval]
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
          simp only [GateOp.eval, List.any_eq_true, List.mem_map,
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
          simp only [GateOp.eval, List.all_eq_true, List.mem_map,
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

lemma elimConst_eval_eq (n k : ℕ) (b : Bool) (C : Circuit) (x : List Bool) (hx : x.length = n)
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

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < (delGate n g r C).gates.length) :
    gateAt (delGate n g r C) k = mapGate (remap n g r) (gateAt C (unshiftG g k)) := by
  have hk_lt : k < C.gates.length - 1 := by
    rw [← delGate_length n g r C hg]; exact hk
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk_lt
  rw [gateAt_eq_getElem (delGate n g r C) k hk]
  simp only [delGate, List.getElem_map, unshiftG]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_monotone2 (n g r : ℕ) (C : Circuit) (hM : Monotone2 C) :
    Monotone2 (delGate n g r C) := by
  intro gt hgt
  simp only [delGate, List.mem_map] at hgt
  obtain ⟨gt0, hgt0, rfl⟩ := hgt
  have h0 := hM gt0 (List.mem_of_mem_eraseIdx hgt0)
  exact ⟨h0.1, by simp [mapGate, h0.2]⟩

lemma delGate_readsBack (n g r : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    ReadsBack n (delGate n g r C) := by
  intro k hk w' hw'
  rw [delGate_gateAt n g r C hg k hk] at hw'
  simp only [mapGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hk_lt : k < C.gates.length - 1 := by
    rw [← delGate_length n g r C hg]; exact hk
  have hk0_lt : unshiftG g k < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt := hRB (unshiftG g k) hk0_lt w hw
  unfold remap
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma unshiftW_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    unshiftW n g (remap n g r u) = u := by
  unfold unshiftW remap
  split_ifs <;> omega

lemma unshiftW_remap_eq (n g r : ℕ) (hr : r < n + g) :
    unshiftW n g (remap n g r (n + g)) = r := by
  unfold unshiftW remap
  split_ifs <;> omega

lemma delGate_wires_eq (n g r : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : (C.wires x).getD (n + g) false = (C.wires x).getD r false) :
    ∀ w < n + (delGate n g r C).gates.length,
      ((delGate n g r C).wires x).getD w false = (C.wires x).getD (unshiftW n g w) false := by
  have hRB' : ReadsBack n (delGate n g r C) := delGate_readsBack n g r C hRB hg hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have huw : unshiftW n g w = w := by unfold unshiftW; split_ifs <;> omega
      rw [huw, wires_input _ x w (by omega), wires_input _ x w (by omega)]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hlen' := delGate_length n g r C hg
      have hk0_lt : unshiftG g k < C.gates.length := by
        unfold unshiftG; split_ifs <;> omega
      have huw : unshiftW n g (n + k) = n + unshiftG g k := by
        unfold unshiftW unshiftG; split_ifs <;> omega
      rw [hw_eq, huw]
      rw [wires_gate n (delGate n g r C) x hx k hk_lt hRB']
      rw [wires_gate n C x hx (unshiftG g k) hk0_lt hRB]
      rw [delGate_gateAt n g r C hg k hk_lt]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt]
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hRB' k hk_lt (remap n g r u) h1
      simp only [Function.comp_apply]
      rw [ih (remap n g r u) (by omega) (by omega)]
      by_cases hug : u = n + g
      · rw [hug, unshiftW_remap_eq n g r hr, hmatch]
      · rw [unshiftW_remap_ne n g r u hug]

lemma delGate_eval_eq (n g r : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hout : C.output < n + C.gates.length)
    (hmatch : (C.wires x).getD (n + g) false = (C.wires x).getD r false) :
    (delGate n g r C).eval x = C.eval x := by
  unfold Circuit.eval
  have hout' := delGate_output_lt n g r C hg hr hout
  rw [delGate_wires_eq n g r C x hx hRB hg hr hmatch (delGate n g r C).output hout']
  by_cases ho : C.output = n + g
  · simp only [delGate]
    rw [ho, unshiftW_remap_eq n g r hr, ← hmatch]
  · simp only [delGate]
    rw [unshiftW_remap_ne n g r C.output ho]

lemma delGate_wires_mono (n g r : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hM : Monotone2 C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmono_g : (C.wires x).getD (n + g) false = true → (C.wires x).getD r false = true) :
    ∀ w < n + (delGate n g r C).gates.length,
      (C.wires x).getD (unshiftW n g w) false = true →
      ((delGate n g r C).wires x).getD w false = true := by
  have hRB' : ReadsBack n (delGate n g r C) := delGate_readsBack n g r C hRB hg hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwn : w < n
    · have huw : unshiftW n g w = w := by unfold unshiftW; split_ifs <;> omega
      rw [huw, wires_input _ x w (by omega)] at htrue
      rw [wires_input _ x w (by omega)]
      exact htrue
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hlen' := delGate_length n g r C hg
      have hk0_lt : unshiftG g k < C.gates.length := by
        unfold unshiftG; split_ifs <;> omega
      have huw : unshiftW n g (n + k) = n + unshiftG g k := by
        unfold unshiftW unshiftG; split_ifs <;> omega
      rw [hw_eq] at htrue ⊢
      rw [huw, wires_gate n C x hx (unshiftG g k) hk0_lt hRB] at htrue
      rw [wires_gate n (delGate n g r C) x hx k hk_lt hRB']
      rw [delGate_gateAt n g r C hg k hk_lt]
      simp only [mapGate, List.map_map]
      have hop : (gateAt C (unshiftG g k)).op = GateOp.and ∨
          (gateAt C (unshiftG g k)).op = GateOp.or := by
        rw [gateAt_eq_getElem C (unshiftG g k) hk0_lt]
        exact monotone2_op_or C hM C.gates[unshiftG g k] (List.getElem_mem hk0_lt)
      apply gateOp_eval_mono (gateAt C (unshiftG g k)).op hop _ _ (by simp) _ htrue
      intro p hp1 hp2 hv
      simp only [List.getElem_map, Function.comp_apply] at hv ⊢
      set u := (gateAt C (unshiftG g k)).inputs[p]'(by simpa using hp1) with hu_def
      have hu_mem : u ∈ (gateAt C (unshiftG g k)).inputs := List.getElem_mem (by simpa using hp1)
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt]
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu_mem, rfl⟩
        exact hRB' k hk_lt (remap n g r u) h1
      apply ih (remap n g r u) (by omega) (by omega)
      by_cases hug : u = n + g
      · rw [hug, unshiftW_remap_eq n g r hr]
        rw [hug] at hv
        exact hmono_g hv
      · rw [unshiftW_remap_ne n g r u hug]
        exact hv

lemma delGate_eval_mono (n g r : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hM : Monotone2 C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hout : C.output < n + C.gates.length)
    (hmono_g : (C.wires x).getD (n + g) false = true → (C.wires x).getD r false = true)
    (hC : C.eval x = true) :
    (delGate n g r C).eval x = true := by
  unfold Circuit.eval at hC ⊢
  have hout' := delGate_output_lt n g r C hg hr hout
  apply delGate_wires_mono n g r C x hx hM hRB hg hr hmono_g (delGate n g r C).output hout'
  by_cases ho : C.output = n + g
  · simp only [delGate]
    rw [ho, unshiftW_remap_eq n g r hr]
    rw [ho] at hC
    exact hmono_g hC
  · simp only [delGate]
    rw [unshiftW_remap_ne n g r C.output ho]
    exact hC

lemma delGate_wires_prefix_eq (n g r : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g) :
    ∀ w < n + g, ((delGate n g r C).wires x).getD w false = (C.wires x).getD w false := by
  have hRB' : ReadsBack n (delGate n g r C) := delGate_readsBack n g r C hRB hg hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wires_input _ x w (by omega), wires_input _ x w (by omega)]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hkg : k < g := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by
        rw [delGate_length n g r C hg]; omega
      rw [hw_eq, wires_gate n (delGate n g r C) x hx k hk_lt hRB']
      rw [delGate_gateAt n g r C hg k hk_lt]
      have hun : unshiftG g k = k := by unfold unshiftG; simp [hkg]
      rw [hun, wires_gate n C x hx k (by omega) hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k := hRB k (by omega) u hu
      have hrm : remap n g r u = u := by unfold remap; split_ifs <;> omega
      simp only [Function.comp_apply, hrm]
      exact ih u (by omega) (by omega)

lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_lt_size (n : ℕ) (C : Circuit) (a b : ℕ) (h : InCone n C a b) :
    b < C.gates.length := by
  by_contra hge
  push Not at hge
  unfold InCone cones at h
  rw [List.getD_eq_getElem?_getD] at h
  have hlen : (C.gates.foldl (coneStep n) []).length = C.gates.length := by
    rw [foldl_coneStep_length, List.length_nil, Nat.zero_add]
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ m < j, (cones n C).getD m [] = acc.getD m [] := by
    intro m hm
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc m (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi

lemma inCone_lt (n : ℕ) (C : Circuit) (a b : ℕ) (h : InCone n C a b) : a < b := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    have hb := inCone_lt_size n C a b h
    rw [inCone_iff n C a b hb] at h
    obtain ⟨w, _, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · omega
    · have := ih (w - n) (by omega) hcone
      omega

lemma exists_direct_reader (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (h : InCone n C i j) :
    ∃ g, i < g ∧ g ≤ j ∧ g < C.gates.length ∧ n + i ∈ (gateAt C g).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · refine ⟨j, by omega, le_refl j, hj, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [heq]
      exact hw
    · have hklt : w - n < j := by omega
      obtain ⟨g, hig, hgk, hglen, hmem⟩ := ih (w - n) hklt (by omega) hcone
      exact ⟨g, hig, by omega, hglen, hmem⟩

lemma inCone_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (i j : ℕ)
    (hj : j < C.gates.length) :
    InCone n ⟨C.gates ++ [g], out⟩ i j ↔ InCone n C i j := by
  unfold InCone cones
  have hlen : j < (C.gates.foldl (coneStep n) []).length := by
    rw [foldl_coneStep_length, List.length_nil, Nat.zero_add]
    exact hj
  have heq : ((C.gates ++ [g]).foldl (coneStep n) []).getD j [] =
      (C.gates.foldl (coneStep n) []).getD j [] := by
    rw [List.foldl_append]
    exact foldl_coneStep_prefix n [g] (C.gates.foldl (coneStep n) []) j hlen
  rw [heq]

lemma delGate_inCone_imp (n r y : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hr : r < C.gates.length) (hy_mem : y ∈ (gateAt C r).inputs) :
    ∀ j' < (delGate n r y C).gates.length, ∀ i',
      InCone n (delGate n r y C) i' j' → InCone n C (unshiftG r i') (unshiftG r j') := by
  have hy_lt : y < n + r := hRB r hr y hy_mem
  have hlen' := delGate_length n r y C hr
  intro j'
  induction j' using Nat.strong_induction_on with
  | ind j' ih =>
    intro hj' i' hcone
    have hj0_lt : unshiftG r j' < C.gates.length := by
      unfold unshiftG; split_ifs <;> omega
    rw [inCone_iff n (delGate n r y C) i' j' hj'] at hcone
    obtain ⟨w', hw'_in, hnw', hw'_lt, hcase⟩ := hcone
    rw [delGate_gateAt n r y C hr j' hj'] at hw'_in
    simp only [mapGate, List.mem_map] at hw'_in
    obtain ⟨w, hw_in, rfl⟩ := hw'_in
    have hw_lt : w < n + unshiftG r j' := hRB (unshiftG r j') hj0_lt w hw_in
    by_cases hwr : w = n + r
    · have hrm : remap n r y w = y := by
        rw [hwr]; unfold remap; split_ifs <;> omega
      rw [hrm] at hnw' hw'_lt hcase
      have hun_y : unshiftG r (y - n) = y - n := by
        unfold unshiftG; split_ifs <;> omega
      have hcone_r : InCone n C (unshiftG r i') r := by
        rw [inCone_iff n C (unshiftG r i') r hr]
        refine ⟨y, hy_mem, hnw', hy_lt, ?_⟩
        rcases hcase with rfl | hsub
        · exact Or.inl hun_y
        · right
          rw [← hun_y]
          exact ih (y - n) (by omega) (by omega) i' hsub
      rw [inCone_iff n C (unshiftG r i') (unshiftG r j') hj0_lt]
      refine ⟨w, hw_in, by omega, hw_lt, Or.inr ?_⟩
      have hsub_r : w - n = r := by omega
      rw [hsub_r]
      exact hcone_r
    · have hnw : n ≤ w := by
        unfold remap at hnw'; split_ifs at hnw' <;> omega
      have hun_w : unshiftG r (remap n r y w - n) = w - n := by
        unfold unshiftG remap; split_ifs <;> omega
      rw [inCone_iff n C (unshiftG r i') (unshiftG r j') hj0_lt]
      refine ⟨w, hw_in, hnw, hw_lt, ?_⟩
      rcases hcase with rfl | hsub
      · exact Or.inl hun_w
      · right
        rw [← hun_w]
        exact ih (remap n r y w - n) (by omega) (by omega) i' hsub

def quadInput (Q : Finset (Fin 13)) : List Bool :=
  incidenceInput Q (missLines singerLines3 Q)

def ValidPG (l0 : Fin 13) (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack 26 C ∧
    (∀ (p l : Fin 13), p ∈ singerLines3 l → p ≠ 0 ∨ l ≠ l0 →
      C.eval (incidenceInput {p} {l}) = true) ∧
    (∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q → C.eval (quadInput Q) = false)

lemma incidenceInput_length (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
  simp [incidenceInput]

lemma quadInput_length (Q : Finset (Fin 13)) : (quadInput Q).length = 26 :=
  incidenceInput_length Q (missLines singerLines3 Q)

lemma one_mem_singerLines3_zero : (1 : Fin 13) ∈ singerLines3 0 := by
  decide

lemma exists_quadrangle : ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q := by
  refine ⟨{0, 1, 2, 5}, ?_⟩
  decide

lemma validPG_output_lt (l0 : Fin 13) (C : Circuit) (hV : ValidPG l0 C) :
    C.output < 26 + C.gates.length := by
  by_contra hge
  push Not at hge
  have htrue : C.eval (incidenceInput {(1 : Fin 13)} {(0 : Fin 13)}) = true :=
    hV.2.2.1 1 0 one_mem_singerLines3_zero (Or.inl (by decide))
  unfold Circuit.eval at htrue
  rw [List.getD_eq_getElem?_getD] at htrue
  have hlen : (C.wires (incidenceInput {(1 : Fin 13)} {(0 : Fin 13)})).length =
      26 + C.gates.length := by
    rw [wires_length, incidenceInput_length]
  rw [List.getElem?_eq_none (by omega)] at htrue
  simp at htrue

lemma validPG_output_ne_const (l0 : Fin 13) (C : Circuit) (hV : ValidPG l0 C) (k : ℕ) (b : Bool)
    (hk : k < C.gates.length) (hgk : gateAt C k = constGate b) :
    C.output ≠ 26 + k := by
  intro heq
  cases b with
  | false =>
    have htrue : C.eval (incidenceInput {(1 : Fin 13)} {(0 : Fin 13)}) = true :=
      hV.2.2.1 1 0 one_mem_singerLines3_zero (Or.inl (by decide))
    unfold Circuit.eval at htrue
    rw [heq, wires_gate 26 C _ (incidenceInput_length _ _) k hk hV.2.1, hgk] at htrue
    simp [constGate, GateOp.eval] at htrue
  | true =>
    obtain ⟨Q, hQ⟩ := exists_quadrangle
    have hfalse : C.eval (quadInput Q) = false := hV.2.2.2 Q hQ
    unfold Circuit.eval at hfalse
    rw [heq, wires_gate 26 C _ (quadInput_length Q) k hk hV.2.1, hgk] at hfalse
    simp [constGate, GateOp.eval] at hfalse

lemma part1_distinct_binary (l0 : Fin 13) (C : Circuit) (hV : ValidPG l0 C)
    (hMin : ∀ D : Circuit, ValidPG l0 D → C.size ≤ D.size) :
    ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by
  rcases hV with ⟨hM, hRB, hInc, hQuad⟩
  have hV : ValidPG l0 C := ⟨hM, hRB, hInc, hQuad⟩
  have hout : C.output < 26 + C.gates.length := validPG_output_lt l0 C hV
  intro g hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hgk : gateAt C k = C.gates[k] := gateAt_eq_getElem C k hk
  have hlen_le : C.gates[k].inputs.length ≤ 2 := (hM C.gates[k] (List.getElem_mem hk)).2
  have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or :=
    monotone2_op_or C hM C.gates[k] (List.getElem_mem hk)
  rcases hin : C.gates[k].inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
  · exfalso
    rcases hop with hop | hop
    · have hconst : gateAt C k = constGate true := by
        rw [hgk]; cases h : C.gates[k]; simp_all [constGate]
      have hout_ne : C.output ≠ 26 + k := validPG_output_ne_const l0 C hV k true hk hconst
      set C' := elimConst 26 k true C
      have hval_k : ∀ x : List Bool, x.length = 26 → (C.wires x).getD (26 + k) false = true := by
        intro x hx
        rw [wires_gate 26 C x hx k hk hRB, hconst]
        simp [constGate, GateOp.eval]
      have hV' : ValidPG l0 C' := by
        refine ⟨elimConst_monotone2 26 k true C hM, elimConst_readsBack 26 k true C hRB hk, ?_, ?_⟩
        · intro p l hpl hne
          rw [elimConst_eval_eq 26 k true C _ (incidenceInput_length _ _) hM hRB hk hout hout_ne
            (hval_k _ (incidenceInput_length _ _))]
          exact hInc p l hpl hne
        · intro Q hQ
          rw [elimConst_eval_eq 26 k true C _ (quadInput_length Q) hM hRB hk hout hout_ne
            (hval_k _ (quadInput_length Q))]
          exact hQuad Q hQ
      have hle := hMin C' hV'
      have hsz : C'.size = C.size - 1 := elimConst_length 26 k true C hk
      change C.gates.length ≤ C'.gates.length at hle
      change C'.gates.length = C.gates.length - 1 at hsz
      omega
    · have hconst : gateAt C k = constGate false := by
        rw [hgk]; cases h : C.gates[k]; simp_all [constGate]
      have hout_ne : C.output ≠ 26 + k := validPG_output_ne_const l0 C hV k false hk hconst
      set C' := elimConst 26 k false C
      have hval_k : ∀ x : List Bool, x.length = 26 → (C.wires x).getD (26 + k) false = false := by
        intro x hx
        rw [wires_gate 26 C x hx k hk hRB, hconst]
        simp [constGate, GateOp.eval]
      have hV' : ValidPG l0 C' := by
        refine ⟨elimConst_monotone2 26 k false C hM, elimConst_readsBack 26 k false C hRB hk, ?_, ?_⟩
        · intro p l hpl hne
          rw [elimConst_eval_eq 26 k false C _ (incidenceInput_length _ _) hM hRB hk hout hout_ne
            (hval_k _ (incidenceInput_length _ _))]
          exact hInc p l hpl hne
        · intro Q hQ
          rw [elimConst_eval_eq 26 k false C _ (quadInput_length Q) hM hRB hk hout hout_ne
            (hval_k _ (quadInput_length Q))]
          exact hQuad Q hQ
      have hle := hMin C' hV'
      have hsz : C'.size = C.size - 1 := elimConst_length 26 k false C hk
      change C.gates.length ≤ C'.gates.length at hle
      change C'.gates.length = C.gates.length - 1 at hsz
      omega
  · exfalso
    have hu_lt : u < 26 + k := by
      apply hRB k hk u
      rw [hgk, hin]
      simp
    have hmatch : ∀ x : List Bool, x.length = 26 →
        (C.wires x).getD (26 + k) false = (C.wires x).getD u false := by
      intro x hx
      rw [wires_gate 26 C x hx k hk hRB, hgk, hin]
      rcases hop with hop | hop <;> simp [hop, GateOp.eval]
    set C' := delGate 26 k u C
    have hV' : ValidPG l0 C' := by
      refine ⟨delGate_monotone2 26 k u C hM, delGate_readsBack 26 k u C hRB hk hu_lt, ?_, ?_⟩
      · intro p l hpl hne
        rw [delGate_eval_eq 26 k u C _ (incidenceInput_length _ _) hRB hk hu_lt hout
          (hmatch _ (incidenceInput_length _ _))]
        exact hInc p l hpl hne
      · intro Q hQ
        rw [delGate_eval_eq 26 k u C _ (quadInput_length Q) hRB hk hu_lt hout
          (hmatch _ (quadInput_length Q))]
        exact hQuad Q hQ
    have hle := hMin C' hV'
    have hsz : C'.size = C.size - 1 := delGate_length 26 k u C hk
    change C.gates.length ≤ C'.gates.length at hle
    change C'.gates.length = C.gates.length - 1 at hsz
    omega
  · refine ⟨rfl, ?_⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    intro heq
    subst heq
    have hu_lt : u < 26 + k := by
      apply hRB k hk u
      rw [hgk, hin]
      simp
    have hmatch : ∀ x : List Bool, x.length = 26 →
        (C.wires x).getD (26 + k) false = (C.wires x).getD u false := by
      intro x hx
      rw [wires_gate 26 C x hx k hk hRB, hgk, hin]
      rcases hop with hop | hop <;> simp [hop, GateOp.eval]
    set C' := delGate 26 k u C
    have hV' : ValidPG l0 C' := by
      refine ⟨delGate_monotone2 26 k u C hM, delGate_readsBack 26 k u C hRB hk hu_lt, ?_, ?_⟩
      · intro p l hpl hne
        rw [delGate_eval_eq 26 k u C _ (incidenceInput_length _ _) hRB hk hu_lt hout
          (hmatch _ (incidenceInput_length _ _))]
        exact hInc p l hpl hne
      · intro Q hQ
        rw [delGate_eval_eq 26 k u C _ (quadInput_length Q) hRB hk hu_lt hout
          (hmatch _ (quadInput_length Q))]
        exact hQuad Q hQ
    have hle := hMin C' hV'
    have hsz : C'.size = C.size - 1 := delGate_length 26 k u C hk
    change C.gates.length ≤ C'.gates.length at hle
    change C'.gates.length = C.gates.length - 1 at hsz
    omega
  · simp [hin] at hlen_le

lemma other_input_of_mem (C : Circuit) (k u : ℕ) (hk : k < C.gates.length)
    (hBin : ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hu : u ∈ (gateAt C k).inputs) :
    ∃ y, y ∈ (gateAt C k).inputs ∧ y ≠ u ∧
      ((gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u]) := by
  have hk_bin := hBin C.gates[k] (List.getElem_mem hk)
  rw [← gateAt_eq_getElem C k hk] at hk_bin
  rcases hk_bin with ⟨hlen, hne⟩
  rcases hin : (gateAt C k).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [hin] at hlen
  · simp [hin] at hlen
  · simp only [hin, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at hne
    rw [hin] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact ⟨y, by simp, hne.symm, Or.inl rfl⟩
    · exact ⟨x, by simp, hne, Or.inr rfl⟩
  · simp [hin] at hlen

lemma or_gate_eval_pair (C : Circuit) (x : List Bool) (hx : x.length = 26)
    (hRB : ReadsBack 26 C) (r u y : ℕ) (hr : r < C.gates.length)
    (hor : (gateAt C r).op = GateOp.or)
    (hin : (gateAt C r).inputs = [u, y] ∨ (gateAt C r).inputs = [y, u]) :
    (C.wires x).getD (26 + r) false =
      ((C.wires x).getD u false || (C.wires x).getD y false) := by
  rw [wires_gate 26 C x hx r hr hRB, hor]
  rcases hin with h | h <;> rw [h]
  · simp [GateOp.eval]
  · simp [GateOp.eval, Bool.or_comm]

lemma no_and_reader_pg (l0 : Fin 13) (C : Circuit) (a r : ℕ)
    (hV : ValidPG l0 C) (hMin : ∀ D : Circuit, ValidPG l0 D → C.size ≤ D.size)
    (har : a < r) (hr : r < C.gates.length)
    (haZero : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      (C.wires (quadInput Q)).getD (26 + a) false = false)
    (hrAnd : (gateAt C r).op = GateOp.and)
    (hmem : 26 + a ∈ (gateAt C r).inputs) : False := by
  rcases hV with ⟨hM, hRB, hInc, hQuad⟩
  have hout : C.output < 26 + C.gates.length := validPG_output_lt l0 C ⟨hM, hRB, hInc, hQuad⟩
  set C' := delGate 26 r (26 + a) C
  have hmono_r : ∀ x : List Bool, x.length = 26 →
      (C.wires x).getD (26 + r) false = true → (C.wires x).getD (26 + a) false = true := by
    intro x hx hrt
    rw [wires_gate 26 C x hx r hr hRB, hrAnd] at hrt
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hrt
    exact hrt _ ⟨26 + a, hmem, rfl⟩
  have hV' : ValidPG l0 C' := by
    refine ⟨delGate_monotone2 26 r (26 + a) C hM,
      delGate_readsBack 26 r (26 + a) C hRB hr (by omega), ?_, ?_⟩
    · intro p l hpl hne
      exact delGate_eval_mono 26 r (26 + a) C _ (incidenceInput_length _ _) hM hRB hr (by omega)
        hout (hmono_r _ (incidenceInput_length _ _)) (hInc p l hpl hne)
    · intro Q hQ
      have haF : (C.wires (quadInput Q)).getD (26 + a) false = false := haZero Q hQ
      have hrF : (C.wires (quadInput Q)).getD (26 + r) false = false := by
        cases hv : (C.wires (quadInput Q)).getD (26 + r) false with
        | false => rfl
        | true =>
          have := hmono_r (quadInput Q) (quadInput_length Q) hv
          rw [haF] at this
          cases this
      rw [delGate_eval_eq 26 r (26 + a) C _ (quadInput_length Q) hRB hr (by omega) hout
        (by rw [hrF, haF])]
      exact hQuad Q hQ
  have hle := hMin C' hV'
  have hsz : C'.size = C.size - 1 := delGate_length 26 r (26 + a) C hr
  change C.gates.length ≤ C'.gates.length at hle
  change C'.gates.length = C.gates.length - 1 at hsz
  omega

lemma no_two_or_readers_pg (l0 : Fin 13) (C : Circuit) (a r1 r2 : ℕ)
    (hV : ValidPG l0 C) (hMin : ∀ D : Circuit, ValidPG l0 D → C.size ≤ D.size)
    (hBin : ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (har1 : a < r1) (hr12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (haZero : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      (C.wires (quadInput Q)).getD (26 + a) false = false)
    (hr1Or : (gateAt C r1).op = GateOp.or) (hr2Or : (gateAt C r2).op = GateOp.or)
    (hmem1 : 26 + a ∈ (gateAt C r1).inputs) (hmem2 : 26 + a ∈ (gateAt C r2).inputs) : False := by
  rcases hV with ⟨hM, hRB, hInc, hQuad⟩
  have hout : C.output < 26 + C.gates.length := validPG_output_lt l0 C ⟨hM, hRB, hInc, hQuad⟩
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨y1, hy1_mem, _, hy1_in⟩ := other_input_of_mem C r1 (26 + a) hr1 hBin hmem1
  obtain ⟨y2, hy2_mem, _, hy2_in⟩ := other_input_of_mem C r2 (26 + a) hr2 hBin hmem2
  have hy1_lt : y1 < 26 + r1 := hRB r1 hr1 y1 hy1_mem
  have hy2_lt : y2 < 26 + r2 := hRB r2 hr2 y2 hy2_mem
  set C1 := delGate 26 r2 y2 C with hC1
  have hC1_len : C1.gates.length = C.gates.length - 1 := delGate_length 26 r2 y2 C hr2
  have hC1_M : Monotone2 C1 := delGate_monotone2 26 r2 y2 C hM
  have hC1_RB : ReadsBack 26 C1 := delGate_readsBack 26 r2 y2 C hRB hr2 hy2_lt
  have hC1_out : C1.output < 26 + C1.gates.length := delGate_output_lt 26 r2 y2 C hr2 hy2_lt hout
  have hr1_C1 : r1 < C1.gates.length := by omega
  set C2 := delGate 26 r1 y1 C1 with hC2
  have hC2_len : C2.gates.length = C.gates.length - 2 := by
    rw [hC2, delGate_length 26 r1 y1 C1 hr1_C1, hC1_len]; omega
  have hC2_M : Monotone2 C2 := delGate_monotone2 26 r1 y1 C1 hC1_M
  have hC2_RB : ReadsBack 26 C2 := delGate_readsBack 26 r1 y1 C1 hC1_RB hr1_C1 hy1_lt
  have hC2_out : C2.output < 26 + C2.gates.length :=
    delGate_output_lt 26 r1 y1 C1 hr1_C1 hy1_lt hC1_out
  set C' : Circuit := ⟨C2.gates ++ [⟨GateOp.or, [C2.output, 26 + a]⟩], 26 + C2.gates.length⟩
  have hC'_len : C'.gates.length = C.gates.length - 1 := by
    simp only [C', List.length_append, List.length_singleton, hC2_len]
    omega
  have hC'_M : Monotone2 C' := by
    intro g hg
    simp only [C', List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC2_M g hg
    · exact ⟨Or.inr rfl, by simp⟩
  have hC'_RB : ReadsBack 26 C' := by
    intro k hk w hw
    have hk' : k < C2.gates.length + 1 := by simpa [C'] using hk
    by_cases hkm : k < C2.gates.length
    · have hgat : gateAt C' k = gateAt C2 k := by
        rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem C2 k hkm]
        simp [C', List.getElem_append_left hkm]
      rw [hgat] at hw
      exact hC2_RB k hkm w hw
    · have hkeq : k = C2.gates.length := by omega
      have hgat : gateAt C' k = ⟨GateOp.or, [C2.output, 26 + a]⟩ := by
        rw [gateAt_eq_getElem C' k hk]
        simp [C', hkeq]
      rw [hgat] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega
      · rw [hkeq, hC2_len]; omega
  have hC'_eval : ∀ x : List Bool, x.length = 26 →
      C'.eval x = if (C.wires x).getD (26 + a) false = true then true else C.eval x := by
    intro x hx
    have hlast : C'.eval x =
        ((C2.wires x).getD C2.output false || (C2.wires x).getD (26 + a) false) := by
      unfold Circuit.eval
      have h := wires_append_last 26 C2 ⟨GateOp.or, [C2.output, 26 + a]⟩
        (26 + C2.gates.length) x hx
      simpa [C', GateOp.eval] using h
    have ha_eq : (C2.wires x).getD (26 + a) false = (C.wires x).getD (26 + a) false := by
      rw [hC2, delGate_wires_prefix_eq 26 r1 y1 C1 x hx hC1_RB hr1_C1 hy1_lt (26 + a) (by omega)]
      rw [hC1, delGate_wires_prefix_eq 26 r2 y2 C x hx hRB hr2 hy2_lt (26 + a) (by omega)]
    rw [hlast, ha_eq]
    cases hva : (C.wires x).getD (26 + a) false
    · simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      have hmatch2 : (C.wires x).getD (26 + r2) false = (C.wires x).getD y2 false := by
        rw [or_gate_eval_pair C x hx hRB r2 (26 + a) y2 hr2 hr2Or hy2_in, hva, Bool.false_or]
      have hmatch1_C : (C.wires x).getD (26 + r1) false = (C.wires x).getD y1 false := by
        rw [or_gate_eval_pair C x hx hRB r1 (26 + a) y1 hr1 hr1Or hy1_in, hva, Bool.false_or]
      have hmatch1 : (C1.wires x).getD (26 + r1) false = (C1.wires x).getD y1 false := by
        rw [hC1, delGate_wires_prefix_eq 26 r2 y2 C x hx hRB hr2 hy2_lt (26 + r1) (by omega)]
        rw [delGate_wires_prefix_eq 26 r2 y2 C x hx hRB hr2 hy2_lt y1 (by omega)]
        exact hmatch1_C
      have hev2 : C2.eval x = C1.eval x :=
        delGate_eval_eq 26 r1 y1 C1 x hx hC1_RB hr1_C1 hy1_lt hC1_out hmatch1
      have hev1 : C1.eval x = C.eval x :=
        delGate_eval_eq 26 r2 y2 C x hx hRB hr2 hy2_lt hout hmatch2
      exact hev2.trans hev1
    · simp
  have hV' : ValidPG l0 C' := by
    refine ⟨hC'_M, hC'_RB, ?_, ?_⟩
    · intro p l hpl hne
      rw [hC'_eval _ (incidenceInput_length _ _)]
      split_ifs
      · rfl
      · exact hInc p l hpl hne
    · intro Q hQ
      rw [hC'_eval _ (quadInput_length Q), haZero Q hQ]
      simp [hQuad Q hQ]
  have hle := hMin C' hV'
  change C.gates.length ≤ C'.gates.length at hle
  rw [hC'_len] at hle
  omega

lemma no_unique_or_reader_pg (l0 : Fin 13) (C : Circuit) (a b r : ℕ)
    (hV : ValidPG l0 C)
    (hMinPairs : ∀ D : Circuit, ValidPG l0 D → D.size = C.size → andPairs 26 C ≤ andPairs 26 D)
    (hBin : ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (har : a < r) (hrb : r < b) (hb : b < C.gates.length)
    (haAnd : (gateAt C a).op = GateOp.and) (hbAnd : (gateAt C b).op = GateOp.and)
    (hCone : InCone 26 C a b)
    (haZero : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      (C.wires (quadInput Q)).getD (26 + a) false = false)
    (hrOr : (gateAt C r).op = GateOp.or)
    (hmem : 26 + a ∈ (gateAt C r).inputs)
    (huniq : ∀ k < C.gates.length, 26 + a ∈ (gateAt C k).inputs → k = r) : False := by
  rcases hV with ⟨hM, hRB, hInc, hQuad⟩
  have hout : C.output < 26 + C.gates.length := validPG_output_lt l0 C ⟨hM, hRB, hInc, hQuad⟩
  have hr : r < C.gates.length := by omega
  obtain ⟨y, hy_mem, hy_ne, hy_in⟩ := other_input_of_mem C r (26 + a) hr hBin hmem
  have hy_lt : y < 26 + r := hRB r hr y hy_mem
  set Cmid := delGate 26 r y C with hCmid
  have hCmid_len : Cmid.gates.length = C.gates.length - 1 := delGate_length 26 r y C hr
  have hCmid_M : Monotone2 Cmid := delGate_monotone2 26 r y C hM
  have hCmid_RB : ReadsBack 26 Cmid := delGate_readsBack 26 r y C hRB hr hy_lt
  have hCmid_out : Cmid.output < 26 + Cmid.gates.length :=
    delGate_output_lt 26 r y C hr hy_lt hout
  set C' : Circuit := ⟨Cmid.gates ++ [⟨GateOp.or, [Cmid.output, 26 + a]⟩], 26 + Cmid.gates.length⟩
  have hC'_len : C'.gates.length = C.gates.length := by
    simp only [C', List.length_append, List.length_singleton, hCmid_len]
    omega
  have hC'_M : Monotone2 C' := by
    intro g hg
    simp only [C', List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hCmid_M g hg
    · exact ⟨Or.inr rfl, by simp⟩
  have hC'_RB : ReadsBack 26 C' := by
    intro k hk w hw
    have hk' : k < Cmid.gates.length + 1 := by simpa [C'] using hk
    by_cases hkm : k < Cmid.gates.length
    · have hgat : gateAt C' k = gateAt Cmid k := by
        rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem Cmid k hkm]
        simp [C', List.getElem_append_left hkm]
      rw [hgat] at hw
      exact hCmid_RB k hkm w hw
    · have hkeq : k = Cmid.gates.length := by omega
      have hgat : gateAt C' k = ⟨GateOp.or, [Cmid.output, 26 + a]⟩ := by
        rw [gateAt_eq_getElem C' k hk]
        simp [C', hkeq]
      rw [hgat] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega
      · rw [hkeq, hCmid_len]; omega
  have hC'_eval : ∀ x : List Bool, x.length = 26 →
      C'.eval x = if (C.wires x).getD (26 + a) false = true then true else C.eval x := by
    intro x hx
    have hlast : C'.eval x =
        ((Cmid.wires x).getD Cmid.output false || (Cmid.wires x).getD (26 + a) false) := by
      unfold Circuit.eval
      have h := wires_append_last 26 Cmid ⟨GateOp.or, [Cmid.output, 26 + a]⟩
        (26 + Cmid.gates.length) x hx
      simpa [C', GateOp.eval] using h
    have ha_eq : (Cmid.wires x).getD (26 + a) false = (C.wires x).getD (26 + a) false := by
      rw [hCmid, delGate_wires_prefix_eq 26 r y C x hx hRB hr hy_lt (26 + a) (by omega)]
    rw [hlast, ha_eq]
    cases hva : (C.wires x).getD (26 + a) false
    · simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      have hmatch : (C.wires x).getD (26 + r) false = (C.wires x).getD y false := by
        rw [or_gate_eval_pair C x hx hRB r (26 + a) y hr hrOr hy_in, hva, Bool.false_or]
      exact delGate_eval_eq 26 r y C x hx hRB hr hy_lt hout hmatch
    · simp
  have hV' : ValidPG l0 C' := by
    refine ⟨hC'_M, hC'_RB, ?_, ?_⟩
    · intro p l hpl hne
      rw [hC'_eval _ (incidenceInput_length _ _)]
      split_ifs
      · rfl
      · exact hInc p l hpl hne
    · intro Q hQ
      rw [hC'_eval _ (quadInput_length Q), haZero Q hQ]
      simp [hQuad Q hQ]
  have hgateAt_lt : ∀ m < Cmid.gates.length, gateAt C' m = gateAt Cmid m := by
    intro m hm
    have hm' : m < C'.gates.length := by rw [hC'_len]; omega
    rw [gateAt_eq_getElem C' m hm', gateAt_eq_getElem Cmid m hm]
    simp [C', List.getElem_append_left hm]
  have hgateAt_last : gateAt C' Cmid.gates.length = ⟨GateOp.or, [Cmid.output, 26 + a]⟩ := by
    have hm' : Cmid.gates.length < C'.gates.length := by rw [hC'_len]; omega
    rw [gateAt_eq_getElem C' Cmid.gates.length hm']
    simp [C']
  have hno_reader_mid : ∀ m < Cmid.gates.length, 26 + a ∉ (gateAt Cmid m).inputs := by
    intro m hm hmem_m
    rw [hCmid, delGate_gateAt 26 r y C hr m hm] at hmem_m
    simp only [mapGate, List.mem_map] at hmem_m
    obtain ⟨u, hu_in, hu_eq⟩ := hmem_m
    have hm0_lt : unshiftG r m < C.gates.length := by
      unfold unshiftG; split_ifs <;> omega
    have hu_a : u = 26 + a := by
      unfold remap at hu_eq
      split_ifs at hu_eq with h1 h2
      · exact hu_eq
      · exact absurd hu_eq hy_ne
      · omega
    rw [hu_a] at hu_in
    have heq_r := huniq (unshiftG r m) hm0_lt hu_in
    exact unshiftG_ne r m heq_r
  have hpairs_lt : andPairs 26 C' < andPairs 26 C := by
    unfold andPairs
    set f : ℕ × ℕ → ℕ × ℕ := fun p => (unshiftG r p.1, unshiftG r p.2)
    have hf_inj : Function.Injective f := by
      intro p1 p2 h
      have h1 : unshiftG r p1.1 = unshiftG r p2.1 := congrArg Prod.fst h
      have h2 : unshiftG r p1.2 = unshiftG r p2.2 := congrArg Prod.snd h
      exact Prod.ext (unshiftG_inj r p1.1 p2.1 h1) (unshiftG_inj r p1.2 p2.2 h2)
    rw [← Finset.card_image_of_injective _ hf_inj]
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨(a, b), ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨⟨i', j'⟩, hp', rfl⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp'
      rcases hp' with ⟨⟨hi'_lt, hj'_lt⟩, hi'_and, hj'_and, hcone'⟩
      have hi'_mid : i' < Cmid.gates.length := by
        by_contra hge
        have heq : i' = Cmid.gates.length := by omega
        rw [heq, hgateAt_last] at hi'_and
        cases hi'_and
      have hj'_mid : j' < Cmid.gates.length := by
        by_contra hge
        have heq : j' = Cmid.gates.length := by omega
        rw [heq, hgateAt_last] at hj'_and
        cases hj'_and
      have hi_lt : unshiftG r i' < C.gates.length := by
        unfold unshiftG; split_ifs <;> omega
      have hj_lt : unshiftG r j' < C.gates.length := by
        unfold unshiftG; split_ifs <;> omega
      have hi_and : (gateAt C (unshiftG r i')).op = GateOp.and := by
        rw [hgateAt_lt i' hi'_mid, hCmid, delGate_gateAt 26 r y C hr i' hi'_mid] at hi'_and
        exact hi'_and
      have hj_and : (gateAt C (unshiftG r j')).op = GateOp.and := by
        rw [hgateAt_lt j' hj'_mid, hCmid, delGate_gateAt 26 r y C hr j' hj'_mid] at hj'_and
        exact hj'_and
      have hcone_mid : InCone 26 Cmid i' j' :=
        (inCone_append_lt 26 Cmid _ (26 + Cmid.gates.length) i' j' hj'_mid).mp hcone'
      have hcone_orig : InCone 26 C (unshiftG r i') (unshiftG r j') :=
        delGate_inCone_imp 26 r y C hRB hr hy_mem j' hj'_mid i' hcone_mid
      simp only [f, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi_lt, hj_lt⟩, hi_and, hj_and, hcone_orig⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, hb⟩, haAnd, hbAnd, hCone⟩
    · intro hab_mem
      rw [Finset.mem_image] at hab_mem
      obtain ⟨⟨i', j'⟩, hp', hfeq⟩ := hab_mem
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp'
      rcases hp' with ⟨⟨_, hj'_lt⟩, _, hj'_and, hcone'⟩
      have hi'_a : i' = a := by
        have h1 : unshiftG r i' = a := congrArg Prod.fst hfeq
        unfold unshiftG at h1
        split_ifs at h1 <;> omega
      have hj'_mid : j' < Cmid.gates.length := by
        by_contra hge
        have heq_j : j' = Cmid.gates.length := by omega
        rw [heq_j, hgateAt_last] at hj'_and
        cases hj'_and
      rw [hi'_a] at hcone'
      have hcone_mid : InCone 26 Cmid a j' :=
        (inCone_append_lt 26 Cmid _ (26 + Cmid.gates.length) a j' hj'_mid).mp hcone'
      obtain ⟨m, _, _, hm_lt, hm_mem⟩ := exists_direct_reader 26 Cmid a j' hj'_mid hcone_mid
      exact hno_reader_mid m hm_lt hm_mem
  have hle := hMinPairs C' hV' hC'_len
  omega

lemma part2_stacked_and_fires (l0 : Fin 13) (C : Circuit) (hV : ValidPG l0 C)
    (hMin : ∀ D : Circuit, ValidPG l0 D → C.size ≤ D.size)
    (hMinPairs : ∀ D : Circuit, ValidPG l0 D → D.size = C.size → andPairs 26 C ≤ andPairs 26 D)
    (hBin : ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) :
    ∀ a b : ℕ, (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b →
      ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
        (C.wires (quadInput Q)).getD (26 + a) false = true := by
  intro a b haAnd hbAnd hCone
  by_contra hno
  push Not at hno
  have haZero : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      (C.wires (quadInput Q)).getD (26 + a) false = false := by
    intro Q hQ
    have hne := hno Q hQ
    cases hv : (C.wires (quadInput Q)).getD (26 + a) false
    · rfl
    · exact absurd hv hne
  have hb_lt : b < C.gates.length := inCone_lt_size 26 C a b hCone
  have hab : a < b := inCone_lt 26 C a b hCone
  obtain ⟨r0, har0, hr0b, hr0_lt, hr0_mem⟩ := exists_direct_reader 26 C a b hb_lt hCone
  by_cases hand : ∃ r < C.gates.length, (gateAt C r).op = GateOp.and ∧
      26 + a ∈ (gateAt C r).inputs
  · obtain ⟨r, hr_lt, hr_and, hr_mem⟩ := hand
    have har : a < r := by
      have := hV.2.1 r hr_lt (26 + a) hr_mem
      omega
    exact no_and_reader_pg l0 C a r hV hMin har hr_lt haZero hr_and hr_mem
  · push Not at hand
    have hall_or : ∀ r < C.gates.length, 26 + a ∈ (gateAt C r).inputs →
        (gateAt C r).op = GateOp.or := by
      intro r hr_lt hr_mem
      have hop := monotone2_op_or C hV.1 C.gates[r] (List.getElem_mem hr_lt)
      rw [← gateAt_eq_getElem C r hr_lt] at hop
      rcases hop with h | h
      · exact absurd hr_mem (hand r hr_lt h)
      · exact h
    by_cases htwo : ∃ r1 < C.gates.length, ∃ r2 < C.gates.length,
        r1 < r2 ∧ 26 + a ∈ (gateAt C r1).inputs ∧ 26 + a ∈ (gateAt C r2).inputs
    · obtain ⟨r1, hr1_lt, r2, hr2_lt, hr12, hr1_mem, hr2_mem⟩ := htwo
      have har1 : a < r1 := by
        have := hV.2.1 r1 hr1_lt (26 + a) hr1_mem
        omega
      exact no_two_or_readers_pg l0 C a r1 r2 hV hMin hBin har1 hr12 hr2_lt haZero
        (hall_or r1 hr1_lt hr1_mem) (hall_or r2 hr2_lt hr2_mem) hr1_mem hr2_mem
    · push Not at htwo
      have huniq : ∀ k < C.gates.length, 26 + a ∈ (gateAt C k).inputs → k = r0 := by
        intro k hk_lt hk_mem
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact htwo k hk_lt r0 hr0_lt hlt hk_mem hr0_mem
        · exact htwo r0 hr0_lt k hk_lt hgt hr0_mem hk_mem
      have hr0_or : (gateAt C r0).op = GateOp.or := hall_or r0 hr0_lt hr0_mem
      have hr0_lt_b : r0 < b := by
        by_contra hge
        have heq : r0 = b := by omega
        rw [heq, hbAnd] at hr0_or
        cases hr0_or
      exact no_unique_or_reader_pg l0 C a b r0 hV hMinPairs hBin har0 hr0_lt_b hb_lt
        haAnd hbAnd hCone haZero hr0_or hr0_mem huniq

end PEqualNP.Outside.L_meta_7295

theorem PEqualNP.Outside.L_meta_7295 :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : Fin (13 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : Fin (13 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x5 ∈ x1 x6 → x5 ≠ (0 : Fin (13 : ℕ)) ∨ x6 ≠ x3 → x4.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x5 → x4.eval (x2 x5) = Bool.false; ∀ (x4 : Fin (13 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 x5 → (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 x7 → x5.size ≤ x7.size) → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 x8 → x8.size = x5.size → PEqualNP.TopForm.andPairs (26 : ℕ) x5 ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x8) → (∀ x9 ∈ x5.gates, x9.inputs.length = (2 : ℕ) ∧ x9.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x9.inputs.getD (1 : ℕ) (0 : ℕ)) ∧ ∀ (x9 x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x9 x10 → ∃ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x14 ∧ (x5.wires (x2 x14)).getD ((26 : ℕ) + x9) Bool.false = Bool.true := by
  dsimp only
  intro l0 C hV hMin hMinPairs
  have hBin := PEqualNP.Outside.L_meta_7295.part1_distinct_binary l0 C hV hMin
  exact ⟨hBin, PEqualNP.Outside.L_meta_7295.part2_stacked_and_fires l0 C hV hMin hMinPairs hBin⟩
