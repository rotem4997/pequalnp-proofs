import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6975

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def shiftG (k j : ℕ) : ℕ :=
  if j < k then j else j - 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega

lemma shiftW_inj (n k a b : ℕ) (ha : a ≠ n + k) (hb : b ≠ n + k)
    (h : shiftW n k a = shiftW n k b) : a = b := by
  unfold shiftW at h
  split_ifs at h <;> omega

lemma unshiftW_inj (n k a b : ℕ) (h : unshiftW n k a = unshiftW n k b) : a = b := by
  unfold unshiftW at h
  split_ifs at h <;> omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq_getElem (delDead n k C) j hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq_getElem C j (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq_getElem C (j + 1) (by omega)]

lemma delDead_monotone2 (n k : ℕ) (C : Circuit) (hM : Monotone2 C) :
    Monotone2 (delDead n k C) := by
  intro g hg
  simp only [delDead, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have h0 := hM g0 (List.mem_of_mem_eraseIdx hg0)
  exact ⟨h0.1, by simp [shiftGate, h0.2]⟩

lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega

lemma delDead_binary (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs)
    (hbin : ∀ j < C.gates.length, j ≠ k → ∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a, b]) :
    ∀ j < (delDead n k C).gates.length,
      ∃ a b, a ≠ b ∧ (gateAt (delDead n k C) j).inputs = [a, b] := by
  intro j hj
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hj0_ne : unshiftG k j ≠ k := by
    unfold unshiftG; split_ifs <;> omega
  obtain ⟨a0, b0, hab, hin⟩ := hbin (unshiftG k j) hj0_lt hj0_ne
  have ha0 : a0 ≠ n + k := by
    intro heq
    apply hno (unshiftG k j) hj0_lt
    rw [hin, heq]
    simp
  have hb0 : b0 ≠ n + k := by
    intro heq
    apply hno (unshiftG k j) hj0_lt
    rw [hin, heq]
    simp
  refine ⟨shiftW n k a0, shiftW n k b0, ?_, ?_⟩
  · intro heq
    exact hab (shiftW_inj n k a0 b0 ha0 hb0 heq)
  · rw [delDead_gateAt n k C hk j hj]
    simp only [shiftGate, hin, List.map_cons, List.map_nil]

def evalStep {α : Type} (d0 : α) (evalG : GateOp → List α → α) (acc : List α) (g : Gate) :
    List α :=
  acc ++ [evalG g.op (g.inputs.map fun i => acc.getD i d0)]

lemma foldl_evalStep_length {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) :
    (gs.foldl (evalStep d0 evalG) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_prefix {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl (evalStep d0 evalG) acc).getD w d0 = acc.getD w d0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (evalStep d0 evalG acc g).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (evalStep d0 evalG acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_left hw]

lemma foldl_evalStep_gate {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG (gateAt C j).op
        ((gateAt C j).inputs.map fun u => (C.gates.foldl (evalStep d0 evalG) init).getD u d0) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (evalStep d0 evalG) init with hacc
  have hacc_len : acc.length = n + j := by
    rw [hacc, foldl_evalStep_length, hinit, List.length_take]
    omega
  have hpref : ∀ u < n + j,
      (C.gates.foldl (evalStep d0 evalG) init).getD u d0 = acc.getD u d0 := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_evalStep_prefix d0 evalG (C.gates.drop j) acc u (by omega)
  have hval : (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG C.gates[j].op (C.gates[j].inputs.map fun u => acc.getD u d0) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + j < (evalStep d0 evalG acc C.gates[j]).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_evalStep_prefix d0 evalG (C.gates.drop (j + 1)) (evalStep d0 evalG acc C.gates[j])
      (n + j) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_right (by omega : acc.length ≤ n + j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C j hj] at hu
  exact (hpref u (hRB j hj u hu)).symm

lemma delDead_evalStep_eq {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n k : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ w : ℕ,
      ((delDead n k C).gates.foldl (evalStep d0 evalG) init).getD w d0 =
        (C.gates.foldl (evalStep d0 evalG) init).getD (unshiftW n k w) d0 := by
  have hRB' : ReadsBack n (delDead n k C) := delDead_readsBack n k C hRB hk hno
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_oob : n + (delDead n k C).gates.length ≤ w
    · have hlen' : ((delDead n k C).gates.foldl (evalStep d0 evalG) init).length =
          n + (delDead n k C).gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hlen : (C.gates.foldl (evalStep d0 evalG) init).length = n + C.gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hdl := delDead_length n k C hk
      have huw : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hw_oob
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw]
        rw [foldl_evalStep_prefix d0 evalG (delDead n k C).gates init w (by omega)]
        rw [foldl_evalStep_prefix d0 evalG C.gates init w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (delDead n k C).gates.length := by omega
        have hdl := delDead_length n k C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [foldl_evalStep_gate d0 evalG n (delDead n k C) init hinit hRB' j hj_lt]
        rw [foldl_evalStep_gate d0 evalG n C init hinit hRB (unshiftG k j) hj0_lt]
        rw [delDead_gateAt n k C hk j hj_lt]
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : shiftW n k u < n + j := by
          have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
            rw [delDead_gateAt n k C hk j hj_lt]
            simp only [shiftGate, List.mem_map]
            exact ⟨u, hu, rfl⟩
          exact hRB' j hj_lt (shiftW n k u) hmem
        have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
        simp only [Function.comp_apply]
        rw [ih (shiftW n k u) (by omega), unshiftW_shiftW n k u hu_ne]

lemma delDead_wires_eq (n k : ℕ) (C : Circuit) (l : List Bool) (hl : l.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (w : ℕ) :
    ((delDead n k C).wires l).getD w false = (C.wires l).getD (unshiftW n k w) false :=
  delDead_evalStep_eq false GateOp.eval n k C l hl hRB hk hno w

def lineDegEval (op : GateOp) (xs : List ℕ) : ℕ :=
  @ite ℕ (op = GateOp.and) (lineDegreeGateOpDecEq op GateOp.and) xs.sum (xs.foldr max 0)

lemma delDead_lineDegrees_eq (n k : ℕ) (C : Circuit) (S : Finset ℕ)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (w : ℕ) :
    ((delDead n k C).lineDegrees n S).getD w 0 =
      (C.lineDegrees n S).getD (unshiftW n k w) 0 := by
  have hinit : ((List.range n).map fun i => if i ∈ S then 1 else 0).length = n := by simp
  exact delDead_evalStep_eq 0 lineDegEval n k C
    ((List.range n).map fun i => if i ∈ S then 1 else 0) hinit hRB hk hno w

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

lemma delDead_inCone (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (hk_in : (gateAt C k).inputs = [])
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ b < C.gates.length, ∀ a, InCone n C a b →
      a < b ∧ a ≠ k ∧ b ≠ k ∧ InCone n (delDead n k C) (shiftG k a) (shiftG k b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro hb a hab
    rw [inCone_iff n C a b hb] at hab
    obtain ⟨w, hw, hnw, hwlt, hcase⟩ := hab
    have hbk : b ≠ k := by
      intro hEq
      rw [hEq, hk_in] at hw
      cases hw
    have hwk : w ≠ n + k := fun hEq => hno b hb (hEq ▸ hw)
    have hdl := delDead_length n k C hk
    have hb'_lt : shiftG k b < (delDead n k C).gates.length := by
      unfold shiftG; split_ifs <;> omega
    have hun_b : unshiftG k (shiftG k b) = b := by
      unfold unshiftG shiftG; split_ifs <;> omega
    have hw'_mem : shiftW n k w ∈ (gateAt (delDead n k C) (shiftG k b)).inputs := by
      rw [delDead_gateAt n k C hk (shiftG k b) hb'_lt, hun_b]
      simp only [shiftGate, List.mem_map]
      exact ⟨w, hw, rfl⟩
    have hw'_ge : n ≤ shiftW n k w := by
      unfold shiftW; split_ifs <;> omega
    have hw'_lt : shiftW n k w < n + shiftG k b := by
      unfold shiftW shiftG; split_ifs <;> omega
    have hw'_sub : shiftW n k w - n = shiftG k (w - n) := by
      unfold shiftW shiftG; split_ifs <;> omega
    rcases hcase with rfl | hcone
    · refine ⟨by omega, by omega, hbk, ?_⟩
      rw [inCone_iff n (delDead n k C) (shiftG k (w - n)) (shiftG k b) hb'_lt]
      exact ⟨shiftW n k w, hw'_mem, hw'_ge, hw'_lt, Or.inl hw'_sub.symm⟩
    · have hwm_lt : w - n < b := by omega
      obtain ⟨haw, hak, _, hcone'⟩ := ih (w - n) hwm_lt (by omega) a hcone
      refine ⟨by omega, hak, hbk, ?_⟩
      rw [inCone_iff n (delDead n k C) (shiftG k a) (shiftG k b) hb'_lt]
      refine ⟨shiftW n k w, hw'_mem, hw'_ge, hw'_lt, Or.inr ?_⟩
      rw [hw'_sub]
      exact hcone'

lemma delDead_gateAt_op_shift (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < C.gates.length) (hne : j ≠ k) :
    (gateAt (delDead n k C) (shiftG k j)).op = (gateAt C j).op := by
  have hdl := delDead_length n k C hk
  have hj'_lt : shiftG k j < (delDead n k C).gates.length := by
    unfold shiftG; split_ifs <;> omega
  rw [delDead_gateAt n k C hk (shiftG k j) hj'_lt]
  have hun : unshiftG k (shiftG k j) = j := by
    unfold unshiftG shiftG; split_ifs <;> omega
  rw [hun]
  rfl

end PEqualNP.Outside.L_meta_6975

theorem PEqualNP.Outside.L_meta_6975 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool → List Bool → Prop) (x4 : ℕ),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x6 < x5.size, ∀ x8 ≤ x1 + x6, ∃ (x10 : Bool) (x11 : List Bool), x3 x10 x11 ∧ (x5.wires x11).getD (x1 + x6) Bool.false = x10 ∧ (if x8 = x1 + x6 then Bool.false else (x5.wires x11).getD x8 Bool.false) = !x10;   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x7 : ℕ) (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone x1 x6 x7 x8;   (∀ (x7 : Bool) (x8 : List Bool), x3 x7 x8 → x8.length = x1) → PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x4 < x2.size → x2.output ≠ x1 + x4 → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).inputs = [] → (∀ x13 < x2.size, x1 + x4 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs) → (∀ x14 < x2.size, x14 ≠ x4 → ∃ (x17 : ℕ) (x18 : ℕ), x17 ≠ x18 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs = [x17, x18]) → x5 x2 → x6 x2 → ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size + (1 : ℕ) = x2.size ∧ PEqualNP.MetaComplexity.Monotone2 x17 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x17 ∧ (∀ x18 < x17.size, ∃ (x20 : ℕ) (x21 : ℕ), x20 ≠ x21 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x17 x18).inputs = [x20, x21]) ∧ (∀ (x18 : List Bool), x18.length = x1 → x17.eval x18 = x2.eval x18) ∧ (∀ (x18 : Finset ℕ), x17.lineDeg x1 x18 = x2.lineDeg x1 x18) ∧ x5 x17 ∧ x6 x17 := by
  intro n C P k x5 x6 hPlen hM hRB hk hout hk_in hno hbin hx5 hx6
  refine ⟨PEqualNP.Outside.L_meta_6975.delDead n k C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_6975.delDead_size n k C hk
  · exact PEqualNP.Outside.L_meta_6975.delDead_monotone2 n k C hM
  · exact PEqualNP.Outside.L_meta_6975.delDead_readsBack n k C hRB hk hno
  · exact PEqualNP.Outside.L_meta_6975.delDead_binary n k C hk hno hbin
  · intro l hl
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_6975.delDead_wires_eq n k C l hl hRB hk hno]
    simp only [PEqualNP.Outside.L_meta_6975.delDead]
    rw [PEqualNP.Outside.L_meta_6975.unshiftW_shiftW n k C.output hout]
  · intro S
    unfold PEqualNP.CircuitLowerBounds.Circuit.lineDeg
    rw [PEqualNP.Outside.L_meta_6975.delDead_lineDegrees_eq n k C S hRB hk hno]
    simp only [PEqualNP.Outside.L_meta_6975.delDead]
    rw [PEqualNP.Outside.L_meta_6975.unshiftW_shiftW n k C.output hout]
  · intro j hj w hw
    have hsz := PEqualNP.Outside.L_meta_6975.delDead_size n k C hk
    set j0 := PEqualNP.Outside.L_meta_6975.unshiftG k j with hj0_def
    have hj0_lt : j0 < C.size := by
      rw [hj0_def]; unfold PEqualNP.Outside.L_meta_6975.unshiftG; split_ifs <;> omega
    set w0 := PEqualNP.Outside.L_meta_6975.unshiftW n k w with hw0_def
    have huw_j : PEqualNP.Outside.L_meta_6975.unshiftW n k (n + j) = n + j0 := by
      rw [hj0_def]
      unfold PEqualNP.Outside.L_meta_6975.unshiftW PEqualNP.Outside.L_meta_6975.unshiftG
      split_ifs <;> omega
    have hw0_le : w0 ≤ n + j0 := by
      rw [hw0_def, hj0_def]
      unfold PEqualNP.Outside.L_meta_6975.unshiftW PEqualNP.Outside.L_meta_6975.unshiftG
      split_ifs <;> omega
    obtain ⟨b, l, hP, h1, h2⟩ := hx5 j0 hj0_lt w0 hw0_le
    have hl : l.length = n := hPlen b l hP
    refine ⟨b, l, hP, ?_, ?_⟩
    · rw [PEqualNP.Outside.L_meta_6975.delDead_wires_eq n k C l hl hRB hk hno, huw_j]
      exact h1
    · have hiff : w = n + j ↔ w0 = n + j0 := by
        constructor
        · intro heq; rw [hw0_def, heq, huw_j]
        · intro heq
          rw [hw0_def, ← huw_j] at heq
          exact PEqualNP.Outside.L_meta_6975.unshiftW_inj n k w (n + j) heq
      rw [PEqualNP.Outside.L_meta_6975.delDead_wires_eq n k C l hl hRB hk hno]
      by_cases hweq : w = n + j
      · have hw0eq : w0 = n + j0 := hiff.mp hweq
        simp only [hweq, hw0eq, ↓reduceIte] at h2 ⊢
        exact h2
      · have hw0ne : w0 ≠ n + j0 := fun h => hweq (hiff.mpr h)
        simp only [hweq, hw0ne, ↓reduceIte] at h2 ⊢
        exact h2
  · obtain ⟨a, b, ha_op, hb_op, hab⟩ := hx6
    have hb_lt : b < C.gates.length := PEqualNP.Outside.L_meta_6975.inCone_lt_size n C a b hab
    obtain ⟨hab_lt, hak, hbk, hcone'⟩ :=
      PEqualNP.Outside.L_meta_6975.delDead_inCone n k C hk hk_in hno b hb_lt a hab
    refine ⟨PEqualNP.Outside.L_meta_6975.shiftG k a, PEqualNP.Outside.L_meta_6975.shiftG k b,
      ?_, ?_, hcone'⟩
    · rw [PEqualNP.Outside.L_meta_6975.delDead_gateAt_op_shift n k C hk a (by omega) hak]
      exact ha_op
    · rw [PEqualNP.Outside.L_meta_6975.delDead_gateAt_op_shift n k C hk b hb_lt hbk]
      exact hb_op
