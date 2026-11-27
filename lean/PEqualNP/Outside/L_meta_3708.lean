import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3708

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

def foldAppend {α β : Type} (step : List α → β → α) (init : List α) (l : List β) : List α :=
  l.foldl (fun acc b => acc ++ [step acc b]) init

lemma foldAppend_cons {α β : Type} (step : List α → β → α) (init : List α) (b : β) (bs : List β) :
    foldAppend step init (b :: bs) = foldAppend step (init ++ [step init b]) bs :=
  rfl

lemma foldAppend_length {α β : Type} (step : List α → β → α) (init : List α) (l : List β) :
    (foldAppend step init l).length = init.length + l.length := by
  induction l generalizing init with
  | nil => simp [foldAppend]
  | cons b bs ih =>
    rw [foldAppend_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma foldAppend_append {α β : Type} (step : List α → β → α) (init : List α) (l1 l2 : List β) :
    foldAppend step init (l1 ++ l2) = foldAppend step (foldAppend step init l1) l2 := by
  simp [foldAppend, List.foldl_append]

lemma foldAppend_getD_lt {α β : Type} (step : List α → β → α) (init : List α) (l : List β)
    (i : ℕ) (d : α) (hi : i < init.length) :
    (foldAppend step init l).getD i d = init.getD i d := by
  induction l generalizing init with
  | nil => rfl
  | cons b bs ih =>
    rw [foldAppend_cons]
    have hi' : i < (init ++ [step init b]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [ih (init ++ [step init b]) hi']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldAppend_take_getD {α β : Type} (step : List α → β → α) (init : List α) (l : List β)
    (j i : ℕ) (d : α) (hj : j ≤ l.length) (hi : i < init.length + j) :
    (foldAppend step init (l.take j)).getD i d = (foldAppend step init l).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, foldAppend_append]
  have hlen : (foldAppend step init (l.take j)).length = init.length + j := by
    rw [foldAppend_length, List.length_take, Nat.min_eq_left hj]
  exact (foldAppend_getD_lt step (foldAppend step init (l.take j)) (l.drop j) i d (hlen ▸ hi)).symm

lemma foldAppend_getD_add {α β : Type} (step : List α → β → α) (init : List α) (l : List β)
    (j : ℕ) (d : α) (hj : j < l.length) :
    (foldAppend step init l).getD (init.length + j) d =
      step (foldAppend step init (l.take j)) l[j] := by
  have hdrop : l.drop j = l[j] :: l.drop (j + 1) :=
    (List.cons_getElem_drop_succ (h := hj)).symm
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    rw [← hdrop, List.take_append_drop]
  conv_lhs => rw [hsplit, foldAppend_append, foldAppend_cons]
  set acc := foldAppend step init (l.take j)
  have hlen : acc.length = init.length + j := by
    change (foldAppend step init (l.take j)).length = init.length + j
    rw [foldAppend_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : init.length + j < (acc ++ [step acc l[j]]).length := by
    rw [List.length_append, List.length_singleton, hlen]; omega
  rw [foldAppend_getD_lt step (acc ++ [step acc l[j]]) (l.drop (j + 1)) (init.length + j) d hlt]
  simp [List.getD_eq_getElem?_getD, hlen]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_inputs_length_two {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs.length = 2 := by
  rw [gateAt_eq_getElem C j hj]
  exact hAO.2.2 C.gates[j] (List.getElem_mem hj)

lemma gateAt_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen := gateAt_inputs_length_two hAO hj
  cases h : (gateAt C j).inputs with
  | nil => simp [h] at hlen
  | cons w0 t =>
    cases t with
    | nil => simp [h] at hlen
    | cons w1 t' =>
      cases t' with
      | nil => simp [opnd, h]
      | cons _ _ => simp [h] at hlen

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j := by
  have hmem : opnd C j b ∈ (gateAt C j).inputs := by
    rw [gateAt_inputs_eq hAO hj]
    fin_cases b <;> simp
  exact hAO.2.1 j hj (opnd C j b) hmem

lemma gateAt_op_and_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  rw [gateAt_eq_getElem C j hj]
  exact hAO.1 C.gates[j] (List.getElem_mem hj)

lemma wires_eq_foldAppend (C : Circuit) (x : List Bool) :
    C.wires x =
      foldAppend (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates :=
  rfl

lemma wires_getD_lt (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldAppend_getD_lt _ x C.gates i false hi

lemma wires_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : List Bool)
    (hx : x.length = n) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval
        [(C.wires x).getD (opnd C j 0) false, (C.wires x).getD (opnd C j 1) false] := by
  have h := foldAppend_getD_add
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates j false hj
  rw [hx] at h
  change (foldAppend (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates).getD
      (n + j) false = _
  rw [h, ← gateAt_eq_getElem C j hj, gateAt_inputs_eq hAO hj]
  simp only [List.map_cons, List.map_nil]
  have h0 : (foldAppend (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x
      (C.gates.take j)).getD (opnd C j 0) false = (C.wires x).getD (opnd C j 0) false :=
    foldAppend_take_getD _ x C.gates j (opnd C j 0) false (Nat.le_of_lt hj)
      (by rw [hx]; exact opnd_lt hAO hj 0)
  have h1 : (foldAppend (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x
      (C.gates.take j)).getD (opnd C j 1) false = (C.wires x).getD (opnd C j 1) false :=
    foldAppend_take_getD _ x C.gates j (opnd C j 1) false (Nat.le_of_lt hj)
      (by rw [hx]; exact opnd_lt hAO hj 1)
  rw [h0, h1]

def orStepElem (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  cs.length :: (@ite (List ℕ) (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
    ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => cs.getD (w - n) []))
    [])

lemma orSets_eq_foldAppend (n : ℕ) (C : Circuit) :
    orSets n C = foldAppend (orStepElem n) [] C.gates :=
  rfl

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  rw [orSets_eq_foldAppend, foldAppend_length]
  simp

lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; exact hj)]
  rfl

lemma orSets_getD_lt (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (orSets n C).getD j [] =
      j :: (match (gateAt C j).op with
        | GateOp.or =>
          ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
            (fun w => (orSets n C).getD (w - n) [])
        | _ => []) := by
  change (foldAppend (orStepElem n) [] C.gates).getD j [] = _
  have h := foldAppend_getD_add (orStepElem n) [] C.gates j [] hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq_getElem C j hj]
  set prev := foldAppend (orStepElem n) [] (C.gates.take j)
  have hlen : prev.length = j := by
    change (foldAppend (orStepElem n) [] (C.gates.take j)).length = j
    rw [foldAppend_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold orStepElem
  rw [hlen]
  congr 1
  cases hop : (gateAt C j).op with
  | or =>
    change ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
      (fun w => prev.getD (w - n) []) = _
    apply List.flatMap_congr
    intro w hw
    rw [List.mem_filter] at hw
    have hwn : n ≤ w ∧ w < n + j := of_decide_eq_true hw.2
    have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
    exact foldAppend_take_getD (orStepElem n) [] C.gates j (w - n) [] (Nat.le_of_lt hj) hlt
  | and => rfl
  | not => rfl
  | mod _ => rfl
  | maj => rfl

lemma orReaches_lt_n (n : ℕ) (C : Circuit) {w a : ℕ} (hw : w < n) :
    ¬ OrReaches n C w a := by
  intro ⟨h1, _⟩
  omega

lemma orReaches_ge (n : ℕ) (C : Circuit) {w a : ℕ} (hw : n + C.gates.length ≤ w) :
    ¬ OrReaches n C w a := by
  intro ⟨h1, h2⟩
  rw [orSets_getD_ge n C (by omega)] at h2
  simp at h2

lemma orReaches_and {n : ℕ} {C : Circuit} {j a : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    OrReaches n C (n + j) a ↔ a = j := by
  unfold OrReaches
  rw [Nat.add_sub_cancel_left, orSets_getD_lt n C hj, hop]
  simp

lemma orReaches_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j a : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    OrReaches n C (n + j) a ↔
      a = j ∨ OrReaches n C (opnd C j 0) a ∨ OrReaches n C (opnd C j 1) a := by
  unfold OrReaches
  rw [Nat.add_sub_cancel_left, orSets_getD_lt n C hj, hop]
  simp only [Nat.le_add_right, true_and, List.mem_cons, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq]
  rw [gateAt_inputs_eq hAO hj]
  constructor
  · intro h
    rcases h with rfl | ⟨w, ⟨hw, h1, _⟩, hmem⟩
    · exact Or.inl rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inr (Or.inl ⟨h1, hmem⟩)
      · exact Or.inr (Or.inr ⟨h1, hmem⟩)
  · intro h
    rcases h with rfl | ⟨h1, hmem⟩ | ⟨h1, hmem⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨opnd C j 0, ⟨by simp, h1, opnd_lt hAO hj 0⟩, hmem⟩
    · exact Or.inr ⟨opnd C j 1, ⟨by simp, h1, opnd_lt hAO hj 1⟩, hmem⟩

lemma mem_orIn_lt (n : ℕ) (C : Circuit) {w : ℕ} (hw : w < n) (i : Fin n) :
    i ∈ orIn n C w ↔ (i : ℕ) = w := by
  simp [orIn, orReaches_lt_n n C hw]

lemma mem_orIn_ge (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w) (i : Fin n) :
    i ∉ orIn n C w := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and]
  refine ⟨by omega, fun k _ hreach _ _ => orReaches_ge n C hw hreach⟩

lemma mem_orIn_and {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (i : Fin n) :
    i ∉ orIn n C (n + j) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and]
  refine ⟨by omega, fun k _ hreach hkop _ => ?_⟩
  have hk : k = j := (orReaches_and hj hop).mp hreach
  subst hk
  rw [hop] at hkop
  cases hkop

lemma mem_orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (i : Fin n) :
    i ∈ orIn n C (n + j) ↔ i ∈ orIn n C (opnd C j 0) ∨ i ∈ orIn n C (opnd C j 1) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (i : ℕ) ≠ n + j := by omega
  simp only [hne, false_or]
  constructor
  · rintro ⟨k, hk, hreach, hkop, hmem⟩
    rcases (orReaches_or hAO hj hop).mp hreach with rfl | h0 | h1
    · rw [gateAt_inputs_eq hAO hj] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (Or.inl h1)
    · exact Or.inl (Or.inr ⟨k, hk, h0, hkop, hmem⟩)
    · exact Or.inr (Or.inr ⟨k, hk, h1, hkop, hmem⟩)
  · rintro (h0 | h1)
    · rcases h0 with heq | ⟨k, hk, hreach, hkop, hmem⟩
      · refine ⟨j, hj, (orReaches_or hAO hj hop).mpr (Or.inl rfl), hop, ?_⟩
        rw [gateAt_inputs_eq hAO hj, heq]
        simp
      · exact ⟨k, hk, (orReaches_or hAO hj hop).mpr (Or.inr (Or.inl hreach)), hkop, hmem⟩
    · rcases h1 with heq | ⟨k, hk, hreach, hkop, hmem⟩
      · refine ⟨j, hj, (orReaches_or hAO hj hop).mpr (Or.inl rfl), hop, ?_⟩
        rw [gateAt_inputs_eq hAO hj, heq]
        simp
      · exact ⟨k, hk, (orReaches_or hAO hj hop).mpr (Or.inr (Or.inr hreach)), hkop, hmem⟩

lemma orIn_implies_wires_single {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (u : Fin n) :
    ∀ w : ℕ, u ∈ orIn n C w →
      (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hu
    by_cases hw : w < n
    · have heq : (u : ℕ) = w := (mem_orIn_lt n C hw u).mp hu
      have hxlen : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := List.length_ofFn
      rw [wires_getD_lt C _ w (by rw [hxlen]; exact hw)]
      simp [← heq, List.getD_eq_getElem?_getD]
    · by_cases hge : n + C.gates.length ≤ w
      · exact (mem_orIn_ge n C hge u hu).elim
      · have hj : w - n < C.gates.length := by omega
        have hwj : w = n + (w - n) := by omega
        rw [hwj] at hu ⊢
        rcases gateAt_op_and_or hAO hj with hand | hor
        · exact (mem_orIn_and hj hand u hu).elim
        · have hxlen : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := List.length_ofFn
          rw [wires_getD_gate hAO _ hxlen hj, hor]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            Bool.or_eq_true]
          rcases (mem_orIn_or hAO hj hor u).mp hu with h0 | h1
          · exact Or.inl (ih (opnd C (w - n) 0) (by have := opnd_lt hAO hj 0; omega) h0)
          · exact Or.inr (ih (opnd C (w - n) 1) (by have := opnd_lt hAO hj 1; omega) h1)

lemma mem_insertNew (acc : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew acc v ↔ x ∈ acc ∨ x = v := by
  unfold insertNew
  split_ifs with hv
  · constructor
    · intro hx; exact Or.inl hx
    · rintro (hx | rfl)
      · exact hx
      · exact hv
  · simp

lemma mem_foldl_insertNew (l acc : List (List ℕ)) (x : List ℕ) :
    x ∈ l.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih (insertNew acc v), mem_insertNew]
    tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = w := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp

def rvStep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma readVectors_eq_foldAppend (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k =
      foldAppend (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates :=
  rfl

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  rw [readVectors_eq_foldAppend, foldAppend_length, List.length_map, List.length_range]

lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k i : ℕ) (hi : i < n) :
    (readVectors C n S k).getD i [] = leafVectors S k i := by
  rw [readVectors_eq_foldAppend]
  have hlen : ((List.range n).map (leafVectors S k)).length = n := by simp
  rw [foldAppend_getD_lt _ _ C.gates i [] (by rw [hlen]; exact hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma readVectors_getD_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k w : ℕ)
    (hw : n + C.gates.length ≤ w) :
    (readVectors C n S k).getD w [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [readVectors_length]; exact hw)]
  rfl

lemma readVectors_getD_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : List ℕ) (k : ℕ)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (vec : List ℕ) :
    vec ∈ (readVectors C n S k).getD (n + j) [] ↔
      vec ∈ (readVectors C n S k).getD (opnd C j 0) [] ∨
      vec ∈ (readVectors C n S k).getD (opnd C j 1) [] := by
  change vec ∈ (foldAppend (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates).getD
      (n + j) [] ↔ _
  have hinit : ((List.range n).map (leafVectors S k)).length = n := by simp
  have h := foldAppend_getD_add (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates j [] hj
  rw [hinit] at h
  rw [h, ← gateAt_eq_getElem C j hj]
  set prev := foldAppend (rvStep S k) ((List.range n).map (leafVectors S k)) (C.gates.take j)
  unfold rvStep
  rw [gateAt_inputs_eq hAO hj, hop]
  have h0 : prev.getD (opnd C j 0) [] = (readVectors C n S k).getD (opnd C j 0) [] :=
    foldAppend_take_getD (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates j
      (opnd C j 0) [] (Nat.le_of_lt hj) (by rw [hinit]; exact opnd_lt hAO hj 0)
  have h1 : prev.getD (opnd C j 1) [] = (readVectors C n S k).getD (opnd C j 1) [] :=
    foldAppend_take_getD (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates j
      (opnd C j 1) [] (Nat.le_of_lt hj) (by rw [hinit]; exact opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [h0, h1, mem_foldl_insertNew, mem_foldl_insertNew]
  simp

lemma readVectors_getD_and_raw {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : List ℕ) (k : ℕ)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (vec : List ℕ) :
    vec ∈ (readVectors C n S k).getD (n + j) [] ↔
      ∃ p ∈ (readVectors C n S k).getD (opnd C j 0) [],
      ∃ q ∈ (readVectors C n S k).getD (opnd C j 1) [],
        capAdd k (capAdd k (S.map fun _ => 0) p) q = vec := by
  change vec ∈ (foldAppend (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates).getD
      (n + j) [] ↔ _
  have hinit : ((List.range n).map (leafVectors S k)).length = n := by simp
  have h := foldAppend_getD_add (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates j [] hj
  rw [hinit] at h
  rw [h, ← gateAt_eq_getElem C j hj]
  set prev := foldAppend (rvStep S k) ((List.range n).map (leafVectors S k)) (C.gates.take j)
  unfold rvStep
  rw [gateAt_inputs_eq hAO hj, hop]
  have h0 : prev.getD (opnd C j 0) [] = (readVectors C n S k).getD (opnd C j 0) [] :=
    foldAppend_take_getD (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates j
      (opnd C j 0) [] (Nat.le_of_lt hj) (by rw [hinit]; exact opnd_lt hAO hj 0)
  have h1 : prev.getD (opnd C j 1) [] = (readVectors C n S k).getD (opnd C j 1) [] :=
    foldAppend_take_getD (rvStep S k) ((List.range n).map (leafVectors S k)) C.gates j
      (opnd C j 1) [] (Nat.le_of_lt hj) (by rw [hinit]; exact opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [h0, h1, mem_andStep]
  simp only [mem_andStep, List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨r, ⟨p, hp, rfl⟩, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨capAdd k (S.map fun _ => 0) p, ⟨p, hp, rfl⟩, q, hq, rfl⟩

lemma readVectors_shape {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} (huv : u ≠ v) :
    ∀ w : ℕ, ∀ vec ∈ (readVectors C n [u.val, v.val] 1).getD w [],
      ∃ a b : ℕ, vec = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ (1 ≤ a ∨ 1 ≤ b) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro vec hvec
    by_cases hw : w < n
    · rw [readVectors_getD_lt C n [u.val, v.val] 1 w hw] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton] at hvec
        subst hvec
        rcases hmem with rfl | rfl
        · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
          refine ⟨1, 0, ?_, by omega, by omega, Or.inl (by omega)⟩
          simp [hne]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          refine ⟨0, 1, ?_, by omega, by omega, Or.inr (by omega)⟩
          simp [hne]
      · simp at hvec
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [u.val, v.val] 1 w hge] at hvec
        simp at hvec
      · have hj : w - n < C.gates.length := by omega
        have hwj : w = n + (w - n) := by omega
        rw [hwj] at hvec
        rcases gateAt_op_and_or hAO hj with hand | hor
        · rcases (readVectors_getD_and_raw hAO [u.val, v.val] 1 hj hand vec).mp hvec with
            ⟨p, hp, q, hq, rfl⟩
          rcases ih (opnd C (w - n) 0) (by have := opnd_lt hAO hj 0; omega) p hp with
            ⟨a1, b1, rfl, ha1, hb1, hpos1⟩
          rcases ih (opnd C (w - n) 1) (by have := opnd_lt hAO hj 1; omega) q hq with
            ⟨a2, b2, rfl, ha2, hb2, hpos2⟩
          refine ⟨min (min a1 2 + a2) 2, min (min b1 2 + b2) 2, ?_,
            Nat.min_le_right _ _, Nat.min_le_right _ _, ?_⟩
          · simp [capAdd]
          · rcases hpos1 with h | h
            · left; omega
            · right; omega
        · rcases (readVectors_getD_or hAO [u.val, v.val] 1 hj hor vec).mp hvec with h0 | h1
          · exact ih (opnd C (w - n) 0) (by have := opnd_lt hAO hj 0; omega) vec h0
          · exact ih (opnd C (w - n) 1) (by have := opnd_lt hAO hj 1; omega) vec h1

lemma readVectors_getD_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} (huv : u ≠ v)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (vec : List ℕ) :
    vec ∈ (readVectors C n [u.val, v.val] 1).getD (n + j) [] ↔
      ∃ p ∈ (readVectors C n [u.val, v.val] 1).getD (opnd C j 0) [],
      ∃ q ∈ (readVectors C n [u.val, v.val] 1).getD (opnd C j 1) [],
        capAdd 1 p q = vec := by
  rw [readVectors_getD_and_raw hAO [u.val, v.val] 1 hj hop vec]
  constructor
  · rintro ⟨p, hp, q, hq, hcap⟩
    rcases readVectors_shape hAO huv (opnd C j 0) p hp with ⟨a, b, rfl, ha, hb, _⟩
    have hsimp : capAdd 1 ([u.val, v.val].map fun _ => 0) [a, b] = [a, b] := by
      simp [capAdd, Nat.min_eq_left ha, Nat.min_eq_left hb]
    rw [hsimp] at hcap
    exact ⟨[a, b], hp, q, hq, hcap⟩
  · rintro ⟨p, hp, q, hq, hcap⟩
    rcases readVectors_shape hAO huv (opnd C j 0) p hp with ⟨a, b, rfl, ha, hb, _⟩
    have hsimp : capAdd 1 ([u.val, v.val].map fun _ => 0) [a, b] = [a, b] := by
      simp [capAdd, Nat.min_eq_left ha, Nat.min_eq_left hb]
    exact ⟨[a, b], hp, q, hq, by rw [hsimp]; exact hcap⟩

lemma mem_readVectors_10 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} (huv : u ≠ v) :
    ∀ w : ℕ, [1, 0] ∈ (readVectors C n [u.val, v.val] 1).getD w [] ↔ u ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [readVectors_getD_lt C n [u.val, v.val] 1 w hw, mem_orIn_lt n C hw u]
      unfold leafVectors
      split_ifs with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton]
        rcases hmem with rfl | rfl
        · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
          simp [hne]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          simp [hne]
      · simp only [List.not_mem_nil, false_iff]
        intro heq
        exact hmem (by simp [← heq])
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [u.val, v.val] 1 w hge]
        simp [mem_orIn_ge n C hge u]
      · have hj : w - n < C.gates.length := by omega
        have hwj : w = n + (w - n) := by omega
        rw [hwj]
        rcases gateAt_op_and_or hAO hj with hand | hor
        · simp only [mem_orIn_and hj hand u, iff_false]
          intro hmem
          rcases (readVectors_getD_and hAO huv hj hand [1, 0]).mp hmem with ⟨p, hp, q, hq, hcap⟩
          rcases readVectors_shape hAO huv (opnd C (w - n) 0) p hp with
            ⟨a1, b1, rfl, ha1, hb1, hpos1⟩
          rcases readVectors_shape hAO huv (opnd C (w - n) 1) q hq with
            ⟨a2, b2, rfl, ha2, hb2, hpos2⟩
          simp [capAdd] at hcap
          omega
        · rw [readVectors_getD_or hAO [u.val, v.val] 1 hj hor [1, 0], mem_orIn_or hAO hj hor u]
          rw [ih (opnd C (w - n) 0) (by have := opnd_lt hAO hj 0; omega)]
          rw [ih (opnd C (w - n) 1) (by have := opnd_lt hAO hj 1; omega)]

lemma mem_readVectors_01 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} (huv : u ≠ v) :
    ∀ w : ℕ, [0, 1] ∈ (readVectors C n [u.val, v.val] 1).getD w [] ↔ v ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [readVectors_getD_lt C n [u.val, v.val] 1 w hw, mem_orIn_lt n C hw v]
      unfold leafVectors
      split_ifs with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton]
        rcases hmem with rfl | rfl
        · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
          simp [hne]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          simp [hne]
      · simp only [List.not_mem_nil, false_iff]
        intro heq
        exact hmem (by simp [← heq])
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [u.val, v.val] 1 w hge]
        simp [mem_orIn_ge n C hge v]
      · have hj : w - n < C.gates.length := by omega
        have hwj : w = n + (w - n) := by omega
        rw [hwj]
        rcases gateAt_op_and_or hAO hj with hand | hor
        · simp only [mem_orIn_and hj hand v, iff_false]
          intro hmem
          rcases (readVectors_getD_and hAO huv hj hand [0, 1]).mp hmem with ⟨p, hp, q, hq, hcap⟩
          rcases readVectors_shape hAO huv (opnd C (w - n) 0) p hp with
            ⟨a1, b1, rfl, ha1, hb1, hpos1⟩
          rcases readVectors_shape hAO huv (opnd C (w - n) 1) q hq with
            ⟨a2, b2, rfl, ha2, hb2, hpos2⟩
          simp [capAdd] at hcap
          omega
        · rw [readVectors_getD_or hAO [u.val, v.val] 1 hj hor [0, 1], mem_orIn_or hAO hj hor v]
          rw [ih (opnd C (w - n) 0) (by have := opnd_lt hAO hj 0; omega)]
          rw [ih (opnd C (w - n) 1) (by have := opnd_lt hAO hj 1; omega)]

lemma mem_readVectors_11 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n} (huv : u ≠ v) :
    ∀ w : ℕ, [1, 1] ∈ (readVectors C n [u.val, v.val] 1).getD w [] ↔
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C w a ∧
        ((u ∈ orIn n C (opnd C a 0) ∧ v ∈ orIn n C (opnd C a 1)) ∨
         (v ∈ orIn n C (opnd C a 0) ∧ u ∈ orIn n C (opnd C a 1))) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [readVectors_getD_lt C n [u.val, v.val] 1 w hw]
      constructor
      · intro hmem
        unfold leafVectors at hmem
        split_ifs at hmem with hin
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
          simp only [List.mem_singleton] at hmem
          rcases hin with rfl | rfl
          · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
            simp [hne] at hmem
          · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
            simp [hne] at hmem
        · simp at hmem
      · rintro ⟨a, _, _, hreach, _⟩
        exact (orReaches_lt_n n C hw hreach).elim
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [u.val, v.val] 1 w hge]
        constructor
        · intro h; simp at h
        · rintro ⟨a, _, _, hreach, _⟩
          exact (orReaches_ge n C hge hreach).elim
      · have hj : w - n < C.gates.length := by omega
        have hwj : w = n + (w - n) := by omega
        rw [hwj]
        rcases gateAt_op_and_or hAO hj with hand | hor
        · rw [readVectors_getD_and hAO huv hj hand [1, 1]]
          constructor
          · rintro ⟨p, hp, q, hq, hcap⟩
            rcases readVectors_shape hAO huv (opnd C (w - n) 0) p hp with
              ⟨a1, b1, rfl, ha1, hb1, hpos1⟩
            rcases readVectors_shape hAO huv (opnd C (w - n) 1) q hq with
              ⟨a2, b2, rfl, ha2, hb2, hpos2⟩
            simp [capAdd] at hcap
            refine ⟨w - n, hj, hand, (orReaches_and hj hand).mpr rfl, ?_⟩
            have hcases : (a1 = 1 ∧ b1 = 0 ∧ a2 = 0 ∧ b2 = 1) ∨
                (a1 = 0 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 0) := by omega
            rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · exact Or.inl ⟨(mem_readVectors_10 hAO huv _).mp hp,
                (mem_readVectors_01 hAO huv _).mp hq⟩
            · exact Or.inr ⟨(mem_readVectors_01 hAO huv _).mp hp,
                (mem_readVectors_10 hAO huv _).mp hq⟩
          · rintro ⟨a, _, _, hreach, hsplit⟩
            have ha : a = w - n := (orReaches_and hj hand).mp hreach
            subst ha
            rcases hsplit with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
            · exact ⟨[1, 0], (mem_readVectors_10 hAO huv _).mpr hu0,
                [0, 1], (mem_readVectors_01 hAO huv _).mpr hv1, by simp [capAdd]⟩
            · exact ⟨[0, 1], (mem_readVectors_01 hAO huv _).mpr hv0,
                [1, 0], (mem_readVectors_10 hAO huv _).mpr hu1, by simp [capAdd]⟩
        · rw [readVectors_getD_or hAO [u.val, v.val] 1 hj hor [1, 1]]
          rw [ih (opnd C (w - n) 0) (by have := opnd_lt hAO hj 0; omega)]
          rw [ih (opnd C (w - n) 1) (by have := opnd_lt hAO hj 1; omega)]
          constructor
          · rintro (⟨a, ha, hop, hreach, hsplit⟩ | ⟨a, ha, hop, hreach, hsplit⟩)
            · exact ⟨a, ha, hop, (orReaches_or hAO hj hor).mpr (Or.inr (Or.inl hreach)), hsplit⟩
            · exact ⟨a, ha, hop, (orReaches_or hAO hj hor).mpr (Or.inr (Or.inr hreach)), hsplit⟩
          · rintro ⟨a, ha, hop, hreach, hsplit⟩
            rcases (orReaches_or hAO hj hor).mp hreach with rfl | h0 | h1
            · rw [hor] at hop; cases hop
            · exact Or.inl ⟨a, ha, hop, h0, hsplit⟩
            · exact Or.inr ⟨a, ha, hop, h1, hsplit⟩

lemma graphFun_single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) :
    graphFun G ∅ (fun i : Fin n => decide (i = x)) = false := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_false_iff_not, not_exists, not_and]
  intro a b hab ha hb
  have hax : a = x := of_decide_eq_true ha
  have hbx : b = x := of_decide_eq_true hb
  subst hax; subst hbx
  exact G.ne_of_adj hab rfl

lemma le_output_of_graphFun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) : n ≤ C.output := by
  by_contra hle
  have hlt : C.output < n := Nat.lt_of_not_le hle
  let x : Fin n := ⟨C.output, hlt⟩
  have h1 : circuitFun n C (fun i => decide (i = x)) = true := by
    unfold circuitFun Circuit.eval
    have hxlen : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := List.length_ofFn
    rw [wires_getD_lt C _ C.output (by rw [hxlen]; exact hlt)]
    simp [x, List.getD_eq_getElem?_getD, hlt]
  have h2 : circuitFun n C (fun i => decide (i = x)) = false := by
    rw [hfun]
    exact graphFun_single_false G x
  rw [h1] at h2
  cases h2

lemma not_mem_orIn_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (x : Fin n) :
    x ∉ orIn n C C.output := by
  intro hx
  have h1 : circuitFun n C (fun i => decide (i = x)) = true :=
    orIn_implies_wires_single hAO x C.output hx
  have h2 : circuitFun n C (fun i => decide (i = x)) = false := by
    rw [hfun]
    exact graphFun_single_false G x
  rw [h1] at h2
  cases h2

end PEqualNP.Outside.L_meta_3708

theorem PEqualNP.Outside.L_meta_3708 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ u v : Fin n, G.Adj u v →
        (¬ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v ↔
          ∃ a < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.CleanedNonEdge.OrToOutput n C a ∧
            ((u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)) ∨ (v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)))) := by
  intro n G _ C _ hAO hfun u v huv
  have hne : u ≠ v := G.ne_of_adj huv
  have hout : n ≤ C.output := PEqualNP.Outside.L_meta_3708.le_output_of_graphFun G C hfun
  have hat : PEqualNP.Core.atGate n C (C.output - n) = C := by
    cases C with
    | mk gates output =>
      simp only [PEqualNP.Core.atGate] at hout ⊢
      congr 1
      omega
  unfold PEqualNP.Core.ReadTwiceAt PEqualNP.CleanedNonEdge.OrToOutput
  rw [hat, Bool.not_eq_false]
  unfold PEqualNP.ReadK.readsAtMost
  rw [List.any_eq_true]
  constructor
  · rintro ⟨vec, hmem, hall⟩
    rcases PEqualNP.Outside.L_meta_3708.readVectors_shape hAO hne C.output vec hmem with
      ⟨a, b, rfl, ha, hb, hpos⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hall
    have hcases : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (PEqualNP.Outside.L_meta_3708.not_mem_orIn_output G C hAO hfun u
        ((PEqualNP.Outside.L_meta_3708.mem_readVectors_10 hAO hne C.output).mp hmem)).elim
    · exact (PEqualNP.Outside.L_meta_3708.not_mem_orIn_output G C hAO hfun v
        ((PEqualNP.Outside.L_meta_3708.mem_readVectors_01 hAO hne C.output).mp hmem)).elim
    · exact (PEqualNP.Outside.L_meta_3708.mem_readVectors_11 hAO hne C.output).mp hmem
  · intro hrhs
    refine ⟨[1, 1], (PEqualNP.Outside.L_meta_3708.mem_readVectors_11 hAO hne C.output).mpr hrhs, ?_⟩
    decide
