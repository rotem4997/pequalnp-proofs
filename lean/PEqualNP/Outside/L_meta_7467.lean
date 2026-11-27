import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7467

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
theorem eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
theorem oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
theorem orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
theorem orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

def edges : List (Fin 11 × Fin 11) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

abbrev G11 : SimpleGraph (Fin 11) :=
  edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

lemma noFour : NoFourCycle G11 := by decide

lemma edges_adj (u v : Fin 11) :
    G11.Adj u v ↔ (u, v) ∈ edges ∨ (v, u) ∈ edges := by
  decide +revert

def maskBit (m : Fin 2048) (v : Fin 11) : Bool := m.val.testBit v.val

def maskCard (m : Fin 2048) : ℕ := (List.finRange 11).countP (maskBit m)

def finsetToMaskNat (T : Finset (Fin 11)) : List (Fin 11) → ℕ
  | [] => 0
  | v :: vs => (if v ∈ T then 2 ^ v.val else 0) ||| finsetToMaskNat T vs

lemma finsetToMaskNat_lt (T : Finset (Fin 11)) : ∀ l : List (Fin 11), finsetToMaskNat T l < 2048
  | [] => by simp [finsetToMaskNat]
  | v :: vs => by
    unfold finsetToMaskNat
    have hvs := finsetToMaskNat_lt T vs
    have hv : (if v ∈ T then 2 ^ v.val else 0) < 2 ^ 11 := by
      split_ifs
      · exact Nat.pow_lt_pow_right (by omega) v.isLt
      · omega
    exact Nat.or_lt_two_pow hv hvs

lemma finsetToMaskNat_testBit (T : Finset (Fin 11)) (u : Fin 11) :
    ∀ l : List (Fin 11), (finsetToMaskNat T l).testBit u.val = decide (u ∈ l ∧ u ∈ T)
  | [] => by simp [finsetToMaskNat]
  | v :: vs => by
    unfold finsetToMaskNat
    rw [Nat.testBit_or, finsetToMaskNat_testBit T u vs]
    by_cases hvT : v ∈ T
    · simp only [hvT, ↓reduceIte, Nat.testBit_two_pow]
      by_cases huv : v = u
      · subst huv; simp [hvT]
      · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h)
        simp [hne, Ne.symm huv]
    · simp only [hvT, ↓reduceIte, Nat.zero_testBit, Bool.false_or]
      by_cases huv : u = v
      · subst huv; simp [hvT]
      · simp [huv]

def finsetToMask (T : Finset (Fin 11)) : Fin 2048 :=
  ⟨finsetToMaskNat T (List.finRange 11), finsetToMaskNat_lt T (List.finRange 11)⟩

lemma maskBit_finsetToMask (T : Finset (Fin 11)) (u : Fin 11) :
    maskBit (finsetToMask T) u = decide (u ∈ T) := by
  unfold maskBit finsetToMask
  rw [finsetToMaskNat_testBit]
  simp [List.mem_finRange]

lemma maskCard_finsetToMask (T : Finset (Fin 11)) :
    maskCard (finsetToMask T) = T.card := by
  unfold maskCard
  have heq : (List.finRange 11).countP (fun v => maskBit (finsetToMask T) v) =
      (List.finRange 11).countP (fun v => decide (v ∈ T)) := by
    congr 1; funext v; exact maskBit_finsetToMask T v
  rw [heq, List.countP_eq_length_filter]
  have hnodup : ((List.finRange 11).filter (fun v => decide (v ∈ T))).Nodup :=
    (List.nodup_finRange 11).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1
  ext v
  simp


def outside (m : Fin 2048) : List (Fin 11 × Fin 11) :=
  edges.filter fun e => !(maskBit m e.1 || maskBit m e.2)

def neighbors (c : Fin 11) (v : Fin 11) : Bool :=
  ([1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85] : List ℕ)[c.val]!.testBit v.val

lemma neighbors_iff (c v : Fin 11) : neighbors c v = true ↔ G11.Adj c v := by
  decide +revert

def hits (c : Fin 11) (e : Fin 11 × Fin 11) : Bool :=
  neighbors c e.1 || neighbors c e.2

def witnessMasks : List (Fin 2048) :=
  [1, 4, 16, 32, 34, 48, 64, 96, 128, 132, 144, 256, 257, 320, 512, 514,
   520, 528, 576, 1024, 1026, 1152, 1280]

def safe (y : Fin 2048) : Bool :=
  edges.all fun e => !(maskBit y e.1 && maskBit y e.2)

def transfers (m y : Fin 2048) (es : List (Fin 11 × Fin 11)) : Bool :=
  (List.finRange 11).all fun d =>
    !maskBit m d || es.any fun e =>
      (!neighbors d e.1 || maskBit y e.1) && (!neighbors d e.2 || maskBit y e.2)

def goodPin (m : Fin 2048) (es : List (Fin 11 × Fin 11)) (v : Fin 11) : Bool :=
  witnessMasks.any fun y => maskBit y v && safe y && transfers m y es

def checkCover (m : Fin 2048) : Bool :=
  if maskCard m ≤ 5 then
    let es := outside m
    !es.isEmpty &&
    (List.finRange 11).all (fun v => es.any fun e => v != e.1 && v != e.2) &&
    (List.finRange 11).all (fun c =>
      !(maskBit m c && es.all (hits c)) ||
      es.any (fun e =>
        (!neighbors c e.1 || goodPin m es e.1) &&
        (!neighbors c e.2 || goodPin m es e.2)))
  else true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma checks (a : Fin 64) :
    ∀ b : Fin 32, checkCover ⟨a.val * 32 + b.val, by omega⟩ = true := by
  revert a
  decide

lemma checkAll (m : Fin 2048) : checkCover m = true := by
  have h := checks ⟨m.val / 32, by omega⟩ ⟨m.val % 32, by omega⟩
  have eq : (⟨m.val / 32 * 32 + m.val % 32, by omega⟩ : Fin 2048) = m :=
    Fin.ext (by dsimp; omega)
  rwa [eq] at h

lemma outsideData {T : Finset (Fin 11)} {e : Fin 11 × Fin 11}
    (he : e ∈ outside (finsetToMask T)) :
    G11.Adj e.1 e.2 ∧ e.1 ∉ T ∧ e.2 ∉ T := by
  obtain ⟨h, ht⟩ := List.mem_filter.mp he
  exact ⟨(edges_adj _ _).mpr (.inl h), by
    simpa [maskBit_finsetToMask] using ht⟩

lemma safeGraph {y : Fin 2048} (h : safe y = true) :
    graphFun G11 ∅ (maskBit y) = false := by
  have no (u v : Fin 11) (he : (u, v) ∈ edges)
      (hu : maskBit y u = true) (hv : maskBit y v = true) : False := by
    have hz := List.all_eq_true.mp h (u, v) he
    simp [hu, hv] at hz
  by_contra hf
  have ht : graphFun G11 ∅ (maskBit y) = true := by
    cases hg : graphFun G11 ∅ (maskBit y) <;> simp_all
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at ht
  obtain ⟨u, v, hadj, hu, hv⟩ := ht
  exact ((edges_adj u v).mp hadj).elim (fun he => no u v he hu hv)
    (fun he => no v u he hv hu)

lemma certified (T : Finset (Fin 11)) (hle : T.card ≤ 5) :
    let es := outside (finsetToMask T)
    es ≠ [] ∧
    (∀ v : Fin 11, ∃ e ∈ es, v ≠ e.1 ∧ v ≠ e.2) ∧
    (∀ c ∈ T, (∀ e ∈ es, G11.Adj c e.1 ∨ G11.Adj c e.2) →
      ∃ e ∈ es, ∀ v : Fin 11, (v = e.1 ∨ v = e.2) → G11.Adj c v →
        ∃ y : Fin 2048, maskBit y v = true ∧ graphFun G11 ∅ (maskBit y) = false ∧
          ∀ d ∈ T, ∃ f ∈ es, (G11.Adj d f.1 → maskBit y f.1 = true) ∧
            (G11.Adj d f.2 → maskBit y f.2 = true)) := by
  let m := finsetToMask T
  let es := outside m
  have h := checkAll m
  rw [checkCover, ite_eq_left (by simpa [m, maskCard_finsetToMask] using hle)] at h
  obtain ⟨⟨hne, hp⟩, hc⟩ := by simpa only [Bool.and_eq_true] using h
  refine ⟨by simpa using hne, ?_, ?_⟩
  · intro v
    obtain ⟨e, he, hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hp v (List.mem_finRange v))
    exact ⟨e, he, by simpa using hs⟩
  · intro c hct hall
    have hact : (maskBit m c && es.all (hits c)) = true := by
      refine Bool.and_eq_true_iff.mpr ⟨by simp [m, maskBit_finsetToMask, hct], ?_⟩
      exact List.all_eq_true.mpr fun e he => by simpa [hits, neighbors_iff] using hall e he
    have row := List.all_eq_true.mp hc c (List.mem_finRange c)
    rw [hact] at row
    simp only [Bool.not_true, Bool.false_or] at row
    obtain ⟨e, he, hok⟩ := List.any_eq_true.mp row
    refine ⟨e, he, fun v hv ha => ?_⟩
    have pin : goodPin m es v = true := by
      have hnb : neighbors c v = true := by exact (neighbors_iff _ _).mpr ha
      rcases hv with rfl | rfl
      · simpa [hnb] using (Bool.and_eq_true_iff.mp hok).1
      · simpa [hnb] using (Bool.and_eq_true_iff.mp hok).2
    obtain ⟨y, _, hy⟩ := List.any_eq_true.mp pin
    obtain ⟨hleft, ht⟩ := Bool.and_eq_true_iff.mp hy
    obtain ⟨hpin, hs⟩ := Bool.and_eq_true_iff.mp hleft
    refine ⟨y, hpin, safeGraph hs, fun d hd => ?_⟩
    have hrow := List.all_eq_true.mp ht d (List.mem_finRange d)
    have din : maskBit m d = true := by simp [m, maskBit_finsetToMask, hd]
    rw [din] at hrow
    simp only [Bool.not_true, Bool.false_or] at hrow
    obtain ⟨f, hf, hyes⟩ := List.any_eq_true.mp hrow
    have help (w : Fin 11) (hw : (!neighbors d w || maskBit y w) = true)
        (hn : G11.Adj d w) : maskBit y w = true := by
      have hb : neighbors d w = true := by exact (neighbors_iff _ _).mpr hn
      simpa [hb] using hw
    exact ⟨f, hf, help _ (Bool.and_eq_true_iff.mp hyes).1, help _ (Bool.and_eq_true_iff.mp hyes).2⟩


lemma rawGate {n : ℕ} {C : Circuit} {k : ℕ} {u : Fin n} :
    u ∈ orIn n C (n+k) ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n+k ∧ u ∈ orIn n C w := by
  constructor
  · intro hu
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w,hs,rest⟩
    · have := u.isLt; omega
    · obtain ⟨j,hj,eq,op,port,lt⟩ := hs
      have : j = k := by omega
      subst j
      exact ⟨hj,op,w,port,lt,reach_mem_orIn u rest⟩
  · rintro ⟨hk,op,w,port,lt,hu⟩
    apply reach_mem_orIn u
    exact Relation.ReflTransGen.head ⟨k,hk,rfl,op,port,lt⟩ (mem_orIn_reach u hu)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma lambdaPort (ao : IsAO2 n C) {k w : ℕ} (hk : k ∈ lam G C)
    (hw : w ∈ (gateAt C k).inputs) : (orIn n C w).Nonempty := by
  let _ : DecidableEq GateOp := gateOpDecEq
  obtain ⟨hor,h0,h1,_⟩ := Finset.mem_filter.mp hk
  have valid : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hor).1
  obtain ⟨b,rfl⟩ := inputsAsOpnd ao valid hw
  exact (eitherOperand 0 b).elim (fun h => h ▸ h0) (fun h => h ▸ h1)

lemma mixingOutside {k : ℕ} (hk : k ∈ mixing G C) : k ∈ orN G C \ lam G C := by
  obtain ⟨hn, hne⟩ := Finset.mem_filter.mp hk
  refine Finset.mem_sdiff.mpr ⟨hn, fun hl => ?_⟩
  obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
  exact hne (propext ⟨fun h => ((Finset.nonempty_iff_ne_empty.mp h0) h).elim,
    fun h => ((Finset.nonempty_iff_ne_empty.mp h1) h).elim⟩)

-- A firing wire with a nonempty raw support whose inputs are all false must
-- reach a mixing OR through OR gates.
lemma mixingSource (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      (∀ v ∈ orIn n C w, x v = false) →
      ∃ k ∈ mixing G C, OrReaches n C w k ∧ (orIn n C (n+k)).Nonempty ∧
        gateVal n C k x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw yes absent
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      have mem : v ∈ orIn n C w := reach_mem_orIn _ Relation.ReflTransGen.refl
      exact (Bool.false_ne_true ((absent v mem).symm.trans ((val_ofFn C x v).symm.trans yes))).elim
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨v,hv⟩ := raw
      obtain ⟨hk,hop,q,hq,hback,hqv⟩ := rawGate.mp hv
      by_cases mixed : k ∈ mixing G C
      · exact ⟨k,mixed,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,⟨v,hv⟩,yes⟩
      · obtain ⟨p,hp,hpback,hpOn⟩ := (val_or (n := n) (by simp) hk hop).mp yes
        have hpr : (orIn n C p).Nonempty := by
          by_contra hempty
          have ep := Finset.not_nonempty_iff_eq_empty.mp hempty
          obtain ⟨b,hb⟩ := inputsAsOpnd ao hk hp
          obtain ⟨d,hd⟩ := inputsAsOpnd ao hk hq
          have hn := orNOfRaw (G := G) hk hop ⟨v,hv⟩
          have pempty : orIn n C (opnd C k b) = ∅ := hb ▸ ep
          have qfull : (orIn n C (opnd C k d)).Nonempty := ⟨v,hd ▸ hqv⟩
          have hne := Finset.nonempty_iff_ne_empty.mp qfull
          apply mixed
          refine Finset.mem_filter.mpr ⟨hn, ?_⟩
          intro eq
          fin_cases b <;> fin_cases d <;>
            first | exact hne pempty | exact hne (eq.mp pempty) | exact hne (eq.mpr pempty)
        have off (u : Fin n) (h : u ∈ orIn n C p) : x u = false :=
          absent u (rawGate.mpr ⟨hk,hop,p,hp,hpback,h⟩)
        obtain ⟨j,hj,path,qraw,on⟩ := ih p hpback hpr hpOn off
        exact ⟨j,hj,(orReaches_iff n C k j).mpr ⟨hk,Or.inr ⟨hop,p,hp,hpback,path⟩⟩,
          qraw,on⟩

lemma prefixRaw (ao : IsAO2 n C) {m : ℕ} (only : orN G C \ lam G C = {m})
    (x : Fin n → Bool) :
    ∀ w < n+m, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      ∃ v ∈ orIn n C w, x v = true := by
  intro w hw hraw hval
  by_contra h
  have off (v : Fin n) (hv : v ∈ orIn n C w) : x v = false := by
    cases e : x v
    · rfl
    · exact (h ⟨v,hv,e⟩).elim
  obtain ⟨k,hk,hr,_,_⟩ := mixingSource (G := G) ao x w hraw hval off
  have eq : k = m := by simpa [only] using mixingOutside hk
  have le := orStep_le (orReaches_reach k w hr).1
  omega

lemma topNonempty (h : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    (side (n := n) C a b).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  have hm : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    fin_cases b
    · exact ⟨ha, Or.inl he⟩
    · exact ⟨ha, Or.inr he⟩
  simp [h] at hm

lemma singleSide (h4 : NoFourCycle G) (ao : IsAO2 n C) (h : centreless G C = ∅)
    {a : ℕ} (ha : a ∈ tops G C) :
    ∃ (b : Fin 2) (c : Fin n), side C a b = {c} := by
  have positive (b : Fin 2) : 0 < (side (n := n) C a b).card :=
    Finset.card_pos.mpr (topNonempty h ha b)
  by_cases h0 : (side (n := n) C a 0).card = 1
  · obtain ⟨c,hc⟩ := Finset.card_eq_one.mp h0
    exact ⟨0,c,hc⟩
  · have hgt : 1 < (side (n := n) C a 0).card := by have := positive 0; omega
    obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp hgt
    have sub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) :=
      fun w hw => by simp [topAdj ao ha hu hw, topAdj ao ha hv hw]
    have hle := (Finset.card_le_card sub).trans (h4 u v ne)
    have h1 : (side (n := n) C a 1).card = 1 := by have := positive 1; omega
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp h1
    exact ⟨1,c,hc⟩

lemma oppositeAdj (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    {u v : Fin n} (hu : u ∈ side C a b) (hv : v ∈ side C a (1-b)) : G.Adj u v := by
  fin_cases b
  · exact topAdj ao ha hu hv
  · exact (topAdj ao ha hv hu).symm

lemma belowReachesTop (ao : IsAO2 n C) {k : ℕ} (below : BelowF G C k)
    {u v : Fin n} (on : gateVal n C k (pairInput u v) = true) :
    ∃ a ∈ tops G C, a ≤ k ∧ gateVal n C a (pairInput u v) = true := by
  let _ : DecidableEq GateOp := gateOpDecEq
  rcases operand_trace (C := C) u v (n+k) on with ⟨t,_,hr⟩ | ⟨a,ha,hop,hr,hv⟩
  · have trueAt := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    exact (G.irrefl ((graphFun_pair G t t).mp (below _ trueAt))).elim
  · refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,
        (ao.1 _ (gateAt_mem ha)).resolve_right hop, ?_⟩, ?_, hv⟩
    · intro x hx
      exact below x (orStep_up (n := n) (by simp) hr hx)
    · have := orStep_le hr
      omega




def edgeInput (e : Fin 11 × Fin 11) : Fin 11 → Bool := pairInput e.1 e.2

-- A single mixing gate supplies the singleton side of every top that
-- fires on an edge outside the set of chosen star centers.
lemma main (C : Circuit) (least : IsLeastAO G11 C)
    (num : (tops G11 C).card ≤ 5) (nonempty : centreless G11 C = ∅)
    (one : (orN G11 C \ lam G11 C).card = 1) : False := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  have ao := least.1
  obtain ⟨m, only⟩ := Finset.card_eq_one.mp one
  have sideChoice (a : ℕ) : ∃ (b : Fin 2) (c : Fin 11), a ∈ tops G11 C → side C a b = {c} := by
    by_cases ha : a ∈ tops G11 C
    · obtain ⟨b,c,h⟩ := singleSide noFour ao nonempty ha
      exact ⟨b,c,fun _ => h⟩
    · exact ⟨0,0,fun h => (ha h).elim⟩
  choose bit center orient using sideChoice
  let T := (tops G11 C).image center
  let es := outside (finsetToMask T)
  have hT : T.card ≤ 5 := Finset.card_image_le.trans num
  have inT {a : ℕ} (ha : a ∈ tops G11 C) : center a ∈ T := Finset.mem_image_of_mem _ ha
  obtain ⟨hes, noPin, cert⟩ := certified T hT
  have avoids {e : Fin 11 × Fin 11} (he : e ∈ es) {v : Fin 11} (hv : v ∈ T) :
      edgeInput e v = false := by
    have h := outsideData he
    have ne₁ : v ≠ e.1 := fun eq => h.2.1 (eq ▸ hv)
    have ne₂ : v ≠ e.2 := fun eq => h.2.2 (eq ▸ hv)
    simp [edgeInput, pairInput, ne₁, ne₂]
  have routeAt {e : Fin 11 × Fin 11} (he : e ∈ es) {a : ℕ} (ha : a ∈ tops G11 C)
      (on : gateVal 11 C a (edgeInput e) = true) :
      OrReaches 11 C (opnd C a (bit a)) m ∧ (orIn 11 C (11+m)).Nonempty ∧
        gateVal 11 C m (edgeInput e) = true := by
    obtain ⟨al, hand, _⟩ := topData ha
    have off (v : Fin 11) (hv : v ∈ side C a (bit a)) : edgeInput e v = false := by
      rw [orient a ha, Finset.mem_singleton] at hv
      subst v
      exact avoids he (inT ha)
    obtain ⟨k,hk,path,raw,yes⟩ := mixingSource (G := G11) ao (edgeInput e) _
      (topNonempty nonempty ha (bit a)) ((andValOperands ao al hand _).mp on (bit a)) off
    have heq : k = m := by simpa [only] using mixingOutside hk
    subst k
    exact ⟨path,raw,yes⟩
  have routed (e : Fin 11 × Fin 11) (he : e ∈ es) :
      ∃ a ∈ tops G11 C, gateVal 11 C a (edgeInput e) = true ∧
        OrReaches 11 C (opnd C a (bit a)) m ∧ (orIn 11 C (11+m)).Nonempty ∧
        gateVal 11 C m (edgeInput e) = true := by
    obtain ⟨a,ha,on⟩ := acceptedTop least (outsideData he).1
    exact ⟨a,ha,on,routeAt he ha on⟩
  have mixSub {a : ℕ} (ha : a ∈ tops G11 C) (path : OrReaches 11 C (opnd C a (bit a)) m) :
      orIn 11 C (11+m) ⊆ {center a} := by
    rw [← orient a ha]
    exact orInTrans (orReaches_reach m _ path).1
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil es hes
  obtain ⟨a₀, ha₀, _, path₀, raw₀, _⟩ := routed e₀ he₀
  let c := center a₀
  have cT : c ∈ T := inT ha₀
  have cr : c ∈ orIn 11 C (11+m) := by
    obtain ⟨r,hr⟩ := raw₀
    have eq : r = c := Finset.mem_singleton.mp (mixSub ha₀ path₀ hr)
    exact eq ▸ hr
  have mOn (e : Fin 11 × Fin 11) (he : e ∈ es) : gateVal 11 C m (edgeInput e) = true := by
    obtain ⟨_,_,_,_,_,h⟩ := routed e he
    exact h
  have receiver (e : Fin 11 × Fin 11) (he : e ∈ es) :
      ∃ v : Fin 11, (v = e.1 ∨ v = e.2) ∧ G11.Adj c v ∧
        ∀ x : Fin 11 → Bool, gateVal 11 C m x = true → x v = true → graphFun G11 ∅ x = true := by
    obtain ⟨a,ha,on,path,_,_⟩ := routed e he
    obtain ⟨al,hand,below⟩ := topData ha
    have cMem : c ∈ side C a (bit a) := by
      rw [orient a ha]
      exact mixSub ha path cr
    have leafOn := (andValOperands ao al hand _).mp on (1 - bit a)
    have hasPin : ∃ v ∈ side C a (1 - bit a), edgeInput e v = true := by
      by_contra h
      have off (v : Fin 11) (hv : v ∈ side C a (1 - bit a)) : edgeInput e v = false := by
        cases eq : edgeInput e v
        · rfl
        · exact (h ⟨v,hv,eq⟩).elim
      obtain ⟨k,hk,leafPath,_,_⟩ := mixingSource (G := G11) ao (edgeInput e) _
        (topNonempty nonempty ha (1 - bit a)) leafOn off
      have eq : k = m := by simpa [only] using mixingOutside hk
      subst k
      have leafC : c ∈ side C a (1 - bit a) := orInTrans (orReaches_reach m _ leafPath).1 cr
      exact G11.irrefl (oppositeAdj ao ha cMem leafC)
    obtain ⟨v,hv,hon⟩ := hasPin
    refine ⟨v, (pairInput_true _ _ _).mp hon, oppositeAdj ao ha cMem hv, ?_⟩
    intro x hx ht
    exact (oppositeSideWmax ao ha path hv |> Finset.mem_filter.mp).2 x hx ht
  have allHit (e : Fin 11 × Fin 11) (he : e ∈ es) : G11.Adj c e.1 ∨ G11.Adj c e.2 := by
    obtain ⟨v,hv,hc,_⟩ := receiver e he
    rcases hv with rfl | rfl
    · exact .inl hc
    · exact .inr hc
  obtain ⟨e,he,hgood⟩ := cert c cT allHit
  obtain ⟨v,hv,hadj,accepted⟩ := receiver e he
  obtain ⟨y,yon,ysafe,clause⟩ := hgood v hv hadj
  let x := maskBit y
  -- Before the mixer, firing on the whole test list propagates through
  -- AND gates and through raw clauses in the neighborhood of a center.
  have lift : ∀ w < 11+m,
      (∀ f ∈ es, val C (List.ofFn (edgeInput f)) w = true) →
      val C (List.ofFn x) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro before on
      by_cases hw : w < 11
      · let u : Fin 11 := ⟨w,hw⟩
        obtain ⟨f,hf,hn₁,hn₂⟩ := noPin u
        have ok := (val_ofFn C (edgeInput f) u).symm.trans (on f hf)
        exact (((pairInput_true _ _ _).mp ok).elim hn₁ hn₂).elim
      · obtain ⟨k,rfl⟩ : ∃ k, w = 11+k := ⟨w-11,by omega⟩
        have hk : k < C.gates.length := by
          have valid := (rawGate.mp cr).1
          omega
        rcases ao.1 _ (gateAt_mem hk) with hand | hor
        · apply (val_and (n := 11) (by simp) hk hand).mpr
          intro p hp
          have back := ao.2.1 k hk p hp
          exact ⟨back, ih p back (by omega) fun f hf =>
            ((val_and (n := 11) (by simp) hk hand).mp (on f hf) p hp).2⟩
        · have hnot : ¬ BelowF G11 C k := by
            intro below
            obtain ⟨a,ha,hle,haon⟩ := belowReachesTop ao below (on e₀ he₀)
            have path := (routeAt he₀ ha haon).1
            have reach := orStep_le (orReaches_reach m _ path).1
            have back := opndBound ao (topData ha).1 (bit a)
            omega
          have hn : k ∈ orN G11 C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,hnot⟩
          have hlam : k ∈ lam G11 C := by
            by_contra no
            have eq : k = m := by simpa [only] using Finset.mem_sdiff.mpr ⟨hn,no⟩
            omega
          obtain ⟨z,hz⟩ := lambdaPort ao hlam (opndMem ao hk 0)
          have raw : (orIn 11 C (11+k)).Nonempty :=
            ⟨z,rawGate.mpr ⟨hk,hor,_,opndMem ao hk 0,opndBound ao hk 0,hz⟩⟩
          have hit (f : Fin 11 × Fin 11) (hf : f ∈ es) :
              ∃ u ∈ orIn 11 C (11+k), edgeInput f u = true :=
            prefixRaw ao only (edgeInput f) _ before raw (on f hf)
          obtain ⟨_,_,_,a,ha,b,_,path⟩ := Finset.mem_filter.mp hlam
          have sub : orIn 11 C (11+k) ⊆ side C a b := orInTrans (orReaches_reach k _ path).1
          rcases eitherOperand (bit a) b with same | opp
          · obtain ⟨u,hu,huOn⟩ := hit e₀ he₀
            have hu' := sub hu
            rw [same, orient a ha, Finset.mem_singleton] at hu'
            exact (Bool.false_ne_true ((avoids he₀ (hu'.symm ▸ inT ha)).symm.trans huOn)).elim
          · obtain ⟨f,hf,h₁,h₂⟩ := clause (center a) (inT ha)
            obtain ⟨u,hu,huOn⟩ := hit f hf
            have uleaf := sub hu
            rw [opp] at uleaf
            have uadj : G11.Adj (center a) u :=
              oppositeAdj ao ha (by rw [orient a ha]; simp) uleaf
            have uOn : x u = true := by
              rcases (pairInput_true _ _ _).mp huOn with rfl | rfl
              · exact h₁ uadj
              · exact h₂ uadj
            exact reach_var_val x _ u (mem_orIn_reach u hu) uOn
  -- Only the other port of the mixer can fire on the test edges.
  obtain ⟨ml, mor, p, hp, pl, cp⟩ := rawGate.mp cr
  obtain ⟨b, eb⟩ := inputsAsOpnd ao ml hp
  let q := opnd C m (1-b)
  have liveQ (f : Fin 11 × Fin 11) (hf : f ∈ es) :
      val C (List.ofFn (edgeInput f)) q = true := by
    obtain ⟨z,hz,_,on⟩ := (val_or (n := 11) (by simp) ml mor).mp (mOn f hf)
    obtain ⟨d,ed⟩ := inputsAsOpnd ao ml hz
    rcases eitherOperand b d with rfl | rfl
    · have eq : z = p := ed.trans eb.symm
      rw [eq] at on
      obtain ⟨u,hu,huOn⟩ := prefixRaw ao only (edgeInput f) p pl ⟨c,cp⟩ on
      have eq : u = c := Finset.mem_singleton.mp
        (mixSub ha₀ path₀ (rawGate.mpr ⟨ml,mor,p,hp,pl,hu⟩))
      exact (Bool.false_ne_true ((avoids hf (eq.symm ▸ cT)).symm.trans huOn)).elim
    · dsimp only [q]
      rwa [ed] at on
  have qBound : q < 11+m := opndBound ao ml (1-b)
  have mixerOn : gateVal 11 C m x = true :=
    (val_or (n := 11) (by simp) ml mor).mpr ⟨q,opndMem ao ml (1-b),qBound,lift q qBound liveQ⟩
  exact Bool.false_ne_true (ysafe.symm.trans (accepted x mixerOn yon))


end PEqualNP.Outside.L_meta_7467

theorem PEqualNP.Outside.L_meta_7467 :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       x2.size ≤ (21 : ℕ) → x5.card = (3 : ℕ) → (PEqualNP.TopForm.tops x1 x2).card = (5 : ℕ) → PEqualNP.TopForm.centreless x1 x2 = ∅ → (PEqualNP.TopForm.junk x1 x2).card = (3 : ℕ) → (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card = (1 : ℕ) → (∃ (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x5) x12 ∧ x12.card = (5 : ℕ)) → False := by
  intro _ C least _ _ _ _ five centered _ one _
  exact PEqualNP.Outside.L_meta_7467.main C least five.le centered one
