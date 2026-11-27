import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17251

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
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
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
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
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
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

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
    (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
    (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
    m ∈ orN G C \ lam G C := by
  obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
  have hNotBelow : ¬ BelowF G C m := by
    intro h
    have hvm : gateVal n C m x = true := (val_or (n := n) (by simp) hm ho).mpr
      ⟨n + j, hi, hb, hjx⟩
    exact Bool.noConfusion (hx.symm.trans (h x hvm))
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro ho hNotBelow)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
    have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty (n := n) hjop] at hnonempty
    exact Finset.not_nonempty_empty hnonempty

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hr, hjv⟩

lemma residualConnection (hL : IsLeastAO G C) (hT : TopForm G C)
    (he : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty := by
  obtain ⟨e, he⟩ := he
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, j, hj, hr, _⟩ := residualTrace hL hT he
    rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨m, hl, ho, hi, hb, _⟩
    · have hz : side (n := n) C a b = ∅ := by
        change orIn n C (opnd C a b) = ∅
        rw [heq]
        exact andRawEmpty (junkData hj).2.1
      left
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
      fin_cases b
      · exact .inl hz
      · exact .inr hz
    · exact .inr ⟨m, lastOrOutside hL.1 hj hl ho hi hb⟩




open PEqualNP.MetaComplexity

abbrev G11 : SimpleGraph (Fin 11) :=
  edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def g11Edges : List (Nat × Nat) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def adjMask : Nat → Nat
  | 0 => 1536
  | 1 => 272
  | 2 => 1056
  | 3 => 192
  | 4 => 1282
  | 5 => 772
  | 6 => 1160
  | 7 => 584
  | 8 => 562
  | 9 => 417
  | 10 => 85
  | _ => 0

def lamList : List Nat :=
  [1, 2, 4, 5, 8, 16, 17, 18, 20, 21, 32, 33, 34, 48, 50, 64, 65, 68, 69, 72, 80, 81, 84, 85,
   128, 129, 136, 160, 161, 192, 256, 257, 258, 260, 272, 288, 289, 384, 385, 416, 417,
   512, 514, 516, 520, 528, 530, 544, 546, 560, 562, 576, 584, 768, 772, 1024, 1026, 1032,
   1056, 1152, 1160, 1280, 1282, 1536]

def tau5Pairs : List ((Nat × Nat) × (Nat × Nat)) :=
  [((0,9),(1,4)), ((0,9),(3,6)), ((0,10),(3,7)), ((1,4),(2,5)),
   ((1,4),(3,6)), ((1,4),(3,7)), ((1,4),(6,7)), ((1,8),(3,6)),
   ((1,8),(3,7)), ((1,8),(6,7)), ((2,5),(3,6)), ((2,5),(3,7)),
   ((2,5),(6,7)), ((3,6),(4,8)), ((3,7),(4,8)), ((4,8),(6,7))]

def popcount11 (m : Nat) : Nat :=
  (List.range 11).foldl (fun acc i => if m.testBit i then acc + 1 else acc) 0

def missedEdges (k : Nat) : List (Nat × Nat) :=
  g11Edges.filter fun e => !(k.testBit e.1 || k.testBit e.2)

def checkTau5 : Bool :=
  (List.range 2048).all fun k =>
    if popcount11 k != 5 then true
    else
      match missedEdges k with
      | [e1, e2] => (e1, e2) ∈ tau5Pairs
      | _ :: _ :: _ :: _ => true
      | _ => false

theorem checkTau5_ok : checkTau5 = true := by decide +kernel

def checkLamList : Bool :=
  (List.range 2048).all fun m =>
    if m == 0 then true
    else
      let isSing := (List.range 11).any fun v => m == (1 <<< v)
      let isNbr := (List.range 11).any fun c => (m &&& adjMask c) == m
      if isSing || isNbr then m ∈ lamList else true

theorem checkLamList_ok : checkLamList = true := by decide +kernel

def hasIndepNotAdj (A B D : Nat) (w : Nat) : Bool :=
  (List.range 11).any fun a =>
    A.testBit a &&
    (List.range 11).any fun b =>
      B.testBit b && !(adjMask a).testBit b &&
      (List.range 11).any fun d =>
        D.testBit d && !((adjMask a ||| adjMask b).testBit d) &&
        !((adjMask a ||| adjMask b ||| adjMask d).testBit w)

def hasIndep (A B D : Nat) : Bool :=
  (List.range 11).any fun a =>
    A.testBit a &&
    (List.range 11).any fun b =>
      B.testBit b && !(adjMask a).testBit b &&
      (List.range 11).any fun d =>
        D.testBit d && !((adjMask a ||| adjMask b).testBit d)

def checkPair (e1 e2 : Nat × Nat) : Bool :=
  let m1 := (1 <<< e1.1) ||| (1 <<< e1.2)
  let m2 := (1 <<< e2.1) ||| (1 <<< e2.2)
  let cand := lamList.filter fun s => (s &&& m1) != 0 && (s &&& m2) != 0
  (List.range 11).all fun z =>
    if z == e1.1 || z == e1.2 || z == e2.1 || z == e2.2 then true
    else
      [e1.1, e1.2].all fun w1 =>
        if !(adjMask z).testBit w1 then true
        else
          [e2.1, e2.2].all fun w2 =>
            if !(adjMask z).testBit w2 then true
            else
              cand.all fun A =>
                cand.all fun B =>
                  cand.all fun D =>
                    !hasIndep A B D || hasIndepNotAdj A B D w1 || hasIndepNotAdj A B D w2

def checkAllTriples : Bool := tau5Pairs.all fun p => checkPair p.1 p.2

theorem checkAllTriples_ok : checkAllTriples = true := by decide +kernel

theorem G11_noFourCycle : NoFourCycle G11 := by decide +kernel

theorem G11_edgeCard : G11.edgeFinset.card = 16 := by decide +kernel

theorem G11_adj_iff_adjMask (u v : Fin 11) : G11.Adj u v ↔ (adjMask u.val).testBit v.val = true := by
  revert u v; decide +kernel

theorem g11Edges_nodup_sym2 :
    (g11Edges.map fun p => s(p.1, p.2)).Nodup := by decide +kernel

theorem g11Edges_bounds : ∀ p ∈ g11Edges, p.1 < 11 ∧ p.2 < 11 := by decide +kernel

theorem g11Edges_adj : ∀ p ∈ g11Edges, ∀ (h1 : p.1 < 11) (h2 : p.2 < 11),
    G11.Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ := by decide +kernel

def toMask (S : Finset (Fin 11)) : Nat :=
  (List.finRange 11).foldl (fun acc v => if v ∈ S then acc ||| (1 <<< v.val) else acc) 0

theorem toMask_lt (S : Finset (Fin 11)) : toMask S < 2048 := by
  have haux : ∀ (l : List (Fin 11)) (acc : Nat), acc < 2 ^ 11 →
      l.foldl (fun a v => if v ∈ S then a ||| (1 <<< v.val) else a) acc < 2 ^ 11 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons v vs ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      split_ifs
      · apply Nat.or_lt_two_pow h
        have hv := v.isLt
        have : 1 <<< v.val = 2 ^ v.val := by simp [Nat.shiftLeft_eq]
        rw [this]
        exact Nat.pow_lt_pow_right (by omega) hv
      · exact h
  exact haux _ 0 (by omega)

theorem toMask_testBit (S : Finset (Fin 11)) (u : Fin 11) :
    (toMask S).testBit u.val = decide (u ∈ S) := by
  have haux : ∀ (l : List (Fin 11)) (acc : Nat),
      (l.foldl (fun a v => if v ∈ S then a ||| (1 <<< v.val) else a) acc).testBit u.val =
        (acc.testBit u.val || (u ∈ l && decide (u ∈ S))) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons v vs ih =>
      intro acc
      simp only [List.foldl_cons, ih]
      by_cases hvu : u = v
      · subst hvu
        by_cases huS : u ∈ S <;> simp [huS, Nat.testBit_or, Nat.testBit_shiftLeft]
      · have hne : v.val ≠ u.val := fun h => hvu (Fin.ext h.symm)
        by_cases hvS : v ∈ S
        · have hbit : (1 <<< v.val).testBit u.val = false := by
            rw [Nat.testBit_shiftLeft]
            by_cases hle : v.val ≤ u.val
            · have hpos : u.val - v.val ≠ 0 := by omega
              rcases Nat.exists_eq_succ_of_ne_zero hpos with ⟨k, hk⟩
              rw [hk]
              simp [hle, Nat.testBit_succ]
            · simp [hle]
          simp [hvS, hvu, Nat.testBit_or, hbit]
        · simp [hvS, hvu]
  have := haux (List.finRange 11) 0
  simp at this
  exact this

theorem popcount11_toMask (S : Finset (Fin 11)) : popcount11 (toMask S) = S.card := by
  have haux : ∀ (l : List (Fin 11)) (acc : Nat), l.Nodup →
      (l.map Fin.val).foldl (fun a i => if (toMask S).testBit i then a + 1 else a) acc =
        acc + (l.filter (fun v => decide (v ∈ S))).length := by
    intro l
    induction l with
    | nil => intro acc _; simp
    | cons v vs ih =>
      intro acc hnd
      simp only [List.map_cons, List.foldl_cons, List.filter_cons]
      rw [toMask_testBit, ih _ (List.nodup_cons.mp hnd).2]
      cases decide (v ∈ S) <;> simp <;> omega
  have hrange : List.range 11 = (List.finRange 11).map Fin.val := by decide +kernel
  unfold popcount11
  rw [hrange, haux (List.finRange 11) 0 (List.nodup_finRange 11), Nat.zero_add]
  have hEq : S = ((List.finRange 11).filter (fun v => decide (v ∈ S))).toFinset := by
    ext v; simp
  have hcard : S.card = ((List.finRange 11).filter (fun v => decide (v ∈ S))).length := by
    conv_lhs => rw [hEq]
    exact List.toFinset_card_of_nodup ((List.nodup_finRange 11).filter _)
  omega

theorem toMask_eq_zero_iff (S : Finset (Fin 11)) : toMask S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    have := toMask_testBit S u
    rw [h] at this
    simp [hu] at this
  · intro h
    subst h
    decide +kernel

theorem toMask_singleton (v : Fin 11) : toMask {v} = 1 <<< v.val := by
  revert v; decide +kernel

theorem toMask_and_adjMask (S : Finset (Fin 11)) (c : Fin 11)
    (hsub : ∀ v ∈ S, G11.Adj c v) : (toMask S &&& adjMask c.val) = toMask S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 11
  · let u : Fin 11 := ⟨i, hi⟩
    change ((toMask S).testBit u.val && (adjMask c.val).testBit u.val) = (toMask S).testBit u.val
    rw [toMask_testBit]
    by_cases hu : u ∈ S
    · simp [hu, (G11_adj_iff_adjMask c u).mp (hsub u hu)]
    · simp [hu]
  · have hlt := toMask_lt S
    have hpow : 2048 ≤ 2 ^ i := by
      have : 2 ^ 11 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h0 : (toMask S).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hpow)
    simp [h0]

theorem toMask_mem_lamList (S : Finset (Fin 11)) (hn : S.Nonempty)
    (hl : (∃ v : Fin 11, S = {v}) ∨ ∃ c : Fin 11, ∀ v ∈ S, G11.Adj c v) :
    toMask S ∈ lamList := by
  have hall := List.all_eq_true.mp checkLamList_ok (toMask S) (List.mem_range.mpr (toMask_lt S))
  have hnz : toMask S ≠ 0 := fun h => Finset.not_nonempty_empty ((toMask_eq_zero_iff S).mp h ▸ hn)
  have hnzb : (toMask S == 0) = false := beq_false_of_ne hnz
  simp only [hnzb, Bool.false_eq_true, ↓reduceIte] at hall
  have horT : (((List.range 11).any fun v => toMask S == 1 <<< v) ||
      ((List.range 11).any fun c => (toMask S &&& adjMask c) == toMask S)) = true := by
    rcases hl with ⟨v, rfl⟩ | ⟨c, hc⟩
    · apply Bool.or_eq_true_iff.mpr; left
      exact List.any_eq_true.mpr ⟨v.val, List.mem_range.mpr v.isLt, beq_iff_eq.mpr (toMask_singleton v)⟩
    · apply Bool.or_eq_true_iff.mpr; right
      exact List.any_eq_true.mpr ⟨c.val, List.mem_range.mpr c.isLt, beq_iff_eq.mpr (toMask_and_adjMask S c hc)⟩
  simp only [horT, ↓reduceIte, decide_eq_true_eq] at hall
  exact hall

theorem toMask_and_edge_ne_zero (S : Finset (Fin 11)) (u v : Fin 11)
    (h : u ∈ S ∨ v ∈ S) : (toMask S &&& ((1 <<< u.val) ||| (1 <<< v.val))) ≠ 0 := by
  intro h0
  rcases h with hu | hv
  · have hb := congrArg (fun x => x.testBit u.val) h0
    simp [Nat.testBit_and, Nat.testBit_or, toMask_testBit, hu, Nat.testBit_shiftLeft] at hb
  · have hb := congrArg (fun x => x.testBit v.val) h0
    simp [Nat.testBit_and, Nat.testBit_or, toMask_testBit, hv, Nat.testBit_shiftLeft] at hb

theorem G11_fullCover (K : Finset (Fin 11)) (hK : G11.IsVertexCover (K : Set _)) :
    7 ≤ K.card := by
  let w (v : Fin 11) : ℕ := if v ∈ K then 1 else 0
  have ew (u v : Fin 11) (he : G11.Adj u v) : 1 ≤ w u + w v := by
    rcases hK he with hu | hv
    · change u ∈ K at hu
      simp [w, hu]
    · change v ∈ K at hv
      simp [w, hv]
  have h0 := ew 1 4 (by decide +kernel)
  have h1 := ew 4 8 (by decide +kernel)
  have h2 := ew 8 1 (by decide +kernel)
  have h3 := ew 3 6 (by decide +kernel)
  have h4 := ew 6 7 (by decide +kernel)
  have h5 := ew 7 3 (by decide +kernel)
  have h6 := ew 0 9 (by decide +kernel)
  have h7 := ew 9 5 (by decide +kernel)
  have h8 := ew 5 2 (by decide +kernel)
  have h9 := ew 2 10 (by decide +kernel)
  have h10 := ew 10 0 (by decide +kernel)
  have hw : ∑ v, w v = K.card := by simp [w]
  simp [Fin.sum_univ_succ] at hw
  omega

theorem coneStrict (C : Circuit) : ∀ k h, InCone 11 C h k → h < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h hh
    obtain ⟨_, p, hp, _, hpath⟩ := (inCone_iff 11 C h k).mp hh
    rcases hpath with rfl | hpath
    · exact hp
    · exact (ih p hp h hpath).trans hp

theorem topStars {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hC4 : NoFourCycle G) (hAO : IsAO2 11 C) :
    ∀ a ∈ tops G C,
      let S : Fin 2 → Finset (Fin 11) := side C a
      (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1) := by
  intro a ha
  refine ⟨fun u hu v hv => topAdj hAO ha hu hv, ?_⟩
  by_contra hboth
  push Not at hboth
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hboth.1
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp hboth.2
  have hsub : ({v1, v2} : Finset (Fin 11)) ⊆ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨topAdj hAO ha hu1 hv1, topAdj hAO ha hu2 hv1⟩
    · exact ⟨topAdj hAO ha hu1 hv2, topAdj hAO ha hu2 hv2⟩
  have hcard2 : ({v1, v2} : Finset (Fin 11)).card = 2 := Finset.card_pair hvne
  have hle := (Finset.card_le_card hsub).trans (hC4 u1 u2 hune)
  omega

theorem residualTraceWithTop {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin 11}
    (he : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal 11 C a (pairInput u v) = true ∧
      OrReaches 11 C (opnd C a b) h ∧
      gateVal 11 C h (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩

theorem inCone_not_orReaches_has_and {C : Circuit} (hAO : IsAO2 11 C) (a : ℕ) :
    ∀ k, k < C.gates.length → InCone 11 C a k → ¬ OrReaches 11 C (11 + k) a →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ InCone 11 C a j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hcone hnor
    rcases hAO.1 _ (gateAt_mem hk) with hand | hor
    · exact ⟨k, hk, hand, hcone⟩
    · obtain ⟨_, p, hp, hpin, hpath⟩ := (inCone_iff 11 C a k).mp hcone
      rcases hpath with rfl | hcp
      · exfalso
        apply hnor
        exact (orReaches_iff 11 C k a).mpr ⟨hk, Or.inr ⟨hor, 11 + a, hpin, by omega,
          (orReaches_iff 11 C a a).mpr ⟨by omega, Or.inl rfl⟩⟩⟩
      · have hnorp : ¬ OrReaches 11 C (11 + p) a := by
          intro hrp
          exact hnor ((orReaches_iff 11 C k a).mpr ⟨hk, Or.inr ⟨hor, 11 + p, hpin, by omega, hrp⟩⟩)
        exact ih p hp (by omega) hcp hnorp

theorem top_orReaches_output {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {a : ℕ} (ha : a ∈ tops G C) :
    OrReaches 11 C C.output a := by
  by_contra hnor
  obtain ⟨ha_lt, ha_op, ha_below⟩ := topData ha
  let remap (w : ℕ) : ℕ := if w = 11 + a then 0 else if 11 + a < w then w - 1 else w
  let C' : Circuit :=
    ⟨(C.gates.eraseIdx a).map (fun g => ⟨g.op, g.inputs.map remap⟩), remap C.output⟩
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', List.length_eraseIdx, ha_lt]
  have hAO' : IsAO2 11 C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hL.1.1 g0 (List.mem_of_mem_eraseIdx hg0)
    · intro k hk w hw
      have hk_e : k < (C.gates.eraseIdx a).length := by simpa [C'] using hk
      have hge : C'.gates[k] = ⟨((C.gates.eraseIdx a)[k]).op, ((C.gates.eraseIdx a)[k]).inputs.map remap⟩ := by
        simp [C']
      rw [gateAt_eq hk, hge] at hw
      simp only [List.mem_map] at hw
      obtain ⟨w0, hw0, rfl⟩ := hw
      by_cases hka : k < a
      · rw [List.getElem_eraseIdx_of_lt hk_e hka] at hw0
        have hw0_lt : w0 < 11 + k := hL.1.2.1 k (by omega) w0 (by rw [gateAt_eq (by omega)]; exact hw0)
        simp only [remap]
        split_ifs <;> omega
      · rw [List.getElem_eraseIdx_of_ge hk_e (by omega)] at hw0
        have hk1 : k + 1 < C.gates.length := by
          rw [List.length_eraseIdx_of_lt ha_lt] at hk_e; omega
        have hw0_lt : w0 < 11 + (k + 1) :=
          hL.1.2.1 (k + 1) hk1 w0 (by rw [gateAt_eq hk1]; exact hw0)
        simp only [remap]
        split_ifs <;> omega
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp [hL.1.2.2 g0 (List.mem_of_mem_eraseIdx hg0)]
  have hgood_eval : ∀ (x : Fin 11 → Bool) (w : ℕ),
      w ≠ 11 + a → (∀ k, w = 11 + k → k < C.gates.length → ¬ InCone 11 C a k) →
      val C' (List.ofFn x) (remap w) = val C (List.ofFn x) w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hne hnc
      by_cases hw11 : w < 11
      · have hrm : remap w = w := by simp only [remap]; split_ifs <;> omega
        rw [hrm, val_input (n := 11) (by simp) hw11, val_input (n := 11) (by simp) hw11]
      · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
        by_cases hk : k < C.gates.length
        · have hka_ne : k ≠ a := by omega
          have hnc_k : ¬ InCone 11 C a k := hnc k rfl hk
          have hsub : ∀ u ∈ (gateAt C k).inputs,
              u < 11 + k ∧ u ≠ 11 + a ∧ (∀ k', u = 11 + k' → k' < C.gates.length → ¬ InCone 11 C a k') := by
            intro u hu
            have hult : u < 11 + k := hL.1.2.1 k hk u hu
            refine ⟨hult, ?_, ?_⟩
            · intro hua
              apply hnc_k
              exact (inCone_iff 11 C a k).mpr ⟨hk, a, by omega, hua ▸ hu, Or.inl rfl⟩
            · intro k' huk' hk' hc'
              apply hnc_k
              exact (inCone_iff 11 C a k).mpr ⟨hk, k', by omega, huk' ▸ hu, Or.inr hc'⟩
          by_cases hkl : k < a
          · have hrm : remap (11 + k) = 11 + k := by simp only [remap]; split_ifs <;> omega
            have hk' : k < C'.gates.length := by omega
            have hgate' : gateAt C' k = ⟨(gateAt C k).op, (gateAt C k).inputs.map remap⟩ := by
              rw [gateAt_eq hk', gateAt_eq hk]
              simp [C', List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx_of_lt ha_lt]; omega) hkl]
            rw [hrm, val_gate (n := 11) (by simp) hk', val_gate (n := 11) (by simp) hk, hgate']
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro u hu
            obtain ⟨hult, hune, hunc⟩ := hsub u hu
            have hrm_lt : remap u < 11 + k := by simp only [remap]; split_ifs <;> omega
            simp only [Function.comp_apply, ite_eq_left hrm_lt, ite_eq_left hult]
            exact ih u hult hune hunc
          · have hrm : remap (11 + k) = 11 + (k - 1) := by simp only [remap]; split_ifs <;> omega
            have hk' : k - 1 < C'.gates.length := by omega
            have hgate' : gateAt C' (k - 1) = ⟨(gateAt C k).op, (gateAt C k).inputs.map remap⟩ := by
              rw [gateAt_eq hk', gateAt_eq hk]
              have heq : (k - 1) + 1 = k := by omega
              simp only [C', List.getElem_map]
              rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx_of_lt ha_lt]; omega) (by omega)]
              simp [heq]
            rw [hrm, val_gate (n := 11) (by simp) hk', val_gate (n := 11) (by simp) hk, hgate']
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro u hu
            obtain ⟨hult, hune, hunc⟩ := hsub u hu
            have hrm_lt : remap u < 11 + (k - 1) := by simp only [remap]; split_ifs <;> omega
            simp only [Function.comp_apply, ite_eq_left hrm_lt, ite_eq_left hult]
            exact ih u hult hune hunc
        · have hge1 : 11 + C.gates.length ≤ 11 + k := by omega
          have hge2 : 11 + C'.gates.length ≤ remap (11 + k) := by
            simp only [remap]; split_ifs <;> omega
          rw [val_ge (n := 11) (by simp) hge2, val_ge (n := 11) (by simp) hge1]
  have hgood_out : C.output ≠ 11 + a ∧
      ∀ k, C.output = 11 + k → k < C.gates.length → ¬ InCone 11 C a k := by
    refine ⟨?_, ?_⟩
    · intro heq
      exact hnor (heq ▸ (orReaches_iff 11 C a a).mpr ⟨ha_lt, Or.inl rfl⟩)
    · intro k hk_eq hk_lt hcone
      obtain ⟨j, hj_lt, hj_op, hj_cone⟩ :=
        inCone_not_orReaches_has_and hL.1 a k hk_lt hcone (hk_eq ▸ hnor)
      exact hT a ha_lt j hj_lt ha_op ha_below hj_op hj_cone
  have hfun : circuitFun 11 C' = graphFun G ∅ := by
    rw [← hL.2.1]
    funext x
    exact hgood_eval x C.output hgood_out.1 hgood_out.2
  have hle := hL.2.2 C' hAO' hfun
  have hsize' : C'.size = C.size - 1 := hlen'
  have hpos : 0 < C.size := by change 0 < C.gates.length; omega
  omega

theorem tops_le_orT_add_one {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) (hEdge : ∃ u v : Fin 11, G.Adj u v) :
    (tops G C).card ≤ (orT G C).card + 1 := by
  classical
  have hout_ge : 11 ≤ C.output := by
    by_contra hlt
    push Not at hlt
    let v : Fin 11 := ⟨C.output, hlt⟩
    have hv := congrFun hL.2.1 (pairInput v v)
    have hval : circuitFun 11 C (pairInput v v) = true := by
      change val C (List.ofFn (pairInput v v)) v.val = true
      rw [val_ofFn, pairInput_left]
    rw [hval] at hv
    have hadj := (graphFun_pair G v v).mp hv.symm
    exact G.loopless.irrefl v hadj
  have hout_lt : C.output < 11 + C.gates.length := by
    by_contra hge
    push Not at hge
    obtain ⟨u, v, huv⟩ := hEdge
    have hv := congrFun hL.2.1 (pairInput u v)
    have hval : circuitFun 11 C (pairInput u v) = false :=
      val_ge (n := 11) (by simp) hge
    rw [hval] at hv
    have htrue := (graphFun_pair G u v).mpr huv
    rw [htrue] at hv
    cases hv
  have hstep : ∀ (N : ℕ) (S : Finset ℕ),
      (∀ w ∈ S, w < N ∧ 11 ≤ w ∧ w < 11 + C.gates.length ∧ BelowF G C (w - 11)) →
      ((tops G C).filter fun a => ∃ w ∈ S, OrReaches 11 C w a).card ≤
        S.card + ((orT G C).filter fun k => ∃ w ∈ S, OrReaches 11 C w k).card := by
    intro N
    induction N with
    | zero =>
      intro S hS
      have : S = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by have := (hS w hw).1; omega
      subst this; simp
    | succ N ih =>
      intro S hS
      by_cases hN : N ∈ S
      · obtain ⟨_, hN11, hNlt, hNbel⟩ := hS N hN
        let k := N - 11
        have hkN : N = 11 + k := by omega
        have hklt : k < C.gates.length := by omega
        let S0 := S.erase N
        rcases hL.1.1 _ (gateAt_mem hklt) with hand | hor
        · have hS0 : ∀ w ∈ S0, w < N ∧ 11 ≤ w ∧ w < 11 + C.gates.length ∧ BelowF G C (w - 11) := by
            intro w hw
            have hmem := Finset.mem_of_mem_erase hw
            have hne := Finset.ne_of_mem_erase hw
            have := hS w hmem
            exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
          have hsubT : ((tops G C).filter fun a => ∃ w ∈ S, OrReaches 11 C w a) ⊆
              insert k ((tops G C).filter fun a => ∃ w ∈ S0, OrReaches 11 C w a) := by
            intro a ha
            obtain ⟨haT, w, hwS, hr⟩ := Finset.mem_filter.mp ha
            by_cases hwN : w = N
            · subst hwN
              rw [hkN] at hr
              rcases (orReaches_iff 11 C k a).mp hr with ⟨_, rfl | ⟨hor', _⟩⟩
              · exact Finset.mem_insert_self _ _
              · rw [hand] at hor'; cases hor'
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
                ⟨haT, w, Finset.mem_erase.mpr ⟨hwN, hwS⟩, hr⟩)
          have hsubO : ((orT G C).filter fun g => ∃ w ∈ S0, OrReaches 11 C w g) ⊆
              ((orT G C).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
            intro g hg
            obtain ⟨hgO, w, hw, hr⟩ := Finset.mem_filter.mp hg
            exact Finset.mem_filter.mpr ⟨hgO, w, Finset.mem_of_mem_erase hw, hr⟩
          have hih := ih S0 hS0
          have hc1 := Finset.card_le_card hsubT
          have hc2 := Finset.card_insert_le k ((tops G C).filter fun a => ∃ w ∈ S0, OrReaches 11 C w a)
          have hc3 := Finset.card_le_card hsubO
          have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
          omega
        · have hopnd_below (b : Fin 2) :
              11 ≤ opnd C k b ∧ opnd C k b < 11 + k ∧ BelowF G C (opnd C k b - 11) := by
            have hltb := opndBound hL.1 hklt b
            have hmemb := opndMem hL.1 hklt b
            have h11 : 11 ≤ opnd C k b := by
              by_contra hlt11
              push Not at hlt11
              let v : Fin 11 := ⟨opnd C k b, hlt11⟩
              have hv : gateVal 11 C k (pairInput v v) = true := by
                rw [gateVal_eq_val, val_or (n := 11) (by simp) hklt hor]
                refine ⟨v.val, hmemb, hltb, ?_⟩
                rw [val_ofFn, pairInput_left]
              exact G.loopless.irrefl v ((graphFun_pair G v v).mp (hNbel _ hv))
            refine ⟨h11, hltb, ?_⟩
            intro x hx
            apply hNbel x
            rw [gateVal_eq_val, val_or (n := 11) (by simp) hklt hor]
            refine ⟨opnd C k b, hmemb, hltb, ?_⟩
            have heq : 11 + (opnd C k b - 11) = opnd C k b := by omega
            simpa only [gateVal_eq_val, heq] using hx
          let p := opnd C k 0
          let q := opnd C k 1
          let S' := insert p (insert q S0)
          have hS' : ∀ w ∈ S', w < N ∧ 11 ≤ w ∧ w < 11 + C.gates.length ∧ BelowF G C (w - 11) := by
            intro w hw
            simp only [S', Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · have := hopnd_below 0; exact ⟨by omega, this.1, by omega, this.2.2⟩
            · have := hopnd_below 1; exact ⟨by omega, this.1, by omega, this.2.2⟩
            · have hmem := Finset.mem_of_mem_erase hw
              have hne := Finset.ne_of_mem_erase hw
              have := hS w hmem
              exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
          have hsubT : ((tops G C).filter fun a => ∃ w ∈ S, OrReaches 11 C w a) ⊆
              ((tops G C).filter fun a => ∃ w ∈ S', OrReaches 11 C w a) := by
            intro a ha
            obtain ⟨haT, w, hwS, hr⟩ := Finset.mem_filter.mp ha
            by_cases hwN : w = N
            · subst hwN
              rw [hkN] at hr
              rcases (orReaches_iff 11 C k a).mp hr with ⟨_, rfl | ⟨_, u, hu, _, hru⟩⟩
              · have := (topData haT).2.1; rw [hor] at this; cases this
              · obtain ⟨b, rfl⟩ := inputsAsOpnd hL.1 hklt hu
                refine Finset.mem_filter.mpr ⟨haT, opnd C k b, ?_, hru⟩
                fin_cases b
                · exact Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · exact Finset.mem_filter.mpr ⟨haT, w,
                Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwN, hwS⟩)), hr⟩
          have hkInO : k ∈ ((orT G C).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
            refine Finset.mem_filter.mpr ⟨?_, N, hN, ?_⟩
            · simpa only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] using
                And.intro hklt (And.intro hor hNbel)
            · rw [hkN]; exact (orReaches_iff 11 C k k).mpr ⟨hklt, Or.inl rfl⟩
          have hsubO : ((orT G C).filter fun g => ∃ w ∈ S', OrReaches 11 C w g) ⊆
              (((orT G C).filter fun g => ∃ w ∈ S, OrReaches 11 C w g).erase k) := by
            intro g hg
            obtain ⟨hgO, w, hw', hrg⟩ := Finset.mem_filter.mp hg
            have hwlt : w < N := (hS' w hw').1
            have hle := orStep_le (orReaches_reach g w hrg).1
            have hgne : g ≠ k := by omega
            refine Finset.mem_erase.mpr ⟨hgne, Finset.mem_filter.mpr ⟨hgO, ?_⟩⟩
            simp only [S', Finset.mem_insert] at hw'
            rcases hw' with rfl | rfl | hw0
            · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                ⟨hklt, Or.inr ⟨hor, p, opndMem hL.1 hklt 0, opndBound hL.1 hklt 0, hrg⟩⟩⟩
            · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                ⟨hklt, Or.inr ⟨hor, q, opndMem hL.1 hklt 1, opndBound hL.1 hklt 1, hrg⟩⟩⟩
            · exact ⟨w, Finset.mem_of_mem_erase hw0, hrg⟩
          have hih := ih S' hS'
          have hc1 := Finset.card_le_card hsubT
          have hc2 := Finset.card_le_card hsubO
          have hcO := Finset.card_erase_add_one hkInO
          have hcS' : S'.card ≤ S0.card + 2 := by
            have h1 : S'.card ≤ (insert q S0).card + 1 := Finset.card_insert_le p (insert q S0)
            have h2 : (insert q S0).card ≤ S0.card + 1 := Finset.card_insert_le q S0
            omega
          have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
          omega
      · exact ih S (fun w hw => by
          have := hS w hw
          have hne : w ≠ N := fun h => hN (h ▸ hw)
          exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩)
  have houtBel : BelowF G C (C.output - 11) := by
    intro x hx
    have heq : 11 + (C.output - 11) = C.output := by omega
    have hv : circuitFun 11 C x = true := by
      change val C (List.ofFn x) C.output = true
      rw [← heq]; exact hx
    rw [← hL.2.1]; exact hv
  have hmain := hstep (11 + C.gates.length) {C.output} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hout_lt, hout_ge, hout_lt, houtBel⟩)
  have hTfull : ((tops G C).filter fun a => ∃ w ∈ ({C.output} : Finset ℕ), OrReaches 11 C w a) = tops G C := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton, exists_eq_left]
    exact ⟨fun h => h.1, fun ha => ⟨ha, top_orReaches_output hL hT ha⟩⟩
  have hOsub : ((orT G C).filter fun k => ∃ w ∈ ({C.output} : Finset ℕ), OrReaches 11 C w k) ⊆ orT G C :=
    Finset.filter_subset _ _
  have hOcard := Finset.card_le_card hOsub
  rw [hTfull, Finset.card_singleton] at hmain
  omega

theorem orIn_gate {C : Circuit} {k : ℕ} (u : Fin 11) (hu : u ∈ orIn 11 C (11 + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ c ∈ (gateAt C k).inputs, c < 11 + k ∧ u ∈ orIn 11 C c := by
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with h | ⟨c, hstep, hr⟩
  · have := u.isLt; omega
  · obtain ⟨k', hk', e, hop, hin, hlt⟩ := hstep
    have hkk : k' = k := by omega
    subst hkk
    exact ⟨hk', hop, c, hin, hlt, reach_mem_orIn u hr⟩

theorem orIn_or_eq {C : Circuit} (hAO : IsAO2 11 C) {k : ℕ} (hk : k < C.gates.length)
    (hor : (gateAt C k).op = GateOp.or) :
    orIn 11 C (11 + k) = orIn 11 C (opnd C k 0) ∪ orIn 11 C (opnd C k 1) := by
  ext u
  simp only [Finset.mem_union]
  constructor
  · intro hu
    obtain ⟨_, _, c, hc, _, hcu⟩ := orIn_gate u hu
    obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hk hc
    fin_cases b
    · exact Or.inl hcu
    · exact Or.inr hcu
  · intro hu
    apply reach_mem_orIn
    rcases hu with h0 | h1
    · exact Relation.ReflTransGen.head
        ⟨k, hk, rfl, hor, opndMem hAO hk 0, opndBound hAO hk 0⟩ (mem_orIn_reach u h0)
    · exact Relation.ReflTransGen.head
        ⟨k, hk, rfl, hor, opndMem hAO hk 1, opndBound hAO hk 1⟩ (mem_orIn_reach u h1)

theorem starEdges_le_tops_add_lam {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hC4 : NoFourCycle G) (hAO : IsAO2 11 C) (hV : centreless G C = ∅) :
    (starEdges G C).card ≤ (tops G C).card + (lam G C).card ∧
      ∃ K : Finset (Fin 11), K.card ≤ (tops G C).card ∧
        ∀ u v : Fin 11, (G.deleteEdges ↑(Ustar G C)).Adj u v → u ∈ K ∨ v ∈ K := by
  classical
  have hStars := topStars hC4 hAO
  have hNonemptySide : ∀ a ∈ tops G C, ∀ b : Fin 2, (side (n := 11) C a b).Nonempty := by
    intro a ha b
    by_contra hne
    have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hmem : a ∈ centreless G C := by
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    rw [hV] at hmem
    exact Finset.notMem_empty a hmem
  have hCenterEx : ∀ a ∈ tops G C, ∃ b : Fin 2, ∃ c : Fin 11, side (n := 11) C a b = {c} := by
    intro a ha
    rcases (hStars a ha).2 with h0 | h1
    · have hpos := Finset.card_pos.mpr (hNonemptySide a ha 0)
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (by omega : (side (n := 11) C a 0).card = 1)
      exact ⟨0, c, hc⟩
    · have hpos := Finset.card_pos.mpr (hNonemptySide a ha 1)
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (by omega : (side (n := 11) C a 1).card = 1)
      exact ⟨1, c, hc⟩
  let cb (a : ℕ) : Fin 2 := if h : a ∈ tops G C then (hCenterEx a h).choose else 0
  let center (a : ℕ) : Fin 11 := if h : a ∈ tops G C then (hCenterEx a h).choose_spec.choose else 0
  have hCenterSpec (a : ℕ) (ha : a ∈ tops G C) : side (n := 11) C a (cb a) = {center a} := by
    simp only [cb, center, dite_eq_left ha]
    exact (hCenterEx a ha).choose_spec.choose_spec
  let leafOpnd (a : ℕ) : ℕ := opnd C a (1 - cb a)
  have hLeafAdj (a : ℕ) (ha : a ∈ tops G C) (v : Fin 11) (hv : v ∈ orIn 11 C (leafOpnd a)) :
      G.Adj (center a) v := by
    have hc : center a ∈ side (n := 11) C a (cb a) := by rw [hCenterSpec a ha]; simp
    have hside : v ∈ side (n := 11) C a (1 - cb a) := hv
    generalize hcb : cb a = b at hc hside
    fin_cases b
    · exact topAdj hAO ha hc hside
    · exact (topAdj hAO ha hside hc).symm
  let Tc (c : Fin 11) : Finset ℕ := (tops G C).filter fun a => center a = c
  let Wc (c : Fin 11) : Finset ℕ := (Tc c).image leafOpnd
  let Lc (c : Fin 11) : Finset (Fin 11) := (Wc c).biUnion (orIn 11 C)
  let Lamc (c : Fin 11) : Finset ℕ :=
    (lam G C).filter fun g => 2 ≤ (orIn 11 C (11 + g)).card ∧ ∀ u ∈ orIn 11 C (11 + g), G.Adj c u
  have hBound_c (c : Fin 11) : (Lc c).card ≤ (Wc c).card + (Lamc c).card := by
    have hstep : ∀ (N : ℕ) (S : Finset ℕ),
        (∀ w ∈ S, w < N ∧ ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w) →
        (S.biUnion (orIn 11 C)).card ≤
          S.card + ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g).card := by
      intro N
      induction N with
      | zero =>
        intro S hS
        have : S = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by have := (hS w hw).1; omega
        subst this; simp
      | succ N ih =>
        intro S hS
        by_cases hN : N ∈ S
        · by_cases hN11 : N < 11
          · have hall : ∀ w ∈ S, (orIn 11 C w).card ≤ 1 := by
              intro w hw
              have hw11 : w < 11 := by have := (hS w hw).1; omega
              let v : Fin 11 := ⟨w, hw11⟩
              have hsub : orIn 11 C w ⊆ {v} := by
                intro u hu
                rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with heq | ⟨_, hst, _⟩
                · exact Finset.mem_singleton.mpr (Fin.ext heq.symm)
                · obtain ⟨_, _, h11, _, _, _⟩ := hst; omega
              exact (Finset.card_le_card hsub).trans (by simp)
            calc (S.biUnion (orIn 11 C)).card
                ≤ ∑ w ∈ S, (orIn 11 C w).card := Finset.card_biUnion_le
              _ ≤ ∑ _w ∈ S, 1 := Finset.sum_le_sum hall
              _ = S.card := by simp
              _ ≤ S.card + _ := Nat.le_add_right _ _
          · let k := N - 11
            have hkN : N = 11 + k := by omega
            let S0 := S.erase N
            by_cases hEmpty : orIn 11 C N = ∅
            · have hsubU : S.biUnion (orIn 11 C) ⊆ S0.biUnion (orIn 11 C) := by
                intro u hu
                obtain ⟨w, hwS, hwu⟩ := Finset.mem_biUnion.mp hu
                have hwne : w ≠ N := fun h => by rw [h, hEmpty] at hwu; exact Finset.notMem_empty u hwu
                exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwne, hwS⟩, hwu⟩
              have hsubM : ((Lamc c).filter fun g => ∃ w ∈ S0, OrReaches 11 C w g) ⊆
                  ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
                intro g hg
                obtain ⟨hgL, w, hw, hr⟩ := Finset.mem_filter.mp hg
                exact Finset.mem_filter.mpr ⟨hgL, w, Finset.mem_of_mem_erase hw, hr⟩
              have hih := ih S0 (fun w hw => by
                have hmem := Finset.mem_of_mem_erase hw
                have hne := Finset.ne_of_mem_erase hw
                have := hS w hmem
                exact ⟨by omega, this.2⟩)
              have hc1 := Finset.card_le_card hsubU
              have hc2 := Finset.card_le_card hsubM
              have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
              omega
            · obtain ⟨u0, hu0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
              rw [hkN] at hu0
              obtain ⟨hklt, hor, _, _, _, _⟩ := orIn_gate u0 hu0
              let p := opnd C k 0
              let q := opnd C k 1
              have hUnion : orIn 11 C N = orIn 11 C p ∪ orIn 11 C q := hkN ▸ orIn_or_eq hAO hklt hor
              obtain ⟨_, a0, ha0Tc, hpath0⟩ := hS N hN
              have hStepChild (b : Fin 2) :
                  Relation.ReflTransGen (OrStep 11 C) (leafOpnd a0) (opnd C k b) :=
                hpath0.tail ⟨k, hklt, hkN, hor, opndMem hAO hklt b, opndBound hAO hklt b⟩
              by_cases hSmall : orIn 11 C p = ∅ ∨ orIn 11 C q = ∅ ∨ (orIn 11 C N).card ≤ 1
              · have hPick : ∃ b : Fin 2, orIn 11 C N = orIn 11 C (opnd C k b) := by
                  rcases hSmall with hp0 | hq0 | hc1
                  · exact ⟨1, by rw [hUnion, hp0, Finset.empty_union]⟩
                  · exact ⟨0, by rw [hUnion, hq0, Finset.union_empty]⟩
                  · have hsub : orIn 11 C p ⊆ orIn 11 C N := by rw [hUnion]; exact Finset.subset_union_left
                    by_cases hpne : (orIn 11 C p).Nonempty
                    · exact ⟨0, (Finset.eq_of_subset_of_card_le hsub (by have := Finset.card_pos.mpr hpne; omega)).symm⟩
                    · rw [Finset.not_nonempty_iff_eq_empty] at hpne
                      exact ⟨1, by rw [hUnion, hpne, Finset.empty_union]⟩
                obtain ⟨b, hbEq⟩ := hPick
                let S' := insert (opnd C k b) S0
                have hS' : ∀ w ∈ S', w < N ∧ ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w := by
                  intro w hw
                  rcases Finset.mem_insert.mp hw with rfl | hw0
                  · exact ⟨by have := opndBound hAO hklt b; omega, a0, ha0Tc, hStepChild b⟩
                  · have hmem := Finset.mem_of_mem_erase hw0
                    have hne := Finset.ne_of_mem_erase hw0
                    have := hS w hmem
                    exact ⟨by omega, this.2⟩
                have hsubU : S.biUnion (orIn 11 C) ⊆ S'.biUnion (orIn 11 C) := by
                  intro u hu
                  obtain ⟨w, hwS, hwu⟩ := Finset.mem_biUnion.mp hu
                  by_cases hwN : w = N
                  · subst hwN
                    exact Finset.mem_biUnion.mpr ⟨opnd C k b, Finset.mem_insert_self _ _, hbEq ▸ hwu⟩
                  · exact Finset.mem_biUnion.mpr ⟨w,
                      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwN, hwS⟩), hwu⟩
                have hsubM : ((Lamc c).filter fun g => ∃ w ∈ S', OrReaches 11 C w g) ⊆
                    ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
                  intro g hg
                  obtain ⟨hgL, w, hw', hrg⟩ := Finset.mem_filter.mp hg
                  rcases Finset.mem_insert.mp hw' with rfl | hw0
                  · exact Finset.mem_filter.mpr ⟨hgL, N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                      ⟨hklt, Or.inr ⟨hor, opnd C k b, opndMem hAO hklt b, opndBound hAO hklt b, hrg⟩⟩⟩
                  · exact Finset.mem_filter.mpr ⟨hgL, w, Finset.mem_of_mem_erase hw0, hrg⟩
                have hih := ih S' hS'
                have hc1 := Finset.card_le_card hsubU
                have hc2 := Finset.card_le_card hsubM
                have hcS' : S'.card ≤ S0.card + 1 := Finset.card_insert_le (opnd C k b) S0
                have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
                omega
              · push Not at hSmall
                obtain ⟨hpNon, hqNon, hcard2⟩ := hSmall
                have hkNotBel : ¬ BelowF G C k := by
                  intro hbel
                  have hv : gateVal 11 C k (pairInput u0 u0) = true :=
                    reach_var_val (pairInput u0 u0) (11 + k) u0 (mem_orIn_reach u0 hu0) (pairInput_left u0 u0)
                  exact G.loopless.irrefl u0 ((graphFun_pair G u0 u0).mp (hbel _ hv))
                have hkLam : k ∈ lam G C := by
                  refine Finset.mem_filter.mpr ⟨?_, hpNon, hqNon, ?_⟩
                  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
                      And.intro hklt (And.intro hor hkNotBel)
                  · obtain ⟨ha0T, ha0c⟩ := Finset.mem_filter.mp ha0Tc
                    refine ⟨a0, ha0T, 1 - cb a0, ?_, reach_orReaches hpath0 k hkN hklt⟩
                    have hsub1 : (1 : Fin 2) - (1 - cb a0) = cb a0 := by
                      generalize cb a0 = b; fin_cases b <;> rfl
                    rw [hsub1, hCenterSpec a0 ha0T, Finset.card_singleton]
                have hkAdj : ∀ u ∈ orIn 11 C (11 + k), G.Adj c u := by
                  intro u hu
                  obtain ⟨ha0T, ha0c⟩ := Finset.mem_filter.mp ha0Tc
                  have huLeaf : u ∈ orIn 11 C (leafOpnd a0) :=
                    reach_mem_orIn u (hpath0.trans (hkN ▸ mem_orIn_reach u hu))
                  rw [← ha0c]
                  exact hLeafAdj a0 ha0T u huLeaf
                have hkLamc : k ∈ Lamc c :=
                  Finset.mem_filter.mpr ⟨hkLam, by rw [← hkN]; omega, hkAdj⟩
                have hkInM : k ∈ ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) :=
                  Finset.mem_filter.mpr ⟨hkLamc, N, hN, hkN ▸ (orReaches_iff 11 C k k).mpr ⟨hklt, Or.inl rfl⟩⟩
                let S' := insert p (insert q S0)
                have hS' : ∀ w ∈ S', w < N ∧ ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w := by
                  intro w hw
                  simp only [S', Finset.mem_insert] at hw
                  rcases hw with rfl | rfl | hw0
                  · exact ⟨by have := opndBound hAO hklt 0; omega, a0, ha0Tc, hStepChild 0⟩
                  · exact ⟨by have := opndBound hAO hklt 1; omega, a0, ha0Tc, hStepChild 1⟩
                  · have hmem := Finset.mem_of_mem_erase hw0
                    have hne := Finset.ne_of_mem_erase hw0
                    have := hS w hmem
                    exact ⟨by omega, this.2⟩
                have hsubU : S.biUnion (orIn 11 C) ⊆ S'.biUnion (orIn 11 C) := by
                  intro u hu
                  obtain ⟨w, hwS, hwu⟩ := Finset.mem_biUnion.mp hu
                  by_cases hwN : w = N
                  · subst hwN
                    rw [hUnion, Finset.mem_union] at hwu
                    rcases hwu with hup | huq
                    · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_insert_self _ _, hup⟩
                    · exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), huq⟩
                  · exact Finset.mem_biUnion.mpr ⟨w,
                      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwN, hwS⟩)), hwu⟩
                have hsubM : ((Lamc c).filter fun g => ∃ w ∈ S', OrReaches 11 C w g) ⊆
                    (((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g).erase k) := by
                  intro g hg
                  obtain ⟨hgL, w, hw', hrg⟩ := Finset.mem_filter.mp hg
                  have hwlt : w < N := (hS' w hw').1
                  have hle := orStep_le (orReaches_reach g w hrg).1
                  have hgne : g ≠ k := by omega
                  refine Finset.mem_erase.mpr ⟨hgne, Finset.mem_filter.mpr ⟨hgL, ?_⟩⟩
                  simp only [S', Finset.mem_insert] at hw'
                  rcases hw' with rfl | rfl | hw0
                  · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                      ⟨hklt, Or.inr ⟨hor, p, opndMem hAO hklt 0, opndBound hAO hklt 0, hrg⟩⟩⟩
                  · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                      ⟨hklt, Or.inr ⟨hor, q, opndMem hAO hklt 1, opndBound hAO hklt 1, hrg⟩⟩⟩
                  · exact ⟨w, Finset.mem_of_mem_erase hw0, hrg⟩
                have hih := ih S' hS'
                have hc1 := Finset.card_le_card hsubU
                have hc2 := Finset.card_le_card hsubM
                have hcM := Finset.card_erase_add_one hkInM
                have hcS' : S'.card ≤ S0.card + 2 := by
                  have h1 : S'.card ≤ (insert q S0).card + 1 := Finset.card_insert_le p (insert q S0)
                  have h2 : (insert q S0).card ≤ S0.card + 1 := Finset.card_insert_le q S0
                  omega
                have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
                omega
        · exact ih S (fun w hw => by
            have := hS w hw
            have hne : w ≠ N := fun h => hN (h ▸ hw)
            exact ⟨by omega, this.2⟩)
    have hWlt : ∀ w ∈ Wc c, w < 11 + C.gates.length ∧
        ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w := by
      intro w hw
      obtain ⟨a, haTc, rfl⟩ := Finset.mem_image.mp hw
      have haT := (Finset.mem_filter.mp haTc).1
      have hlt : leafOpnd a < 11 + a := opndBound hAO (topData haT).1 (1 - cb a)
      exact ⟨by have := (topData haT).1; omega, a, haTc, Relation.ReflTransGen.refl⟩
    have hmain := hstep (11 + C.gates.length) (Wc c) hWlt
    have hsub : ((Lamc c).filter fun g => ∃ w ∈ Wc c, OrReaches 11 C w g) ⊆ Lamc c :=
      Finset.filter_subset _ _
    exact hmain.trans (Nat.add_le_add_left (Finset.card_le_card hsub) _)
  have hStarSub : starEdges G C ⊆ Finset.univ.biUnion fun c : Fin 11 => (Lc c).image fun v => s(c, v) := by
    intro e he
    obtain ⟨a, haT, hp⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    dsimp only at hu hv ⊢
    refine Finset.mem_biUnion.mpr ⟨center a, Finset.mem_univ _, ?_⟩
    have haTc : a ∈ Tc (center a) := Finset.mem_filter.mpr ⟨haT, rfl⟩
    have hlo : leafOpnd a ∈ Wc (center a) := Finset.mem_image.mpr ⟨a, haTc, rfl⟩
    have hcs := hCenterSpec a haT
    have hloEq : leafOpnd a = opnd C a (1 - cb a) := rfl
    generalize hcb : cb a = b at hcs hloEq
    fin_cases b
    · change side (n := 11) C a 0 = {center a} at hcs
      change leafOpnd a = opnd C a 1 at hloEq
      rw [hcs, Finset.mem_singleton] at hu
      subst hu
      exact Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨leafOpnd a, hlo, by rw [hloEq]; exact hv⟩, rfl⟩
    · change side (n := 11) C a 1 = {center a} at hcs
      change leafOpnd a = opnd C a 0 at hloEq
      rw [hcs, Finset.mem_singleton] at hv
      subst hv
      exact Finset.mem_image.mpr ⟨u, Finset.mem_biUnion.mpr ⟨leafOpnd a, hlo, by rw [hloEq]; exact hu⟩, Sym2.eq_swap⟩
  have hSumT : ∑ c : Fin 11, (Tc c).card = (tops G C).card := by
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 11)) Tc := by
      intro c1 _ c2 _ hne
      change Disjoint (Tc c1) (Tc c2)
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
    have hpart : (Finset.univ : Finset (Fin 11)).biUnion Tc = tops G C := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Tc, Finset.mem_filter]
      exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨center a, ha, rfl⟩⟩
    rw [← hpart, Finset.card_biUnion hdisj]
  have hSumLam : ∑ c : Fin 11, (Lamc c).card ≤ (lam G C).card := by
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 11)) Lamc := by
      intro c1 _ c2 _ hne
      change Disjoint (Lamc c1) (Lamc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      obtain ⟨_, h2, hadj1⟩ := Finset.mem_filter.mp hg1
      obtain ⟨_, _, hadj2⟩ := Finset.mem_filter.mp hg2
      have hsub : orIn 11 C (11 + g) ⊆ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) :=
        fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1 w hw, hadj2 w hw⟩
      have hle := (Finset.card_le_card hsub).trans (hC4 c1 c2 hne)
      omega
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun c _ => Finset.filter_subset _ _)
  have hStarCard : (starEdges G C).card ≤ (tops G C).card + (lam G C).card := by
    calc (starEdges G C).card
        ≤ (Finset.univ.biUnion fun c : Fin 11 => (Lc c).image fun v => s(c, v)).card :=
          Finset.card_le_card hStarSub
      _ ≤ ∑ c : Fin 11, ((Lc c).image fun v => s(c, v)).card := Finset.card_biUnion_le
      _ ≤ ∑ c : Fin 11, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
      _ ≤ ∑ c : Fin 11, ((Wc c).card + (Lamc c).card) := Finset.sum_le_sum fun c _ => hBound_c c
      _ ≤ ∑ c : Fin 11, ((Tc c).card + (Lamc c).card) :=
          Finset.sum_le_sum fun c _ => Nat.add_le_add_right Finset.card_image_le _
      _ = (∑ c : Fin 11, (Tc c).card) + (∑ c : Fin 11, (Lamc c).card) := Finset.sum_add_distrib
      _ ≤ (tops G C).card + (lam G C).card := by omega
  refine ⟨hStarCard, (tops G C).image center, Finset.card_image_le, ?_⟩
  intro u v huv
  obtain ⟨hadj, hnotU⟩ := SimpleGraph.deleteEdges_adj.mp huv
  have hmemStar : s(u, v) ∈ starEdges G C := by
    by_contra hns
    exact hnotU (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, hns⟩)
  obtain ⟨a, haT, hp⟩ := Finset.mem_biUnion.mp hmemStar
  obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  dsimp only at hx hy heq
  have hca : center a ∈ (tops G C).image center := Finset.mem_image.mpr ⟨a, haT, rfl⟩
  have hcs := hCenterSpec a haT
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
  generalize hcb : cb a = b at hcs
  fin_cases b
  · change side (n := 11) C a 0 = {center a} at hcs
    rw [hcs, Finset.mem_singleton] at hx
    subst hx
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hca
    · exact Or.inr hca
  · change side (n := 11) C a 1 = {center a} at hcs
    rw [hcs, Finset.mem_singleton] at hy
    subst hy
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr hca
    · exact Or.inl hca

theorem pure_lam_wire {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 11 C) {m : ℕ} (hR : orN G C \ lam G C = {m}) :
    ∀ w, w < 11 + m →
      (∃ x : Fin 11 → Bool, val C (List.ofFn x) w = true ∧ graphFun G ∅ x = false) →
      (∀ h ∈ junk G C, w ≠ 11 + h) →
      (∀ x : Fin 11 → Bool, val C (List.ofFn x) w = true ↔ ∃ v ∈ orIn 11 C w, x v = true) ∧
      (orIn 11 C w).Nonempty ∧
      ((∃ v : Fin 11, orIn 11 C w = {v}) ∨ ∃ c : Fin 11, ∀ v ∈ orIn 11 C w, G.Adj c v) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwm hdirty hnojunk
    by_cases hw11 : w < 11
    · let v0 : Fin 11 := ⟨w, hw11⟩
      have horIn : orIn 11 C w = {v0} := by
        ext u
        simp only [Finset.mem_singleton]
        constructor
        · intro hu
          rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with heq | ⟨_, hst, _⟩
          · exact Fin.ext heq.symm
          · obtain ⟨_, _, h11, _, _, _⟩ := hst; omega
        · rintro rfl
          exact reach_mem_orIn v0 Relation.ReflTransGen.refl
      refine ⟨?_, by rw [horIn]; exact Finset.singleton_nonempty v0, Or.inl ⟨v0, horIn⟩⟩
      intro x
      rw [horIn]
      simp only [Finset.mem_singleton, exists_eq_left]
      exact ⟨fun h => by rwa [← val_ofFn C x v0], fun h => by rwa [val_ofFn C x v0]⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      have hklt : k < C.gates.length := by
        by_contra hge
        obtain ⟨x, hx, _⟩ := hdirty
        have hfalse := val_ge (n := 11) (C := C) (x := List.ofFn x) (by simp) (by omega : 11 + C.gates.length ≤ 11 + k)
        rw [hfalse] at hx; cases hx
      have hNotBel : ¬ BelowF G C k := by
        intro hbel
        obtain ⟨x, hx, hfx⟩ := hdirty
        exact Bool.noConfusion (hfx.symm.trans (hbel x hx))
      have hor : (gateAt C k).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hklt) with hand | hor
        · exfalso
          have hkj : k ∈ junk G C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, hand, hklt, hdirty⟩
          exact hnojunk k hkj rfl
        · exact hor
      have hkOrN : k ∈ orN G C := by
        simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hklt (And.intro hor hNotBel)
      have hkLam : k ∈ lam G C := by
        by_contra hnl
        have hkR : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hkOrN, hnl⟩
        rw [hR, Finset.mem_singleton] at hkR
        omega
      obtain ⟨_, hpNon, hqNon, a, haT, b, hcard1, hreach⟩ := Finset.mem_filter.mp hkLam
      have hChild (s : Fin 2) (hsNon : (orIn 11 C (opnd C k s)).Nonempty) :
          (∀ x : Fin 11 → Bool, val C (List.ofFn x) (opnd C k s) = true ↔
            ∃ v ∈ orIn 11 C (opnd C k s), x v = true) := by
        have hlt := opndBound hAO hklt s
        obtain ⟨u, hu⟩ := hsNon
        have hdir : ∃ x : Fin 11 → Bool, val C (List.ofFn x) (opnd C k s) = true ∧ graphFun G ∅ x = false :=
          ⟨pairInput u u, reach_var_val _ _ u (mem_orIn_reach u hu) (pairInput_left u u),
            Bool.eq_false_iff.mpr fun hf => G.loopless.irrefl u ((graphFun_pair G u u).mp hf)⟩
        have hnj : ∀ h ∈ junk G C, opnd C k s ≠ 11 + h := by
          intro h hh heq
          rw [heq, andRawEmpty (junkData hh).2.1] at hu
          exact Finset.notMem_empty u hu
        exact (ih (opnd C k s) hlt (by omega) hdir hnj).1
      have h0 := hChild 0 hpNon
      have h1 := hChild 1 hqNon
      have hUnion := orIn_or_eq hAO hklt hor
      have hVal : ∀ x : Fin 11 → Bool,
          val C (List.ofFn x) (11 + k) = true ↔ ∃ v ∈ orIn 11 C (11 + k), x v = true := by
        intro x
        rw [val_or (n := 11) (by simp) hklt hor, hUnion]
        constructor
        · rintro ⟨u, hu, _, hvu⟩
          obtain ⟨s, rfl⟩ := inputsAsOpnd hAO hklt hu
          fin_cases s
          · obtain ⟨v, hv, hxv⟩ := (h0 x).mp hvu
            exact ⟨v, Finset.mem_union_left _ hv, hxv⟩
          · obtain ⟨v, hv, hxv⟩ := (h1 x).mp hvu
            exact ⟨v, Finset.mem_union_right _ hv, hxv⟩
        · rintro ⟨v, hv, hxv⟩
          rcases Finset.mem_union.mp hv with hv0 | hv1
          · exact ⟨opnd C k 0, opndMem hAO hklt 0, opndBound hAO hklt 0, (h0 x).mpr ⟨v, hv0, hxv⟩⟩
          · exact ⟨opnd C k 1, opndMem hAO hklt 1, opndBound hAO hklt 1, (h1 x).mpr ⟨v, hv1, hxv⟩⟩
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
      have hNbr : ∀ v ∈ orIn 11 C (11 + k), G.Adj c v := by
        intro v hv
        have hvSide : v ∈ side (n := 11) C a b :=
          reach_mem_orIn v ((orReaches_reach k _ hreach).1.trans (mem_orIn_reach v hv))
        have hcSide : c ∈ side (n := 11) C a (1 - b) := by rw [hc]; simp
        fin_cases b
        · exact (topAdj hAO haT hvSide hcSide).symm
        · exact topAdj hAO haT hcSide hvSide
      refine ⟨hVal, ?_, Or.inr ⟨c, hNbr⟩⟩
      rw [hUnion]
      exact hpNon.mono Finset.subset_union_left

theorem gate_partition_card {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] (C : Circuit) :
    (tops G C).card + (junk G C).card + (orT G C).card + (lam G C).card + (orN G C \ lam G C).card ≤ C.size := by
  letI : DecidableEq GateOp := gateOpDecEq
  have hdisj (A B : Finset ℕ) (h : Disjoint A B) : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint h
  have dTJ : Disjoint (tops G C) (junk G C) := Finset.disjoint_left.mpr fun k hk1 hk2 => by
    obtain ⟨_, _, hb⟩ := topData hk1
    obtain ⟨_, _, x, hx, hf⟩ := junkData hk2
    exact Bool.noConfusion (hf.symm.trans (hb x hx))
  have dTJoT : Disjoint (tops G C ∪ junk G C) (orT G C) := Finset.disjoint_left.mpr fun k hk1 hk2 => by
    have ho : (gateAt C k).op = GateOp.or := (Finset.mem_filter.mp hk2).2.1
    rcases Finset.mem_union.mp hk1 with hkT | hkJ
    · rw [(topData hkT).2.1] at ho; cases ho
    · rw [(junkData hkJ).2.1] at ho; cases ho
  have dAndOrN : Disjoint (tops G C ∪ junk G C ∪ orT G C) (orN G C) := Finset.disjoint_left.mpr fun k hk1 hk2 => by
    obtain ⟨_, hoN, hnb⟩ := Finset.mem_filter.mp hk2
    rcases Finset.mem_union.mp hk1 with hkTJ | hkOT
    · rcases Finset.mem_union.mp hkTJ with hkT | hkJ
      · rw [(topData hkT).2.1] at hoN; cases hoN
      · rw [(junkData hkJ).2.1] at hoN; cases hoN
    · exact hnb (Finset.mem_filter.mp hkOT).2.2
  have hLamSub : lam G C ⊆ orN G C := Finset.filter_subset _ _
  have hOrNcard : (orN G C \ lam G C).card + (lam G C).card = (orN G C).card :=
    Finset.card_sdiff_add_card_eq_card hLamSub
  have hSubAll : tops G C ∪ junk G C ∪ orT G C ∪ orN G C ⊆ Finset.range C.gates.length := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk1 | hk4
    · rcases Finset.mem_union.mp hk1 with hk2 | hk3
      · rcases Finset.mem_union.mp hk2 with hkT | hkJ
        · exact Finset.mem_range.mpr (topData hkT).1
        · exact Finset.mem_range.mpr (junkData hkJ).1
      · exact (Finset.mem_filter.mp hk3).1
    · exact (Finset.mem_filter.mp hk4).1
  have hle := Finset.card_le_card hSubAll
  rw [Finset.card_range] at hle
  rw [hdisj _ _ dAndOrN, hdisj _ _ dTJoT, hdisj _ _ dTJ] at hle
  change (tops G C).card + (junk G C).card + (orT G C).card + (lam G C).card +
    (orN G C \ lam G C).card ≤ C.gates.length
  omega

theorem main_proof_G11 (C : Circuit)
    (hLeast : IsLeastAO G11 C) (hTop : TopForm G11 C) (hSizeLt : C.size < 22)
    (hJunkEx : ∃ i j, junk G11 C = {i, j} ∧ InCone 11 C i j)
    (hU2 : (Ustar G11 C).card = 2) :
    2 ≤ 2 * (centreless G11 C).card + (orN G11 C \ lam G11 C).card := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_contra hlt
  obtain ⟨i, j, hJunk, hCone⟩ := hJunkEx
  have hOrder : i < j := coneStrict C j i hCone
  have hJunkCard : (junk G11 C).card = 2 := by
    rw [hJunk, Finset.card_pair (Nat.ne_of_lt hOrder)]
  have hUpos : (Ustar G11 C).Nonempty := Finset.card_pos.mp (by omega)
  have hOff : 1 ≤ 2 * (centreless G11 C).card + (orN G11 C \ lam G11 C).card := by
    rcases residualConnection hLeast hTop hUpos with hv | hr
    · have := Finset.card_pos.mpr hv; omega
    · have := Finset.card_pos.mpr hr; omega
  have hV : centreless G11 C = ∅ := Finset.card_eq_zero.mp (by omega)
  have hR1 : (orN G11 C \ lam G11 C).card = 1 := by
    have hv0 : (centreless G11 C).card = 0 := by rw [hV]; simp
    omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hR1
  have hTleOrT : (tops G11 C).card ≤ (orT G11 C).card + 1 :=
    tops_le_orT_add_one hLeast hTop ⟨0, 9, by decide +kernel⟩
  obtain ⟨hStarLe, K, hKcardLe, hKcov⟩ := starEdges_le_tops_add_lam G11_noFourCycle hLeast.1 hV
  have hDisj5 := gate_partition_card (G := G11) C
  have hStarGe14 : 14 ≤ (starEdges G11 C).card := by
    have hsub : G11.edgeFinset ⊆ starEdges G11 C ∪ Ustar G11 C := by
      intro e he
      by_cases hs : e ∈ starEdges G11 C
      · exact Finset.mem_union_left _ hs
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hs⟩)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [G11_edgeCard] at hle
    omega
  have hTle5 : (tops G11 C).card ≤ 5 := by omega
  have hKge5 : 5 ≤ K.card := by
    let A := (Ustar G11 C).image (fun e => e.out.1)
    have hA : A.card ≤ (Ustar G11 C).card := Finset.card_image_le
    have hUn := Finset.card_union_le K A
    have hfull : G11.IsVertexCover ((K ∪ A : Finset (Fin 11)) : Set _) := by
      intro u v huv
      by_cases he : s(u, v) ∈ Ustar G11 C
      · have hv := Finset.mem_image_of_mem (fun e : Sym2 (Fin 11) => e.out.1) he
        have hs := Sym2.out_fst_mem s(u, v)
        rw [Sym2.mem_iff] at hs
        rcases hs with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hv))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hv))
      · exact (hKcov u v (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩)).imp
          (Finset.mem_union_left A) (Finset.mem_union_left A)
    have hc := G11_fullCover (K ∪ A) hfull
    omega
  have hK5 : K.card = 5 := by omega
  have hKmissed : ∀ p ∈ missedEdges (toMask K), ∃ h1 : p.1 < 11, ∃ h2 : p.2 < 11,
      s(⟨p.1, h1⟩, ⟨p.2, h2⟩) ∈ Ustar G11 C := by
    intro p hp
    simp only [missedEdges, List.mem_filter, Bool.not_eq_true', Bool.or_eq_false_iff] at hp
    obtain ⟨hpg, h1b, h2b⟩ := hp
    obtain ⟨h1, h2⟩ := g11Edges_bounds p hpg
    refine ⟨h1, h2, ?_⟩
    by_contra hnotU
    have hadj : (G11.deleteEdges ↑(Ustar G11 C)).Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ :=
      SimpleGraph.deleteEdges_adj.mpr ⟨g11Edges_adj p hpg h1 h2, hnotU⟩
    rcases hKcov ⟨p.1, h1⟩ ⟨p.2, h2⟩ hadj with hu | hv
    · have := toMask_testBit K ⟨p.1, h1⟩
      simp [hu, h1b] at this
    · have := toMask_testBit K ⟨p.2, h2⟩
      simp [hv, h2b] at this
  have hMissedLenLe : (missedEdges (toMask K)).length ≤ 2 := by
    let f : (Nat × Nat) → Sym2 (Fin 11) := fun p =>
      if h : p.1 < 11 ∧ p.2 < 11 then s(⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else s(0, 0)
    have hnd : ((missedEdges (toMask K)).map f).Nodup := by
      have hsub : (missedEdges (toMask K)).Sublist g11Edges := List.filter_sublist
      have hnd0 : ((missedEdges (toMask K)).map fun p => s(p.1, p.2)).Nodup :=
        g11Edges_nodup_sym2.sublist (hsub.map _)
      have hndList : (missedEdges (toMask K)).Nodup := List.Nodup.of_map _ hnd0
      rw [List.nodup_map_iff_inj_on hndList] at hnd0 ⊢
      intro x hx y hy hxy
      apply hnd0 x hx y hy
      have hx' := g11Edges_bounds x (List.mem_of_mem_filter hx)
      have hy' := g11Edges_bounds y (List.mem_of_mem_filter hy)
      simp only [f, dite_eq_left hx', dite_eq_left hy', Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, Fin.ext_iff] at hxy ⊢
      exact hxy
    have hsubU : ((missedEdges (toMask K)).map f).toFinset ⊆ Ustar G11 C := by
      intro e he
      rw [List.mem_toFinset, List.mem_map] at he
      obtain ⟨p, hp, rfl⟩ := he
      obtain ⟨h1, h2, hmem⟩ := hKmissed p hp
      simpa only [f, dite_eq_left (And.intro h1 h2)] using hmem
    have hle := Finset.card_le_card hsubU
    rw [List.toFinset_card_of_nodup hnd, List.length_map] at hle
    omega
  have hTau5Check : ∃ e1 e2, missedEdges (toMask K) = [e1, e2] ∧ (e1, e2) ∈ tau5Pairs := by
    have hall := List.all_eq_true.mp checkTau5_ok (toMask K) (List.mem_range.mpr (toMask_lt K))
    simp only [popcount11_toMask, hK5, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hall
    cases hme : missedEdges (toMask K) with
    | nil => rw [hme] at hall; simp at hall
    | cons e1 rest =>
      cases rest with
      | nil => rw [hme] at hall; simp at hall
      | cons e2 rest2 =>
        cases rest2 with
        | nil =>
          rw [hme] at hall
          exact ⟨e1, e2, rfl, decide_eq_true_eq.mp hall⟩
        | cons e3 rest3 =>
          rw [hme] at hMissedLenLe; simp at hMissedLenLe
  obtain ⟨e1, e2, hmeEq, hInTau5⟩ := hTau5Check
  obtain ⟨hu1, hv1lt, he1U⟩ := hKmissed e1 (by rw [hmeEq]; simp)
  obtain ⟨hu2, hv2lt, he2U⟩ := hKmissed e2 (by rw [hmeEq]; simp)
  have nonemptySide (a : ℕ) (ha : a ∈ tops G11 C) (b : Fin 2) : (orIn 11 C (opnd C a b)).Nonempty := by
    by_contra hne
    have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hmem : a ∈ centreless G11 C := by
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    rw [hV] at hmem
    exact Finset.notMem_empty a hmem
  have junction (u v : Fin 11) (he : s(u, v) ∈ Ustar G11 C) :
      ∃ a ∈ tops G11 C, ∃ b : Fin 2, ∃ h ∈ junk G11 C,
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) m ∧
        gateVal 11 C h (pairInput u v) = true ∧
        Relation.ReflTransGen (OrStep 11 C) (opnd C a b) (11 + m) ∧
        11 + h ∈ (gateAt C m).inputs := by
    obtain ⟨a, ha, b, h, hh, hv, hr, hhval⟩ := residualTraceWithTop hLeast hTop he
    rcases lastOrBefore (orReaches_reach h _ hr).1 with heq | ⟨k, hk, hop, hin, hlt', hpath⟩
    · have hne := nonemptySide a ha b
      rw [heq, andRawEmpty (junkData hh).2.1] at hne
      exact (Finset.not_nonempty_empty hne).elim
    · have hkR : k ∈ orN G11 C \ lam G11 C := lastOrOutside hLeast.1 hh hk hop hin hlt'
      have hkm : k = m := by simpa only [hm, Finset.mem_singleton] using hkR
      subst k
      exact ⟨a, ha, b, h, hh, hv, reach_orReaches hpath m rfl hk, hhval, hpath, hin⟩
  have hmData : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G11 C m := by
    have hmem : m ∈ orN G11 C \ lam G11 C := by simp [hm]
    have ho := (Finset.mem_sdiff.mp hmem).1
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using ho
  obtain ⟨hlen, ho, _⟩ := hmData
  obtain ⟨a1, ha1, b1, h0, hh0, hva1, hr1, hh0v1, hp1, hread0⟩ := junction ⟨e1.1, hu1⟩ ⟨e1.2, hv1lt⟩ he1U
  have hmOr : (orIn 11 C (11 + m)).Nonempty := by
    by_contra hno
    have hme := Finset.not_nonempty_iff_eq_empty.mp hno
    rcases Relation.ReflTransGen.cases_tail hp1 with heq | ⟨w, _, hs⟩
    · have hn := nonemptySide a1 ha1 b1
      rw [← heq, hme] at hn
      exact Finset.not_nonempty_empty hn
    · obtain ⟨k, hk, rfl, hkop, hkmem, hklt⟩ := hs
      obtain ⟨_, _, x, hd, hx⟩ := junkData hh0
      have hmv : val C (List.ofFn x) (11 + m) = true :=
        (val_or (by simp) hlen ho).mpr ⟨11 + h0, hread0, hLeast.1.2.1 m hlen _ hread0, hd⟩
      have hkv : val C (List.ofFn x) (11 + k) = true :=
        (val_or (by simp) hk hkop).mpr ⟨11 + m, hkmem, hklt, hmv⟩
      have hkNotBelow : ¬ BelowF G11 C k := fun hb =>
        Bool.noConfusion (hx.symm.trans (hb x hkv))
      have hkR : k ∈ orN G11 C \ lam G11 C := by
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, ?_⟩
        · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
            And.intro hk (And.intro hkop hkNotBelow)
        · intro hlam
          obtain ⟨_, h0', h1', _⟩ := Finset.mem_filter.mp hlam
          obtain ⟨b', hb'⟩ := inputsAsOpnd hLeast.1 hk hkmem
          have hne' : (orIn 11 C (opnd C k b')).Nonempty := by
            fin_cases b'
            · exact h0'
            · exact h1'
          rw [← hb', hme] at hne'
          exact Finset.not_nonempty_empty hne'
      have : k = m := by simpa only [hm, Finset.mem_singleton] using hkR
      omega
  have huniq (h' : ℕ) (hh' : h' ∈ junk G11 C) (hd : 11 + h' ∈ (gateAt C m).inputs) : h' = h0 := by
    by_contra hne
    obtain ⟨p, q, hpq⟩ := binaryInputs hLeast.1 hlen
    have he1 := andRawEmpty (n := 11) (junkData hh0).2.1
    have he2 := andRawEmpty (n := 11) (junkData hh').2.1
    have hshape : (gateAt C m).inputs = [11 + h0, 11 + h'] ∨
        (gateAt C m).inputs = [11 + h', 11 + h0] := by
      rw [hpq] at hread0 hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hread0 hd
      rcases hread0 with h1 | h1 <;> rcases hd with h2 | h2
      · omega
      · exact Or.inl (by rw [hpq, ← h1, ← h2])
      · exact Or.inr (by rw [hpq, ← h2, ← h1])
      · omega
    obtain ⟨t, ht⟩ := hmOr
    obtain ⟨_, _, w, hw, _, htw⟩ := orIn_gate t ht
    rcases hshape with hs | hs <;> rw [hs] at hw <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;>
      rcases hw with rfl | rfl <;> simp [he1, he2] at htw
  obtain ⟨a2, ha2, b2, h0', hh0', hva2, hr2, hh0v2, _, hread0'⟩ := junction ⟨e2.1, hu2⟩ ⟨e2.2, hv2lt⟩ he2U
  have heqh0 : h0' = h0 := huniq h0' hh0' hread0'
  subst h0'
  obtain ⟨z, hz⟩ := hmOr
  have extractW (u v : Fin 11) (heU : s(u, v) ∈ Ustar G11 C) (a : ℕ) (ha : a ∈ tops G11 C) (b : Fin 2)
      (hva : gateVal 11 C a (pairInput u v) = true) (hrm : OrReaches 11 C (opnd C a b) m) :
      z ≠ u ∧ z ≠ v ∧ ∃ w : Fin 11, (w = u ∨ w = v) ∧ G11.Adj z w ∧
        ∀ x : Fin 11 → Bool, gateVal 11 C h0 x = true → x w = true → graphFun G11 ∅ x = true := by
    have hzSide : z ∈ side (n := 11) C a b :=
      reach_mem_orIn z ((orReaches_reach m _ hrm).1.trans (mem_orIn_reach z hz))
    have hNotOtherM : ¬ OrReaches 11 C (opnd C a (1 - b)) m := by
      intro hrm'
      have hzSide' : z ∈ side (n := 11) C a (1 - b) :=
        reach_mem_orIn z ((orReaches_reach m _ hrm').1.trans (mem_orIn_reach z hz))
      have : G11.Adj z z := by
        fin_cases b
        · exact topAdj hLeast.1 ha hzSide hzSide'
        · exact topAdj hLeast.1 ha hzSide' hzSide
      exact G11.loopless.irrefl z this
    obtain ⟨hl, hop, hbel⟩ := topData ha
    have hvOther := (andValOperands hLeast.1 hl hop (pairInput u v)).mp hva (1 - b)
    rcases operandSupport hLeast.1 hTop hl hop hvOther with ⟨w, hwSide, hwu⟩ | ⟨h', hh', hrh', _⟩
    · have hzw : G11.Adj z w := by
        fin_cases b
        · exact topAdj hLeast.1 ha hzSide hwSide
        · exact (topAdj hLeast.1 ha hwSide hzSide).symm
      have hneU : z ≠ u := by
        intro hzu
        have hmiss := (Finset.mem_sdiff.mp heU).2
        apply hmiss
        unfold starEdges
        rcases hwu with hwu | hwv
        · rw [hzu, hwu] at hzw
          exact (G11.loopless.irrefl u hzw).elim
        · fin_cases b
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(z, w), Finset.mem_product.mpr ⟨hzSide, hwSide⟩, by rw [hzu, hwv]⟩⟩
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(w, z), Finset.mem_product.mpr ⟨hwSide, hzSide⟩, by rw [hzu, hwv, Sym2.eq_swap]⟩⟩
      have hneV : z ≠ v := by
        intro hzv
        have hmiss := (Finset.mem_sdiff.mp heU).2
        apply hmiss
        unfold starEdges
        rcases hwu with hwu | hwv
        · fin_cases b
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(z, w), Finset.mem_product.mpr ⟨hzSide, hwSide⟩, by rw [hzv, hwu, Sym2.eq_swap]⟩⟩
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(w, z), Finset.mem_product.mpr ⟨hwSide, hzSide⟩, by rw [hzv, hwu]⟩⟩
        · rw [hzv, hwv] at hzw
          exact (G11.loopless.irrefl v hzw).elim
      refine ⟨hneU, hneV, w, hwu, hzw, ?_⟩
      intro x hh0x hxw
      apply hbel x
      have hmx : val C (List.ofFn x) (11 + m) = true :=
        (val_or (by simp) hlen ho).mpr ⟨11 + h0, hread0, hLeast.1.2.1 m hlen _ hread0, hh0x⟩
      have hbx : val C (List.ofFn x) (opnd C a b) = true :=
        orStep_up (by simp) (orReaches_reach m _ hrm).1 hmx
      have h1bx : val C (List.ofFn x) (opnd C a (1 - b)) = true := sideVal hwSide hxw
      rw [andValBoth hLeast.1 hl hop x]
      fin_cases b
      · exact ⟨hbx, h1bx⟩
      · exact ⟨h1bx, hbx⟩
    · exfalso
      rcases lastOrBefore (orReaches_reach h' _ hrh').1 with heq | ⟨k, hk, hkop, hin, hlt', hpath⟩
      · have hne := nonemptySide a ha (1 - b)
        rw [heq, andRawEmpty (junkData hh').2.1] at hne
        exact Finset.not_nonempty_empty hne
      · have hkR : k ∈ orN G11 C \ lam G11 C := lastOrOutside hLeast.1 hh' hk hkop hin hlt'
        have hkm : k = m := by simpa only [hm, Finset.mem_singleton] using hkR
        subst k
        exact hNotOtherM (reach_orReaches hpath m rfl hk)
  obtain ⟨hzne1a, hzne1b, w1, hw1m, hzw1, hw1max⟩ := extractW ⟨e1.1, hu1⟩ ⟨e1.2, hv1lt⟩ he1U a1 ha1 b1 hva1 hr1
  obtain ⟨hzne2a, hzne2b, w2, hw2m, hzw2, hw2max⟩ := extractW ⟨e2.1, hu2⟩ ⟨e2.2, hv2lt⟩ he2U a2 ha2 b2 hva2 hr2
  have hh0_lt_m : h0 < m := by
    have := hLeast.1.2.1 m hlen (11 + h0) hread0; omega
  have hi_lt_m : i < m := by
    have hmem : h0 ∈ ({i, j} : Finset ℕ) := hJunk ▸ hh0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> omega
  have hPureOpnd (g : ℕ) (hg : g ∈ junk G11 C) (hgm : g < m) (b : Fin 2) (hni : opnd C g b ≠ 11 + i)
      (hnj : opnd C g b ≠ 11 + j) :
      (∀ x : Fin 11 → Bool, val C (List.ofFn x) (opnd C g b) = true ↔
        ∃ v ∈ orIn 11 C (opnd C g b), x v = true) ∧
      (orIn 11 C (opnd C g b)).Nonempty ∧
      ((∃ v : Fin 11, orIn 11 C (opnd C g b) = {v}) ∨
        ∃ c : Fin 11, ∀ v ∈ orIn 11 C (opnd C g b), G11.Adj c v) := by
    obtain ⟨hglt, hgop, x0, hx0, hfx0⟩ := junkData hg
    have hlt' := opndBound hLeast.1 hglt b
    have hdir : ∃ x, val C (List.ofFn x) (opnd C g b) = true ∧ graphFun G11 ∅ x = false :=
      ⟨x0, (andValOperands hLeast.1 hglt hgop x0).mp hx0 b, hfx0⟩
    have hno : ∀ h' ∈ junk G11 C, opnd C g b ≠ 11 + h' := by
      intro h' hh'
      have hmem : h' ∈ ({i, j} : Finset ℕ) := hJunk ▸ hh'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact hni
      · exact hnj
    exact pure_lam_wire hLeast.1 hm (opnd C g b) (by omega) hdir hno
  have hiJ : i ∈ junk G11 C := by rw [hJunk]; simp
  have hi_repr : ∃ A B : Finset (Fin 11),
      (∀ x, gateVal 11 C i x = true ↔ (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true)) ∧
      toMask A ∈ lamList ∧ toMask B ∈ lamList := by
    have hil := (junkData hiJ).1
    have hio := (junkData hiJ).2.1
    have hb0 := opndBound hLeast.1 hil 0
    have hb1 := opndBound hLeast.1 hil 1
    obtain ⟨h0v, h0n, h0l⟩ := hPureOpnd i hiJ hi_lt_m 0 (by omega) (by omega)
    obtain ⟨h1v, h1n, h1l⟩ := hPureOpnd i hiJ hi_lt_m 1 (by omega) (by omega)
    refine ⟨orIn 11 C (opnd C i 0), orIn 11 C (opnd C i 1), ?_,
      toMask_mem_lamList _ h0n h0l, toMask_mem_lamList _ h1n h1l⟩
    intro x
    rw [andValBoth hLeast.1 hil hio x, h0v x, h1v x]
  have hh0_repr : ∃ A B D : Finset (Fin 11),
      (∀ x, gateVal 11 C h0 x = true ↔
        (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true) ∧ (∃ v ∈ D, x v = true)) ∧
      toMask A ∈ lamList ∧ toMask B ∈ lamList ∧ toMask D ∈ lamList := by
    obtain ⟨Ai, Bi, hiV, hAi, hBi⟩ := hi_repr
    have hmem : h0 ∈ ({i, j} : Finset ℕ) := hJunk ▸ hh0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hh0i | hh0j
    · subst hh0i
      refine ⟨Ai, Bi, Bi, ?_, hAi, hBi, hBi⟩
      intro x
      rw [hiV x]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, h2⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
    · have hjl := (junkData hh0).1
      have hjo := (junkData hh0).2.1
      have hb0 := opndBound hLeast.1 hjl 0
      have hb1 := opndBound hLeast.1 hjl 1
      by_cases h0i : opnd C h0 0 = 11 + i
      · by_cases h1i : opnd C h0 1 = 11 + i
        · refine ⟨Ai, Bi, Bi, ?_, hAi, hBi, hBi⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h0i, h1i]
          change (gateVal 11 C i x = true ∧ gateVal 11 C i x = true) ↔ _
          rw [hiV x]
          exact ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨h1, h2, h2⟩, fun ⟨h1, h2, _⟩ => ⟨⟨h1, h2⟩, ⟨h1, h2⟩⟩⟩
        · obtain ⟨h1v, h1n, h1l⟩ := hPureOpnd h0 hh0 hh0_lt_m 1 h1i (by omega)
          refine ⟨Ai, Bi, orIn 11 C (opnd C h0 1), ?_, hAi, hBi, toMask_mem_lamList _ h1n h1l⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h0i]
          change (gateVal 11 C i x = true ∧ val C (List.ofFn x) (opnd C h0 1) = true) ↔ _
          rw [hiV x, h1v x]
          exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
      · by_cases h1i : opnd C h0 1 = 11 + i
        · obtain ⟨h0v, h0n, h0l⟩ := hPureOpnd h0 hh0 hh0_lt_m 0 h0i (by omega)
          refine ⟨Ai, Bi, orIn 11 C (opnd C h0 0), ?_, hAi, hBi, toMask_mem_lamList _ h0n h0l⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h1i]
          change (val C (List.ofFn x) (opnd C h0 0) = true ∧ gateVal 11 C i x = true) ↔ _
          rw [hiV x, h0v x]
          exact ⟨fun ⟨h3, ⟨h1, h2⟩⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h3, ⟨h1, h2⟩⟩⟩
        · obtain ⟨h0v, h0n, h0l⟩ := hPureOpnd h0 hh0 hh0_lt_m 0 h0i (by omega)
          obtain ⟨h1v, h1n, h1l⟩ := hPureOpnd h0 hh0 hh0_lt_m 1 h1i (by omega)
          refine ⟨orIn 11 C (opnd C h0 0), orIn 11 C (opnd C h0 1), orIn 11 C (opnd C h0 1), ?_,
            toMask_mem_lamList _ h0n h0l, toMask_mem_lamList _ h1n h1l, toMask_mem_lamList _ h1n h1l⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h0v x, h1v x]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, h2⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
  obtain ⟨A, B, D, hABD, hAl, hBl, hDl⟩ := hh0_repr
  have hHits (S : Finset (Fin 11)) (u v : Fin 11) (h : ∃ t ∈ S, pairInput u v t = true) :
      (toMask S &&& ((1 <<< u.val) ||| (1 <<< v.val))) != 0 := by
    obtain ⟨t, ht, hpt⟩ := h
    rw [pairInput_true] at hpt
    exact bne_iff_ne.mpr (toMask_and_edge_ne_zero S u v (by rcases hpt with rfl | rfl <;> [exact Or.inl ht; exact Or.inr ht]))
  have h1 := (hABD (pairInput ⟨e1.1, hu1⟩ ⟨e1.2, hv1lt⟩)).mp hh0v1
  have h2 := (hABD (pairInput ⟨e2.1, hu2⟩ ⟨e2.2, hv2lt⟩)).mp hh0v2
  let m1 := (1 <<< e1.1) ||| (1 <<< e1.2)
  let m2 := (1 <<< e2.1) ||| (1 <<< e2.2)
  let cand := lamList.filter fun s => (s &&& m1) != 0 && (s &&& m2) != 0
  have hAc : toMask A ∈ cand := List.mem_filter.mpr ⟨hAl, by simp [m1, m2, hHits A _ _ h1.1, hHits A _ _ h2.1]⟩
  have hBc : toMask B ∈ cand := List.mem_filter.mpr ⟨hBl, by simp [m1, m2, hHits B _ _ h1.2.1, hHits B _ _ h2.2.1]⟩
  have hDc : toMask D ∈ cand := List.mem_filter.mpr ⟨hDl, by simp [m1, m2, hHits D _ _ h1.2.2, hHits D _ _ h2.2.2]⟩
  have hCheck := List.all_eq_true.mp checkAllTriples_ok (e1, e2) hInTau5
  unfold checkPair at hCheck
  have hCheckZ := List.all_eq_true.mp hCheck z.val (List.mem_range.mpr z.isLt)
  have hzNotE : (z.val == e1.1 || z.val == e1.2 || z.val == e2.1 || z.val == e2.2) = false := by
    have h1a : z.val ≠ e1.1 := fun h => hzne1a (Fin.ext h)
    have h1b : z.val ≠ e1.2 := fun h => hzne1b (Fin.ext h)
    have h2a : z.val ≠ e2.1 := fun h => hzne2a (Fin.ext h)
    have h2b : z.val ≠ e2.2 := fun h => hzne2b (Fin.ext h)
    simp [h1a, h1b, h2a, h2b]
  simp only [hzNotE, Bool.false_eq_true, ↓reduceIte] at hCheckZ
  have hw1In : w1.val ∈ [e1.1, e1.2] := by
    rcases hw1m with rfl | rfl <;> simp
  have hw2In : w2.val ∈ [e2.1, e2.2] := by
    rcases hw2m with rfl | rfl <;> simp
  have hCheckW1 := List.all_eq_true.mp hCheckZ w1.val hw1In
  have hzw1b : (adjMask z.val).testBit w1.val = true := (G11_adj_iff_adjMask z w1).mp hzw1
  simp only [hzw1b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCheckW1
  have hCheckW2 := List.all_eq_true.mp hCheckW1 w2.val hw2In
  have hzw2b : (adjMask z.val).testBit w2.val = true := (G11_adj_iff_adjMask z w2).mp hzw2
  simp only [hzw2b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCheckW2
  have hTrip := List.all_eq_true.mp
    (List.all_eq_true.mp
      (List.all_eq_true.mp hCheckW2 (toMask A) hAc) (toMask B) hBc) (toMask D) hDc
  have hHasInd : hasIndep (toMask A) (toMask B) (toMask D) = true := by
    obtain ⟨_, _, x, hx, hfx⟩ := junkData hh0
    obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩, ⟨d, hd, hxd⟩⟩ := (hABD x).mp hx
    have hnoAdj (u v : Fin 11) (hu : x u = true) (hv : x v = true) : ¬ G11.Adj u v := by
      intro hadj
      have : graphFun G11 ∅ x = true := by
        simp only [graphFun]; exact decide_eq_true ⟨u, v, hadj, hu, hv⟩
      rw [this] at hfx; cases hfx
    have hab : (adjMask a.val).testBit b.val = false :=
      Bool.eq_false_iff.mpr fun h => hnoAdj a b hxa hxb ((G11_adj_iff_adjMask a b).mpr h)
    have had : (adjMask a.val).testBit d.val = false :=
      Bool.eq_false_iff.mpr fun h => hnoAdj a d hxa hxd ((G11_adj_iff_adjMask a d).mpr h)
    have hbd : (adjMask b.val).testBit d.val = false :=
      Bool.eq_false_iff.mpr fun h => hnoAdj b d hxb hxd ((G11_adj_iff_adjMask b d).mpr h)
    unfold hasIndep
    refine List.any_eq_true.mpr ⟨a.val, List.mem_range.mpr a.isLt, ?_⟩
    rw [toMask_testBit, decide_eq_true ha, Bool.true_and]
    refine List.any_eq_true.mpr ⟨b.val, List.mem_range.mpr b.isLt, ?_⟩
    rw [toMask_testBit, decide_eq_true hb, hab, Bool.not_false, Bool.true_and, Bool.true_and]
    refine List.any_eq_true.mpr ⟨d.val, List.mem_range.mpr d.isLt, ?_⟩
    rw [toMask_testBit, decide_eq_true hd, Nat.testBit_or, had, hbd]
    rfl
  have hNoBad (w : Fin 11) (hwmax : ∀ x, gateVal 11 C h0 x = true → x w = true → graphFun G11 ∅ x = true) :
      hasIndepNotAdj (toMask A) (toMask B) (toMask D) w.val = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    unfold hasIndepNotAdj at htrue
    obtain ⟨a, haR, haB⟩ := List.any_eq_true.mp htrue
    simp only [Bool.and_eq_true] at haB
    obtain ⟨haBit, hBex⟩ := haB
    obtain ⟨b, hbR, hbB⟩ := List.any_eq_true.mp hBex
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbB
    obtain ⟨⟨hbBit, hab⟩, hDex⟩ := hbB
    obtain ⟨d, hdR, hdB⟩ := List.any_eq_true.mp hDex
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.testBit_or, Bool.or_eq_false_iff] at hdB
    obtain ⟨⟨hdBit, had, hbd⟩, ⟨haw, hbw⟩, hdw⟩ := hdB
    let af : Fin 11 := ⟨a, List.mem_range.mp haR⟩
    let bf : Fin 11 := ⟨b, List.mem_range.mp hbR⟩
    let df : Fin 11 := ⟨d, List.mem_range.mp hdR⟩
    have haA : af ∈ A := of_decide_eq_true (by rw [← toMask_testBit A af]; exact haBit)
    have hbB' : bf ∈ B := of_decide_eq_true (by rw [← toMask_testBit B bf]; exact hbBit)
    have hdD : df ∈ D := of_decide_eq_true (by rw [← toMask_testBit D df]; exact hdBit)
    let x : Fin 11 → Bool := fun v => decide (v = af ∨ v = bf ∨ v = df ∨ v = w)
    have hh0x : gateVal 11 C h0 x = true :=
      (hABD x).mpr ⟨⟨af, haA, by simp [x]⟩, ⟨bf, hbB', by simp [x]⟩, ⟨df, hdD, by simp [x]⟩⟩
    have hfx : graphFun G11 ∅ x = true := hwmax x hh0x (by simp [x])
    have hfx' : ∃ u v : Fin 11, G11.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hfx
    obtain ⟨u, v, huv, hxu, hxv⟩ := hfx'
    simp only [x, decide_eq_true_eq] at hxu hxv
    have noAdj (p q : Fin 11) (h0 : (adjMask p.val).testBit q.val = false) : ¬ G11.Adj p q :=
      fun h => by rw [(G11_adj_iff_adjMask p q).mp h] at h0; cases h0
    rcases hxu with hu | hu | hu | hu <;> rcases hxv with hv | hv | hv | hv
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
    · rw [hu, hv] at huv; exact noAdj af bf hab huv
    · rw [hu, hv] at huv; exact noAdj af df had huv
    · rw [hu, hv] at huv; exact noAdj af w haw huv
    · rw [hu, hv] at huv; exact noAdj af bf hab huv.symm
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
    · rw [hu, hv] at huv; exact noAdj bf df hbd huv
    · rw [hu, hv] at huv; exact noAdj bf w hbw huv
    · rw [hu, hv] at huv; exact noAdj af df had huv.symm
    · rw [hu, hv] at huv; exact noAdj bf df hbd huv.symm
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
    · rw [hu, hv] at huv; exact noAdj df w hdw huv
    · rw [hu, hv] at huv; exact noAdj af w haw huv.symm
    · rw [hu, hv] at huv; exact noAdj bf w hbw huv.symm
    · rw [hu, hv] at huv; exact noAdj df w hdw huv.symm
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
  rw [hHasInd, hNoBad w1 hw1max, hNoBad w2 hw2max] at hTrip
  cases hTrip

theorem main_proof (G : SimpleGraph (Fin 11)) [inst : DecidableRel G.Adj] (C : Circuit)
    (hG : G = G11) (hLeast : IsLeastAO G C) (hTop : TopForm G C) (hSizeLt : C.size < 22)
    (hJunkEx : ∃ i j, junk G C = {i, j} ∧ InCone 11 C i j)
    (hU2 : (Ustar G C).card = 2) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
  subst hG
  convert main_proof_G11 C (by convert hLeast) (by convert hTop) hSizeLt
    (by convert hJunkEx) (by convert hU2)

end PEqualNP.Outside.L_meta_17251

theorem PEqualNP.Outside.L_meta_17251 : (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → x3.size < (22 : ℕ) → (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) → (PEqualNP.TopForm.Ustar x1 x3).card = (2 : ℕ) → (2 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) :=
  PEqualNP.Outside.L_meta_17251.main_proof
