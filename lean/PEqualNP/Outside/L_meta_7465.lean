import PEqualNP.Defs

/-!
The circuit evaluation and routing lemmas follow the checked proof of L-meta-5869,
which credits L-meta-1490 and L-meta-4901. The oriented old-edge stars use the
centre selection from checked L-meta-6238. The raw-support union follows checked
L-meta-6240. The four edge triples are those specified in the posted statement.
The argument below supplies the exceptional-OR decomposition, matching-clause
bound and finite symbolic gate calculation.
-/

namespace PEqualNP.Outside.L_meta_7465_aux.Routing

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
      gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
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
    · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩


lemma opposite (b c : Fin 2) : c = b ∨ c = 1 - b := by
  revert b c
  decide

lemma topSides (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hc : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  rw [empty] at hc
  exact Finset.notMem_empty _ hc

lemma orData {m : ℕ} (hm : m ∈ orN G C \ lam G C) :
    m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
  simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    (Finset.mem_sdiff.mp hm).1

lemma emptyInputOutside (ao : IsAO2 n C) {j m : ℕ}
    (dirty : ¬ BelowF G C j) (empty : orIn n C (n + j) = ∅)
    (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hin : n + j ∈ (gateAt C m).inputs) :
    m ∈ orN G C \ lam G C := by
  have hbad : ¬ BelowF G C m := by
    intro hb
    apply dirty
    intro x hx
    exact hb x ((val_or (n := n) (by simp) hm hop).mpr
      ⟨_, hin, ao.2.1 _ hm _ hin, hx⟩)
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hop hbad)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb⟩ := inputsAsOpnd ao hm hin
    have hne : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← hb, empty] at hne
    exact Finset.not_nonempty_empty hne

lemma residualPath (ao : IsAO2 n C) (empty : centreless G C = ∅)
    {a j : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hj : j ∈ junk G C)
    (path : OrReaches n C (opnd C a b) j) :
    ∃ m ∈ orN G C \ lam G C, n + j ∈ (gateAt C m).inputs ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) := by
  rcases lastOrBefore (orReaches_reach j _ path).1 with he | ⟨m, hm, hop, hin, hlt, hp⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, andRawEmpty (junkData hj).2.1] at hne
    exact (Finset.not_nonempty_empty hne).elim
  · exact ⟨m, lastOrOutside ao hj hm hop hin hlt, hin, hp⟩

lemma mixingRaw (ao : IsAO2 n C) (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    (orIn n C (n + m)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hz
  rcases lastOrBefore path with he | ⟨k, hk, hop, hin, hlt, _⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, hz] at hne
    exact Finset.not_nonempty_empty hne
  · have hk' := emptyInputOutside ao (orData hm).2.2 hz hk hop hin
    rw [only, Finset.mem_singleton] at hk'
    omega

lemma singleJunkInput (ao : IsAO2 n C) {m j k : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hne : (orIn n C (n + m)).Nonempty)
    (hj : j ∈ junk G C) (hk : k ∈ junk G C)
    (hjin : n + j ∈ (gateAt C m).inputs) (hkin : n + k ∈ (gateAt C m).inputs) :
    j = k := by
  by_contra hjk
  obtain ⟨p, q, hpq⟩ := binaryInputs ao (orData hm).1
  have hinputs : ∀ w ∈ (gateAt C m).inputs, w = n + j ∨ w = n + k := by
    intro w hw
    simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hjin hkin hw
    omega
  obtain ⟨t, ht⟩ := hne
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with he | ⟨w, hs, hrest⟩
  · have := t.isLt
    omega
  · obtain ⟨l, _, he, _, hin, _⟩ := hs
    have hl : l = m := by omega
    subst l
    have ht' := reach_mem_orIn t hrest
    rcases hinputs w hin with rfl | rfl
    · rw [andRawEmpty (junkData hj).2.1] at ht'
      exact Finset.notMem_empty _ ht'
    · rw [andRawEmpty (junkData hk).2.1] at ht'
      exact Finset.notMem_empty _ ht'

lemma cleanAdj (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    {t w : Fin n} (ht : t ∈ side C a b) (hw : w ∈ side C a (1 - b)) :
    (G.deleteEdges ↑(Ustar G C)).Adj t w := by
  have cross {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
      (G.deleteEdges ↑(Ustar G C)).Adj u v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨topAdj ao ha hu hv, ?_⟩
    intro he
    apply (Finset.mem_sdiff.mp (show s(u, v) ∈ Ustar G C from he)).2
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
  fin_cases b
  · exact cross ht hw
  · exact (cross hw ht).symm

lemma firingTop (ao : IsAO2 n C) {a m : ℕ} {b : Fin 2} {w : Fin n}
    (ha : a ∈ tops G C)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
    (hw : w ∈ side C a (1 - b)) (x : Fin n → Bool)
    (hmx : gateVal n C m x = true) (hwx : x w = true) :
    graphFun G ∅ x = true := by
  obtain ⟨haLen, haOp, haBelow⟩ := topData ha
  apply haBelow x ((andValOperands ao haLen haOp x).mpr ?_)
  intro c
  rcases opposite b c with rfl | rfl
  · exact orStep_up (n := n) (by simp) path hmx
  · exact sideVal hw hwx

lemma oppositeEndpoint (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2} {u v : Fin n}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (hv : gateVal n C a (pairInput u v) = true)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    ∃ w ∈ side C a (1 - b), w = u ∨ w = v := by
  obtain ⟨al, aop, ab⟩ := topData ha
  have hv' := (andValOperands least.1 al aop _).mp hv (1 - b)
  rcases operandSupport least.1 top al aop hv' with h | ⟨j, hj, hr, _⟩
  · exact h
  · obtain ⟨k, hk, _, hp⟩ := residualPath least.1 empty ha hj hr
    rw [only, Finset.mem_singleton] at hk
    subst k
    exfalso
    apply (orData hm).2.2
    intro x hx
    apply ab x ((andValOperands least.1 al aop x).mpr ?_)
    intro c
    rcases opposite b c with rfl | rfl
    · exact orStep_up (n := n) (by simp) path hx
    · exact orStep_up (n := n) (by simp) hp hx

lemma rawCoverShape (ao : IsAO2 n C) {m w : ℕ}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (hw : w < n + m) :
    (orIn n C w).card ≤ 1 ∨
      ∃ z : Fin n, ∀ t ∈ orIn n C w, (G.deleteEdges ↑(Ustar G C)).Adj t z := by
  by_cases hcard : (orIn n C w).card ≤ 1
  · exact Or.inl hcard
  have hne : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hu⟩ := hne
  by_cases hi : w < n
  · exfalso
    apply hcard
    apply Finset.card_le_one.mpr
    intro t ht v hv
    have eq (z : Fin n) (hz : z ∈ orIn n C w) : (z : ℕ) = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach z hz) with he | ⟨_, hs, _⟩
      · exact he.symm
      · obtain ⟨k, _, he, _, _, _⟩ := hs
        omega
    exact Fin.ext ((eq t ht).trans (eq v hv).symm)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hkm : k < m := by omega
  have hkl := hkm.trans (orData hm).1
  have hko : (gateAt C k).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem hkl) with h | h
    · rw [andRawEmpty h] at hu
      exact (Finset.notMem_empty _ hu).elim
    · exact h
  have hbelow : ¬ BelowF G C k := by
    intro hb
    have hv := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (hb _ hv))
  have hkN : k ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hkl (And.intro hko hbelow)
  have hkL : k ∈ lam G C := by
    by_contra hn
    have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
    rw [only, Finset.mem_singleton] at hk
    omega
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

lemma falseJunkCover (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (x : Fin n → Bool) :
    ∀ j < m, j ∈ junk G C →
      (∀ u v : Fin n, s(u, v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) →
      gateVal n C j x = false →
      ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
        ∃ z : Fin n, ∀ t ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj t z) ∧
        (∀ u v : Fin n, s(u, v) ∈ Ustar G C → u ∈ S ∨ v ∈ S) ∧
        ∀ t ∈ S, x t = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjm hj fires hx
    obtain ⟨jl, jo, _⟩ := junkData hj
    have hfalse : ∃ b : Fin 2, val C (List.ofFn x) (opnd C j b) = false := by
      by_contra hn
      have hv := (andValOperands ao jl jo x).mpr
        (fun b => by
          cases hval : val C (List.ofFn x) (opnd C j b) with
          | true => rfl
          | false => exact (hn ⟨b, hval⟩).elim)
      exact Bool.false_ne_true (hx.symm.trans hv)
    obtain ⟨b, hb⟩ := hfalse
    have firesOp (u v : Fin n) (he : s(u, v) ∈ Ustar G C) :
        val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
      (andValOperands ao jl jo _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
        opnd C j b = n + k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
      · exact h
      · have hr' := lastOrOutside ao hk rl ro ri rb
        rw [only, Finset.mem_singleton] at hr'
        have hle := orStep_le rp
        have hlt := opndBound ao jl b
        omega
    by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
    · obtain ⟨k, hk, he⟩ := hd
      have hbnd := opndBound ao jl b
      have hkj : k < j := by omega
      apply ih k hkj (hkj.trans hjm) hk
      · intro u v hu
        have hv := firesOp u v hu
        rw [he] at hv
        exact hv
      · rw [he] at hb
        exact hb
    · refine ⟨orIn n C (opnd C j b), rawCoverShape ao only hm (by
        have := opndBound ao jl b
        omega), ?_, ?_⟩
      · intro u v he
        rcases operandSupport ao top jl jo (firesOp u v he) with ⟨t, ht, rfl | rfl⟩ | ⟨k, hk, hr, _⟩
        · exact Or.inl ht
        · exact Or.inr ht
        · exact (hd ⟨k, hk, direct k hk hr⟩).elim
      · intro t ht
        apply Bool.eq_false_iff.mpr
        intro ht'
        exact Bool.false_ne_true (hb.symm.trans (reach_var_val x _ t (mem_orIn_reach t ht) ht'))

lemma finish (least : IsLeastAO G C) (top : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card)
    (budget : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 3)
    (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
    3 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ∧
    ∃ t : Fin n, ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
      ∃ w : Fin n, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
          ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
            ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
            (∀ p q : Fin n, s(p, q) ∈ Ustar G C → p ∈ S ∨ q ∈ S) ∧
            ∀ y ∈ S, x y = false := by
  have empty : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨u, v, he⟩ := nonempty
  obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace least top he
  obtain ⟨m, hm, hin, path⟩ := residualPath least.1 empty ha hj hr
  have hpos := Finset.card_pos.mpr ⟨m, hm⟩
  have only : orN G C \ lam G C = {m} := by
    ext k
    rw [Finset.mem_singleton]
    exact ⟨fun hk => Finset.card_le_one.mp (by omega) k hk m hm, fun h => h.symm ▸ hm⟩
  obtain ⟨t, ht⟩ := mixingRaw least.1 empty only hm ha path
  refine ⟨by omega, t, ?_⟩
  have hml := (orData hm).1
  have hmo := (orData hm).2.1
  have hlt := least.1.2.1 m hml _ hin
  have uniform (p q : Fin n) (hpq : s(p, q) ∈ Ustar G C) :
      gateVal n C j (pairInput p q) = true := by
    obtain ⟨a', ha', b', k, hk, _, hr', hv⟩ := residualTrace least top hpq
    obtain ⟨l, hl, hkin, _⟩ := residualPath least.1 empty ha' hk hr'
    rw [only, Finset.mem_singleton] at hl
    subst l
    have heq := singleJunkInput least.1 hm ⟨t, ht⟩ hj hk hin hkin
    rwa [heq]
  intro p q hpq
  obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace least top hpq
  obtain ⟨l, hl, _, hp⟩ := residualPath least.1 empty ha' hk hr'
  rw [only, Finset.mem_singleton] at hl
  subst l
  obtain ⟨w, hw, hend⟩ := oppositeEndpoint least top empty only hm ha' hav hp
  have ht' : t ∈ side C a' b' :=
    reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  refine ⟨w, hend, cleanAdj least.1 ha' b' ht' hw, ?_⟩
  intro x hx hf
  have hjx : gateVal n C j x = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hmx : gateVal n C m x = true :=
      (val_or (n := n) (by simp) hml hmo).mpr ⟨_, hin, hlt, htrue⟩
    exact Bool.false_ne_true (hf.symm.trans (firingTop least.1 ha' hp hw x hmx hx))
  exact falseJunkCover least.1 top only hm x j (by omega) hj uniform hjx

end PEqualNP.Outside.L_meta_7465_aux.Routing

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm

/-- A conjunction of three positive OR clauses accepting opposite disjoint edges
cannot reject every pair containing one vertex from each edge. -/
theorem threeClausesCorner {V : Type*} [DecidableEq V] (S : Fin 3 → Finset V)
    (p b q d : V) (hpb : ∀ i, p ∈ S i ∨ b ∈ S i) (hqd : ∀ i, q ∈ S i ∨ d ∈ S i)
    (hpq : ∃ i, p ∉ S i ∧ q ∉ S i) (hpd : ∃ i, p ∉ S i ∧ d ∉ S i)
    (hbq : ∃ i, b ∉ S i ∧ q ∉ S i) : ∀ i, b ∈ S i ∨ d ∈ S i := by
  obtain ⟨x, hxp, hxq⟩ := hpq
  obtain ⟨y, hyp, hyd⟩ := hpd
  obtain ⟨z, hzb, hzq⟩ := hbq
  have hxb := (hpb x).resolve_left hxp
  have hxd := (hqd x).resolve_left hxq
  have hyb := (hpb y).resolve_left hyp
  have hzd := (hqd z).resolve_left hzq
  have hxy : x ≠ y := by rintro rfl; exact hyd hxd
  have hxz : x ≠ z := by rintro rfl; exact hzb hxb
  have hyz : y ≠ z := by rintro rfl; exact hzb hyb
  have hall : ({x, y, z} : Finset (Fin 3)) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hxy, hxz, hyz])
  intro i
  have hi : i ∈ ({x, y, z} : Finset (Fin 3)) := by rw [hall]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact Or.inl hxb
  · exact Or.inl hyb
  · exact Or.inr hzd

def hitsClauses {V : Type*} (S : Fin 3 → Finset V) (W : Finset V) : Prop :=
  ∀ i, ∃ v ∈ W, v ∈ S i

private theorem forbidPair {n : ℕ} {G : SimpleGraph (Fin n)} {P : Finset (Fin n)}
    {S : Fin 3 → Finset (Fin n)}
    (hsafe : ∀ p ∈ P, ∀ W : Finset (Fin n), p ∈ W → hitsClauses S W →
      ∃ u ∈ W, ∃ v ∈ W, G.Adj u v)
    {p v : Fin n} (hp : p ∈ P) (hn : ¬G.Adj p v) : ∃ i, p ∉ S i ∧ v ∉ S i := by
  classical
  by_contra! h
  have hit : hitsClauses S {p, v} := by
    intro i
    by_cases hpi : p ∈ S i
    · exact ⟨p, by simp, hpi⟩
    · exact ⟨v, by simp, h i hpi⟩
  obtain ⟨u, hu, w, hw, he⟩ := hsafe p hp {p, v} (by simp) hit
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact G.loopless.irrefl _ he
  · exact hn he
  · exact hn he.symm
  · exact G.loopless.irrefl _ he

private theorem forbidSecondNeighbor {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h₄ : NoFourCycle G) {p q c b : Fin n}
    (hn : p ≠ q) (hcb : c ≠ b) (hpc : G.Adj p c) (hqc : G.Adj q c) (hqb : G.Adj q b) :
    ¬ G.Adj p b := by
  intro hpb
  have hsub : ({c, b} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj q w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc, hqc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb, hqb⟩
  have hsize := (Finset.card_le_card hsub).trans (h₄ p q hn)
  rw [Finset.card_pair hcb] at hsize
  omega

/-- Suppose the raw side P of a star shares a common neighbour c, and a conjunction
of three raw OR clauses may safely be ANDed with every vertex in P. If two induced
matching edges each make that conjunction true and meet P at p and q, then P = {p,q}.
This lets a two-edge cover replace c by p and q at net cost one. -/
theorem inducedMatchingStarSide {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h₄ : NoFourCycle G) (P : Finset (Fin n)) (S : Fin 3 → Finset (Fin n))
    (p b q d c : Fin n) (hp : p ∈ P) (hq : q ∈ P)
    (hpc : ∀ v ∈ P, G.Adj v c) (hcb : c ≠ b) (hcd : c ≠ d)
    (hedge₁ : G.Adj p b) (hedge₂ : G.Adj q d)
    (hnpq : ¬ G.Adj p q) (hnpd : ¬ G.Adj p d) (hnqb : ¬ G.Adj q b) (hnbd : ¬ G.Adj b d)
    (hpb : ∀ i, p ∈ S i ∨ b ∈ S i) (hqd : ∀ i, q ∈ S i ∨ d ∈ S i)
    (hsafe : ∀ x ∈ P, ∀ W : Finset (Fin n), x ∈ W → hitsClauses S W →
      ∃ u ∈ W, ∃ v ∈ W, G.Adj u v) : P = {p, q} := by
  classical
  have h₁ := forbidPair hsafe hp hnpq
  have h₂ := forbidPair hsafe hp hnpd
  obtain ⟨j, hjq, hjb⟩ := forbidPair hsafe hq hnqb
  have corner := threeClausesCorner S p b q d hpb hqd h₁ h₂ ⟨j, hjb, hjq⟩
  apply Finset.Subset.antisymm
  · intro r hr
    by_contra! h
    have hrp : r ≠ p := fun eq => h (by simp [eq])
    have hrq : r ≠ q := fun eq => h (by simp [eq])
    have hrb := forbidSecondNeighbor h₄ hrp hcb (hpc r hr) (hpc p hp) hedge₁
    have hrd := forbidSecondNeighbor h₄ hrq hcd (hpc r hr) (hpc q hq) hedge₂
    let W : Finset (Fin n) := {r, b, d}
    have hit : hitsClauses S W := by
      intro i
      rcases corner i with hb | hd
      · exact ⟨b, by simp [W], hb⟩
      · exact ⟨d, by simp [W], hd⟩
    obtain ⟨u, hu, v, hv, he⟩ := hsafe r hr W (by simp [W]) hit
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact G.loopless.irrefl _ he
    · exact hrb he
    · exact hrd he
    · exact hrb he.symm
    · exact G.loopless.irrefl _ he
    · exact hnbd he
    · exact hrd he.symm
    · exact hnbd he.symm
    · exact G.loopless.irrefl _ he
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm

section CleanClauses

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {I : Type*} {S : I → Finset (Fin n)} {U : Finset (Sym2 (Fin n))}

/-- Negative independent assignments can be witnessed by an entire missed clause. -/
private def rejectsIndependent (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) : Prop :=
  ∀ W : Finset (Fin n), (∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v) → ∃ j, ∀ u ∈ W, u ∉ S j

private theorem missingPair (neg : rejectsIndependent G S) {a b : Fin n} (hn : ¬ G.Adj a b) :
    ∃ j, a ∉ S j ∧ b ∉ S j := by
  classical
  obtain ⟨j,h⟩ := neg {a,b} (by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.irrefl
    · exact hn
    · exact fun h => hn h.symm
    · exact G.irrefl)
  exact ⟨j,h _ (by simp),h _ (by simp)⟩

/-- Two different literals with a common neighbour cannot occupy a single old
neighbourhood when their first edge to that neighbour was deleted. -/
private theorem incompatibleOldClause (h₄ : NoFourCycle G) (j : I)
    (shape : (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z)
    {a b c : Fin n} (hbc : b ≠ c) (ab : G.Adj a b) (ac : G.Adj a c) (removed : s(b,a) ∈ U)
    (hb : b ∈ S j) (hc : c ∈ S j) : False := by
  rcases shape with small | ⟨z, h⟩
  · exact hbc (Finset.card_le_one.mp small _ hb _ hc)
  · have hz : z ≠ a := by
      rintro rfl
      exact (SimpleGraph.deleteEdges_adj.mp (h b hb)).2 removed
    exact forbidSecondNeighbor h₄ hz hbc (SimpleGraph.deleteEdges_adj.mp (h b hb)).1.symm
      ab ac (SimpleGraph.deleteEdges_adj.mp (h c hc)).1.symm

/-- All edges accepted by one below-graph positive CNF with old-neighbourhood
clauses form a matching among the deleted edges. -/
theorem singleTopNeighborUnique (h₄ : NoFourCycle G) (neg : rejectsIndependent G S)
    (shape : ∀ j, (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z)
    {a b c : Fin n} (ab : G.Adj a b) (ac : G.Adj a c) (removed : s(b,a) ∈ U)
    (pos₁ : ∀ j, a ∈ S j ∨ b ∈ S j) (pos₂ : ∀ j, a ∈ S j ∨ c ∈ S j) : b = c := by
  obtain ⟨j,ha,_⟩ := missingPair (a := a) (b := a) neg G.irrefl
  by_contra hbc
  exact incompatibleOldClause h₄ j (shape j) hbc ab ac removed
    ((pos₁ j).resolve_left ha) ((pos₂ j).resolve_left ha)

/-- Accepted disjoint residual edges have no cross edge in the ambient graph. -/
theorem singleTopNoCross (h₄ : NoFourCycle G) (neg : rejectsIndependent G S)
    (shape : ∀ j, (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z)
    {a b c d : Fin n} (hab : G.Adj a b) (hcd : G.Adj c d) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d)
    (removed₁ : s(b,a) ∈ U) (removed₂ : s(d,c) ∈ U)
    (pos₁ : ∀ j, a ∈ S j ∨ b ∈ S j) (pos₂ : ∀ j, c ∈ S j ∨ d ∈ S j) : ¬ G.Adj a c := by
  intro hac
  by_cases adj : G.Adj a d
  · have nbc : ¬ G.Adj c b := by
      intro hcb
      exact forbidSecondNeighbor h₄ hac.ne hbd hab hcb hcd adj
    obtain ⟨j,hc,hb⟩ := missingPair neg nbc
    exact incompatibleOldClause h₄ j (shape j) had.symm hcd hac.symm removed₂
      ((pos₂ j).resolve_left hc) ((pos₁ j).resolve_right hb)
  · obtain ⟨j,ha,hd⟩ := missingPair neg adj
    exact incompatibleOldClause h₄ j (shape j) hbc hab hac removed₁
      ((pos₁ j).resolve_left ha) ((pos₂ j).resolve_right hd)

/-- A below-graph conjunction accepting k induced matching edges needs one different
clause for each of their 2^k independent transversals. -/
theorem inducedMatchingClauseCount {J : Type*} [Fintype J] [Fintype I]
    (neg : rejectsIndependent G S) (ends : J → Bool → Fin n)
    (pos : ∀ i j, ends i false ∈ S j ∨ ends i true ∈ S j)
    (cross : ∀ i h, i ≠ h → ∀ c d, ¬ G.Adj (ends i c) (ends h d)) :
    2^Fintype.card J ≤ Fintype.card I := by
  classical
  have missed (bits : J → Bool) : ∃ j, ∀ i, ends i (bits i) ∉ S j := by
    let W := Finset.univ.image fun i => ends i (bits i)
    obtain ⟨j,hj⟩ := neg W (by
      intro u hu v hv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hv
      by_cases he : i = h
      · subst h
        exact G.irrefl
      · exact cross i h he _ _)
    exact ⟨j,fun i => hj _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  choose witness hw using missed
  have inj : Function.Injective witness := by
    intro x y heq
    funext i
    have hx := hw x i
    have hy := hw y i
    rw [← heq] at hy
    have hpos := pos i (witness x)
    cases hx' : x i <;> cases hy' : y i <;> simp_all
  simpa using Fintype.card_le_of_injective witness inj

/-- Old-neighbourhood clauses separating the residual edges from all independent sets
have exponential cardinality in the number of edges. -/
theorem singleTopClauseLower [Fintype I] (h₄ : NoFourCycle G) (neg : rejectsIndependent G S)
    (shape : ∀ j, (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z)
    (hsub : U ⊆ G.edgeFinset) (positives : ∀ a b, s(a,b) ∈ U → ∀ j, a ∈ S j ∨ b ∈ S j) :
    2^U.card ≤ Fintype.card I := by
  classical
  have endpoints (e : U) : ∃ a b : Fin n, e.val = s(a,b) := by
    induction e.val using Sym2.ind with
    | _ u v => exact ⟨u,v,rfl⟩
  choose a b decomp using endpoints
  let ends (e : U) (s : Bool) := if s then b e else a e
  have edge (e : U) (s : Bool) : s(ends e s,ends e (!s)) = e.val := by
    cases s
    · exact (decomp e).symm
    · exact Sym2.eq_swap.trans (decomp e).symm
  have member (e : U) (s : Bool) : s(ends e s,ends e (!s)) ∈ U := by rw [edge]; exact e.2
  have real (e : U) (s : Bool) : G.Adj (ends e s) (ends e (!s)) :=
    SimpleGraph.mem_edgeFinset.mp (hsub (member e s))
  have rev (e : U) (s : Bool) : s(ends e (!s),ends e s) ∈ U := by
    rw [Sym2.eq_swap]
    exact member e s
  have separate {e f : U} (hne : e ≠ f) (c d : Bool) : ends e c ≠ ends f d := by
    intro eq
    have hcf : G.Adj (ends e c) (ends f (!d)) := by rw [eq]; exact real f d
    have pf : ∀ j, ends e c ∈ S j ∨ ends f (!d) ∈ S j := by
      rw [eq]
      exact positives _ _ (member f d)
    have same := singleTopNeighborUnique h₄ neg shape (real e c) hcf (rev e c)
      (positives _ _ (member e c)) pf
    apply hne
    apply Subtype.ext
    rw [← edge e c, ← edge f d, eq, same]
  have cross (e f : U) (hne : e ≠ f) (c d : Bool) : ¬ G.Adj (ends e c) (ends f d) :=
    singleTopNoCross h₄ neg shape (real e c) (real f d)
      (separate hne (!c) d) (separate hne c (!d)) (separate hne (!c) (!d))
      (rev e c) (rev f d) (positives _ _ (member e c)) (positives _ _ (member f d))
  simpa using inducedMatchingClauseCount neg ends
    (fun e => positives _ _ (member e false)) cross

end CleanClauses

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The proof of 5869.rawCoverShape applies on the entire circuit when there are
no exceptional OR gates. -/
private theorem rawShapeNoOutside (ao : IsAO2 n C) (none : orN G C \ lam G C = ∅)
    {w : ℕ} (hw : w < n + C.gates.length) :
    (orIn n C w).card ≤ 1 ∨
      ∃ z : Fin n, ∀ t ∈ orIn n C w, (G.deleteEdges ↑(Ustar G C)).Adj t z := by
  by_cases hcard : (orIn n C w).card ≤ 1
  · exact Or.inl hcard
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C w).card)
  by_cases hi : w < n
  · exfalso
    apply hcard
    apply Finset.card_le_one.mpr
    intro t ht v hv
    have eq (z : Fin n) (hz : z ∈ orIn n C w) : (z : ℕ) = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach z hz) with he | ⟨_, hs, _⟩
      · exact he.symm
      · obtain ⟨k, _, he, _, _, _⟩ := hs
        omega
    exact Fin.ext ((eq t ht).trans (eq v hv).symm)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hkl : k < C.gates.length := by omega
  have hko : (gateAt C k).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem hkl) with h | h
    · rw [andRawEmpty h] at hu
      exact (Finset.notMem_empty _ hu).elim
    · exact h
  have hbelow : ¬ BelowF G C k := by
    intro hb
    have hv := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (hb _ hv))
  have hkN : k ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hkl (And.intro hko hbelow)
  have hkL : k ∈ lam G C := by
    by_contra hn
    have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
    rw [none] at hk
    exact Finset.notMem_empty _ hk
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1-b)).card)
  exact Or.inr ⟨z,fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

private theorem noOutsideDirect (ao : IsAO2 n C) (none : orN G C \ lam G C = ∅)
    {w j : ℕ} (hj : j ∈ junk G C) (hr : OrReaches n C w j) : w = n + j := by
  rcases lastOrBefore (orReaches_reach j _ hr).1 with he | ⟨m,hm,ho,hi,hb,_⟩
  · exact he
  · have hop := lastOrOutside ao hj hm ho hi hb
    rw [none] at hop
    exact (Finset.notMem_empty _ hop).elim

private theorem onlyCentreFires (hL : IsLeastAO G C) (hT : TopForm G C)
    (none : orN G C \ lam G C = ∅) {a : ℕ} (one : centreless G C = {a})
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) : gateVal n C a (pairInput u v) = true := by
  obtain ⟨g,hg,i,j,hj,on,reach,_⟩ := residualTrace hL hT he
  have direct := noOutsideDirect hL.1 none hj reach
  have hempty : side (n := n) C g i = ∅ := by
    change orIn n C (opnd C g i) = ∅
    rw [direct, andRawEmpty (junkData hj).2.1]
  have hc : g ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨hg,?_⟩
    fin_cases i
    · exact Or.inl hempty
    · exact Or.inr hempty
  have eq : g = a := by simpa [one] using hc
  simpa [eq] using on

private def positiveSlot (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (k : ℕ × Fin 2) : Prop :=
  ∀ u v : Fin n, s(u,v) ∈ Ustar G C → u ∈ side C k.1 k.2 ∨ v ∈ side C k.1 k.2

/-- Trace a false assignment down a chain of genuine AND operands. The resulting
raw slot is available in a fixed finite pool and hits every residual pair. This
extends the argument in 5869.falseJunkCover to the unique centreless top. -/
private theorem missedPositiveSlot (ao : IsAO2 n C) (top : TopForm G C)
    (none : orN G C \ lam G C = ∅) {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool) :
    ∀ g, g ∈ insert a (junk G C) →
      (∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C g (pairInput u v) = true) →
      gateVal n C g x = false →
      ∃ h ∈ insert a (junk G C), ∃ i : Fin 2, positiveSlot G C (h,i) ∧
        ∀ v ∈ side (n := n) C h i, x v = false := by
  intro g
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    intro hg fires hx
    have gate : g < C.gates.length ∧ (gateAt C g).op = GateOp.and := by
      rcases Finset.mem_insert.mp hg with rfl | hj
      · exact ⟨(topData ha).1,(topData ha).2.1⟩
      · exact ⟨(junkData hj).1,(junkData hj).2.1⟩
    obtain ⟨gl,go⟩ := gate
    have hfalse : ∃ i : Fin 2, val C (List.ofFn x) (opnd C g i) = false := by
      by_contra hn
      have hv := (andValOperands ao gl go x).mpr (fun i => by
        cases hval : val C (List.ofFn x) (opnd C g i) with
        | true => rfl
        | false => exact (hn ⟨i,hval⟩).elim)
      exact Bool.false_ne_true (hx.symm.trans hv)
    obtain ⟨i,hi⟩ := hfalse
    have pos (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
        val C (List.ofFn (pairInput u v)) (opnd C g i) = true :=
      (andValOperands ao gl go _).mp (fires u v he) i
    by_cases hd : ∃ j ∈ junk G C, opnd C g i = n+j
    · obtain ⟨j,hj,he⟩ := hd
      have hb := opndBound ao gl i
      apply ih j (by omega) (Finset.mem_insert_of_mem hj)
      · intro u v huv
        have h := pos u v huv
        rw [he] at h
        exact h
      · rw [he] at hi
        exact hi
    · refine ⟨g,hg,i,?_,?_⟩
      · intro u v he
        rcases operandSupport ao top gl go (pos u v he) with
          ⟨t,ht,rfl | rfl⟩ | ⟨j,hj,hr,_⟩
        · exact Or.inl ht
        · exact Or.inr ht
        · exact (hd ⟨j,hj,noOutsideDirect ao none hj hr⟩).elim
      · intro t ht
        apply Bool.eq_false_iff.mpr
        intro hv
        exact Bool.false_ne_true (hi.symm.trans (reach_var_val x _ t (mem_orIn_reach t ht) hv))

/-- With one centreless top and no exceptional OR gate, a CNF separating all
residual pairs from the independent assignments uses at most 2j+1 clauses. -/
theorem oneCentreClauseBound (h₄ : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hU : (Ustar G C).Nonempty) (hc : (centreless G C).card = 1)
    (none : orN G C \ lam G C = ∅) :
    2^(Ustar G C).card ≤ 2 * (junk G C).card + 1 := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  have hac : a ∈ centreless G C := by simp [ha]
  obtain ⟨hat,emptySide⟩ := Finset.mem_filter.mp hac
  have poolData {g : ℕ} (hg : g ∈ insert a (junk G C)) : g < C.gates.length := by
    rcases Finset.mem_insert.mp hg with rfl | hj
    · exact (topData hat).1
    · exact (junkData hj).1
  let U := Ustar G C
  let pool : Finset (ℕ × Fin 2) := (insert a (junk G C)).product Finset.univ
  let F := pool.filter (positiveSlot G C)
  let S (j : F) := side (n := n) C j.val.1 j.val.2
  have contains (j : F) : j.val.1 ∈ insert a (junk G C) :=
    (Finset.mem_product.mp (Finset.mem_filter.mp j.2).1).1
  have shape (j : F) :
      (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z := by
    apply rawShapeNoOutside hL.1 none
    have g := poolData (contains j)
    have bd := opndBound hL.1 g j.val.2
    omega
  have positive (u v : Fin n) (he : s(u,v) ∈ U) (j : F) : u ∈ S j ∨ v ∈ S j :=
    (Finset.mem_filter.mp j.2).2 u v he
  have negative : rejectsIndependent G S := by
    intro W hi
    let x : Fin n → Bool := fun u => decide (u ∈ W)
    have hx : gateVal n C a x = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have pos := (topData hat).2.2 x h
      simp [graphFun,x] at pos
      obtain ⟨u,v,adj,hu,hv⟩ := pos
      exact hi u hu v hv adj
    obtain ⟨g,hg,i,hp,hn⟩ := missedPositiveSlot hL.1 hT none hat x a
      (Finset.mem_insert_self _ _) (fun _ _ he => onlyCentreFires hL hT none ha he) hx
    have entry : (g,i) ∈ F :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg,Finset.mem_univ _⟩, hp⟩
    refine ⟨⟨(g,i),entry⟩,?_⟩
    intro v hv hs
    have zero := hn v hs
    simp [x,hv] at zero
  have actual (e : Sym2 (Fin n)) (he : e ∈ U) : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
  have lower := singleTopClauseLower h₄ negative shape (fun _ he => actual _ he) positive
  have ex : ∃ u v : Fin n, s(u,v) ∈ U := by
    obtain ⟨e,he⟩ := hU
    induction e using Sym2.ind with
    | _ u v => exact ⟨u,v,he⟩
  obtain ⟨u,v,uv⟩ := ex
  have emp : ∃ i : Fin 2, side (n := n) C a i = ∅ := by
    rcases emptySide with he | he
    · exact ⟨0,he⟩
    · exact ⟨1,he⟩
  obtain ⟨i,hi⟩ := emp
  have poolMem : (a,i) ∈ pool := Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,Finset.mem_univ _⟩
  have missing : (a,i) ∉ F := by
    intro h
    have on := (Finset.mem_filter.mp h).2 u v uv
    change u ∈ side (n := n) C a i ∨ v ∈ side (n := n) C a i at on
    simp [hi] at on
  have strict : F ⊂ pool := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩
    intro heq
    exact missing (heq.symm ▸ poolMem)
  have aNotJunk : a ∉ junk G C := by
    intro hj
    obtain ⟨_,_,x,hx,hn⟩ := junkData hj
    exact Bool.false_ne_true (hn.symm.trans ((topData hat).2.2 x hx))
  have psz : pool.card = ((junk G C).card + 1) * 2 := by
    simp [pool,aNotJunk,Finset.card_insert_of_notMem]
  have left : 2^U.card ≤ F.card := by simpa using lower
  have right := Finset.card_lt_card strict
  change 2^U.card ≤ 2 * (junk G C).card + 1
  omega

/-- Exponential clause cost pays for both endpoints' contributions once there
are at least two junk gates. -/
private theorem countToDouble (u j : ℕ) (hj : 2 ≤ j) (bound : 2^u ≤ 2*j+1) : 2*u ≤ j+2 := by
  by_cases hu : u ≤ 2
  · omega
  · have lower (r : ℕ) : 4*r+8 ≤ 2^(r+3) := by
      induction r with
      | zero => decide
      | succ r ih =>
        rw [show r+1+3 = (r+3)+1 by omega, pow_succ]
        omega
    obtain ⟨r,hr⟩ : ∃ r, u = r+3 := ⟨u-3,by omega⟩
    rw [hr] at bound ⊢
    have := lower r
    omega

theorem oneCentrePays (h₄ : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hU : (Ustar G C).Nonempty) (hj : 2 ≤ (junk G C).card)
    (hc : (centreless G C).card = 1) (none : orN G C \ lam G C = ∅) :
    2 * (Ustar G C).card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  have h := countToDouble _ _ hj (oneCentreClauseBound h₄ hL hT hU hc none)
  simpa [hc,none,Nat.add_comm] using h

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm

section Anchored

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {I : Type*} {S : I → Finset (Fin n)} {U : Finset (Sym2 (Fin n))}

private def rejectsAt (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (p : Fin n) : Prop :=
  ∀ W : Finset (Fin n), p ∈ W → (∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v) →
    ∃ j, ∀ u ∈ W, u ∉ S j

private theorem missingAt {p v : Fin n} (safe : rejectsAt G S p) (hn : ¬ G.Adj p v) :
    ∃ j, p ∉ S j ∧ v ∉ S j := by
  classical
  obtain ⟨j,h⟩ := safe {p,v} (by simp) (by
    intro u hu w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact G.irrefl
    · exact hn
    · exact fun h => hn h.symm
    · exact G.irrefl)
  exact ⟨j,h _ (by simp),h _ (by simp)⟩

/-- A single raw mixing anchor protects one endpoint of each accepted residual pair.
The clauses must distinguish all independent transversals containing a protected endpoint. -/
theorem anchoredClauseLower [Fintype I] (h₄ : NoFourCycle G) (t : Fin n)
    (shape : ∀ j, (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z)
    (hsub : U ⊆ G.edgeFinset) (pos : ∀ a b, s(a,b) ∈ U → ∀ j, a ∈ S j ∨ b ∈ S j)
    (orient : ∀ e ∈ U, ∃ p b : Fin n, e = s(p,b) ∧ (G.deleteEdges ↑U).Adj p t ∧ rejectsAt G S p) :
    2^U.card ≤ Fintype.card I + 1 := by
  classical
  choose p b decomp anchor safe using fun e : U => orient e.val e.2
  have mem (e : U) : s(p e,b e) ∈ U := by rw [← decomp e]; exact e.2
  have rev (e : U) : s(b e,p e) ∈ U := by rw [Sym2.eq_swap]; exact mem e
  have real (e : U) : G.Adj (p e) (b e) := SimpleGraph.mem_edgeFinset.mp (hsub (mem e))
  have anch (e : U) : G.Adj (p e) t := (SimpleGraph.deleteEdges_adj.mp (anchor e)).1
  have unique (e : U) {d : Fin n} (hd : s(p e,d) ∈ U) (had : G.Adj (p e) d) : b e = d := by
    obtain ⟨j,hp,_⟩ := missingAt (v := p e) (safe e) G.irrefl
    by_contra hne
    exact incompatibleOldClause h₄ j (shape j) hne (real e) had (rev e)
      ((pos _ _ (mem e) j).resolve_left hp) ((pos _ _ hd j).resolve_left hp)
  have pinj : Function.Injective p := by
    intro e f eq
    have alt : s(p e,b f) ∈ U := by rw [eq]; exact mem f
    have adj : G.Adj (p e) (b f) := by rw [eq]; exact real f
    have same := unique e alt adj
    apply Subtype.ext
    rw [decomp e,decomp f,eq,same]
  have cross (e f : U) (hne : e ≠ f) : ¬ G.Adj (p e) (b f) := by
    have ht : t ≠ b f := by
      intro eq
      apply (SimpleGraph.deleteEdges_adj.mp (anchor f)).2
      rw [eq]
      exact mem f
    exact forbidSecondNeighbor h₄ (pinj.ne hne) ht (anch e) (anch f) (real f)
  have apart (e f : U) (hne : e ≠ f) : b e ≠ p f := by
    intro eq
    have alt : s(p f,p e) ∈ U := by rw [←eq]; exact rev e
    have adj : G.Adj (p f) (p e) := by rw [←eq]; exact (real e).symm
    have same := unique f alt adj
    apply hne
    apply Subtype.ext
    rw [decomp e,decomp f,eq,same,Sym2.eq_swap]
  have lateral (e f : U) (hne : e ≠ f) : (¬ G.Adj (p e) (p f)) ∧ (¬ G.Adj (b e) (b f)) := by
    obtain ⟨j,hp,hb⟩ := missingAt (safe e) (cross e f hne)
    have be := (pos _ _ (mem e) j).resolve_left hp
    have pf := (pos _ _ (mem f) j).resolve_right hb
    constructor
    · intro pp
      exact incompatibleOldClause h₄ j (shape j) (apart e f hne) (real e) pp (rev e) be pf
    · intro bb
      exact incompatibleOldClause h₄ j (shape j) (apart e f hne).symm
        (real f).symm bb.symm (mem f) pf be
  let ends (e : U) (choice : Bool) := if choice then b e else p e
  have separate (e f : U) (hne : e ≠ f) (c d : Bool) : ¬G.Adj (ends e c) (ends f d) := by
    cases c <;> cases d
    · exact (lateral e f hne).1
    · exact cross e f hne
    · exact fun h => cross f e hne.symm h.symm
    · exact (lateral e f hne).2
  let other : U → Bool := fun _ => true
  let T := (Finset.univ : Finset (U → Bool)).erase other
  have missed (q : T) : ∃ j, ∀ e : U, ends e (q.val e) ∉ S j := by
    have pick : ∃ e : U, q.val e = false := by
      by_contra hn
      apply (Finset.mem_erase.mp q.2).1
      funext e
      cases he : q.val e with
      | false => exact (hn ⟨e,he⟩).elim
      | true => rfl
    obtain ⟨f,hf⟩ := pick
    let W := Finset.univ.image fun e => ends e (q.val e)
    have member (e : U) : ends e (q.val e) ∈ W :=
      Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
    have hpf : p f ∈ W := by simpa [hf,ends] using member f
    obtain ⟨j,hj⟩ := safe f W hpf (by
      intro x hx y hy
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hy
      by_cases eq : e = g
      · subst g
        exact G.irrefl
      · exact separate e g eq _ _)
    exact ⟨j,fun e => hj _ (member e)⟩
  choose witness hw using missed
  have inj : Function.Injective witness := by
    intro x y he
    apply Subtype.ext
    funext i
    have hx := hw x i
    have hy := hw y i
    rw [←he] at hy
    have hpos := pos _ _ (mem i) (witness x)
    cases hx' : x.val i <;> cases hy' : y.val i
    · rfl
    · simp [hx',ends] at hx
      simp [hy',ends] at hy
      exact (hpos.elim hx hy).elim
    · simp [hx',ends] at hx
      simp [hy',ends] at hy
      exact (hpos.elim hy hx).elim
    · rfl
  have bound : T.card ≤ Fintype.card I := by simpa using Fintype.card_le_of_injective witness inj
  have tcard : T.card + 1 = 2^U.card := by
    simpa [T] using Finset.card_erase_add_one (Finset.mem_univ other)
  omega

end Anchored

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

/-- Input slots at the boundary of a finite binary subcircuit. A slot is internal
exactly when it is the output wire of one of its selected gates. -/
private def boundarySlots (n : ℕ) (D : Finset ℕ) (wire : ℕ → Fin 2 → ℕ) :
    Finset (ℕ × Fin 2) := by
  classical
  exact (D.product (Finset.univ : Finset (Fin 2))).filter
    (fun k => ¬ ∃ h ∈ D, wire k.1 k.2 = n+h)

/-- Every gate except the root occupies a distinct non-boundary slot of a parent.
The argument allows a gate output to be used more than once. -/
theorem binaryBoundaryCard (n : ℕ) (D : Finset ℕ) (wire : ℕ → Fin 2 → ℕ)
    {r : ℕ} (root : r ∈ D)
    (parent : ∀ g ∈ D, g ≠ r → ∃ h ∈ D, ∃ i, wire h i = n+g) :
    (boundarySlots n D wire).card ≤ D.card+1 := by
  classical
  let pool := D.product (Finset.univ : Finset (Fin 2))
  let leaves := boundarySlots n D wire
  let internal := pool \ leaves
  have sub : leaves ⊆ pool := Finset.filter_subset _ _
  have assigns (g : D.erase r) : ∃ k : internal, wire k.val.1 k.val.2 = n+g.val := by
    obtain ⟨hne,hg⟩ := Finset.mem_erase.mp g.2
    obtain ⟨h,hh,i,he⟩ := parent g.val hg hne
    have selected : (h,i) ∈ pool := Finset.mem_product.mpr ⟨hh,Finset.mem_univ _⟩
    have noLeaf : (h,i) ∉ leaves := by
      intro hleaf
      exact (Finset.mem_filter.mp hleaf).2 ⟨g.val,hg,he⟩
    exact ⟨⟨(h,i),Finset.mem_sdiff.mpr ⟨selected,noLeaf⟩⟩,he⟩
  choose f hf using assigns
  have inj : Function.Injective f := by
    intro g h eq
    apply Subtype.ext
    have hg := hf g
    have hh := hf h
    rw [eq] at hg
    omega
  have charge : (D.erase r).card ≤ internal.card := by simpa using Fintype.card_le_of_injective f inj
  have removed := Finset.card_erase_add_one root
  have split : internal.card = pool.card - leaves.card := Finset.card_sdiff_of_subset sub
  have both : pool.card = D.card * 2 := by simp [pool]
  have hsize := Finset.card_le_card sub
  change leaves.card ≤ D.card+1
  omega

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Extract the common raw witness and last dirty gate from 5869's routing
argument. Only uniqueness of the exceptional OR is needed here. -/
private theorem oneMixingSource (least : IsLeastAO G C) (top : TopForm G C)
    (nonempty : (Ustar G C).Nonempty) (empty : centreless G C = ∅)
    {m : ℕ} (only : orN G C \ lam G C = {m}) :
    ∃ j ∈ junk G C, j < m ∧ ∃ t : Fin n,
      (∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) ∧
      ∀ e ∈ Ustar G C, ∃ p b : Fin n, e = s(p,b) ∧ (G.deleteEdges ↑(Ustar G C)).Adj p t ∧
        ∀ x : Fin n → Bool, x p = true → graphFun G ∅ x = false → gateVal n C j x = false := by
  have hm : m ∈ orN G C \ lam G C := by simp [only]
  obtain ⟨e,he⟩ := nonempty
  have he' : ∃ u v : Fin n, s(u,v) ∈ Ustar G C := by
    induction e using Sym2.ind with
    | _ u v => exact ⟨u,v,he⟩
  obtain ⟨u,v,huv⟩ := he'
  obtain ⟨a,ha,i,j,hj,_,hr,_⟩ := residualTrace least top huv
  obtain ⟨l,hl,hin,path⟩ := residualPath least.1 empty ha hj hr
  have eq : l = m := by simpa [only] using hl
  subst l
  obtain ⟨t,ht⟩ := mixingRaw least.1 empty only hm ha path
  have hmdata := orData hm
  have hlt := least.1.2.1 m hmdata.1 _ hin
  refine ⟨j,hj,by omega,t,?_,?_⟩
  · intro p q hpq
    obtain ⟨a',ha',i',k,hk,_,hr',hv⟩ := residualTrace least top hpq
    obtain ⟨r,hro,hki,_⟩ := residualPath least.1 empty ha' hk hr'
    have heq : r = m := by simpa [only] using hro
    subst r
    have same := singleJunkInput least.1 hm ⟨t,ht⟩ hj hk hin hki
    rwa [same]
  · intro f hf
    induction f using Sym2.ind with
    | _ p q =>
      obtain ⟨a',ha',i',k,hk,hav,reach,_⟩ := residualTrace least top hf
      obtain ⟨r,hro,_,path'⟩ := residualPath least.1 empty ha' hk reach
      have heq : r = m := by simpa [only] using hro
      subst r
      obtain ⟨w,hw,hend⟩ := oppositeEndpoint least top empty only hm ha' hav path'
      have ta : t ∈ side C a' i' := reach_mem_orIn t (path'.trans (mem_orIn_reach t ht))
      have old := (cleanAdj least.1 ha' i' ta hw).symm
      have safe (x : Fin n → Bool) (hx : x w = true) (hn : graphFun G ∅ x = false) :
          gateVal n C j x = false := by
        apply Bool.eq_false_iff.mpr
        intro on
        have mx : gateVal n C m x = true := (val_or (n := n) (by simp) hmdata.1 hmdata.2.1).mpr
          ⟨_,hin,hlt,on⟩
        exact Bool.false_ne_true (hn.symm.trans (firingTop least.1 ha' path' hw x mx hx))
      rcases hend with rfl | rfl
      · exact ⟨w,q,rfl,old,safe⟩
      · exact ⟨w,p,Sym2.eq_swap,old,safe⟩

/-- For a single dirty root before the first exceptional OR, its raw leaf slots
form a positive CNF with at most one more distinct slot than dirty gates. -/
private theorem dirtyRootCNF (least : IsLeastAO G C) (top : TopForm G C)
    {m r : ℕ} (only : orN G C \ lam G C = {m}) (hr : r ∈ junk G C) (hrm : r < m)
    (rootPos : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C r (pairInput u v) = true) :
    ∃ F : Finset (ℕ × Fin 2), F.card ≤ (junk G C).card+1 ∧
      (∀ k ∈ F, (side (n := n) C k.1 k.2).card ≤ 1 ∨
        ∃ z : Fin n, ∀ w ∈ side C k.1 k.2, (G.deleteEdges ↑(Ustar G C)).Adj w z) ∧
      (∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∀ k ∈ F, u ∈ side C k.1 k.2 ∨ v ∈ side C k.1 k.2) ∧
      ∀ x : Fin n → Bool, (∀ k ∈ F, ∃ w ∈ side C k.1 k.2, x w = true) → gateVal n C r x = true := by
  classical
  let step (g h : ℕ) := g ∈ junk G C ∧ h ∈ junk G C ∧ ∃ i : Fin 2, opnd C g i = n+h
  let D := (junk G C).filter fun g => Relation.ReflTransGen step r g
  have root : r ∈ D := Finset.mem_filter.mpr ⟨hr,.refl⟩
  have dirty {g : ℕ} (hg : g ∈ D) : g ∈ junk G C := (Finset.mem_filter.mp hg).1
  have reach {g : ℕ} (hg : g ∈ D) : Relation.ReflTransGen step r g := (Finset.mem_filter.mp hg).2
  have descend {g h : ℕ} (s : step g h) : h < g := by
    obtain ⟨hg,_,i,eq⟩ := s
    have := opndBound least.1 (junkData hg).1 i
    omega
  have before {g : ℕ} (hg : g ∈ D) : g < m := by
    have p := reach hg
    induction p with
    | refl => exact hrm
    | tail p s ih => exact (descend s).trans (ih (Finset.mem_filter.mpr ⟨s.1,p⟩))
  have parent (g : ℕ) (hg : g ∈ D) (hne : g ≠ r) : ∃ h ∈ D, ∃ i, opnd C h i = n+g := by
    rcases Relation.ReflTransGen.cases_tail (reach hg) with eq | ⟨h,p,k⟩
    · exact (hne eq).elim
    · exact ⟨h,Finset.mem_filter.mpr ⟨k.1,p⟩,k.2.2⟩
  have grows {g h : ℕ} (hg : g ∈ D) (hh : h ∈ junk G C) {i : Fin 2}
      (edge : opnd C g i = n+h) : h ∈ D :=
    Finset.mem_filter.mpr ⟨hh,(reach hg).tail ⟨dirty hg,hh,i,edge⟩⟩
  have allPos {g : ℕ} (hg : g ∈ D) (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
      gateVal n C g (pairInput u v) = true := by
    have p := reach hg
    induction p with
    | refl => exact rootPos u v he
    | tail p s ih =>
      obtain ⟨h₁,h₂,i,edge⟩ := s
      have prior := ih (Finset.mem_filter.mpr ⟨h₁,p⟩)
      have hv := (andValOperands least.1 (junkData h₁).1 (junkData h₁).2.1 _).mp prior i
      rw [edge] at hv
      exact hv
  let F := boundarySlots n D (opnd C)
  have source {k : ℕ × Fin 2} (hk : k ∈ F) : k.1 ∈ D :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hk).1).1
  have hm : m ∈ orN G C \ lam G C := by simp [only]
  have Ds : D ⊆ junk G C := Finset.filter_subset _ _
  refine ⟨F,(binaryBoundaryCard n D (opnd C) root parent).trans (by have := Finset.card_le_card Ds; omega),?_,?_,?_⟩
  · intro k hk
    apply rawCoverShape least.1 only hm
    have bd := opndBound least.1 (junkData (dirty (source hk))).1 k.2
    have := before (source hk)
    omega
  · intro u v he k hk
    have hD := source hk
    obtain ⟨gl,go,_⟩ := junkData (dirty hD)
    have hv := (andValOperands least.1 gl go _).mp (allPos hD u v he) k.2
    rcases operandSupport least.1 top gl go hv with ⟨t,ht,rfl | rfl⟩ | ⟨h,hh,path,_⟩
    · exact Or.inl ht
    · exact Or.inr ht
    · have eq : opnd C k.1 k.2 = n+h := by
        rcases lastOrBefore (orReaches_reach h _ path).1 with direct | ⟨v,hl,ho,hi,hle,rest⟩
        · exact direct
        · have same : v = m := by simpa [only] using lastOrOutside least.1 hh hl ho hi hle
          have earlier := orStep_le rest
          have bd := opndBound least.1 gl k.2
          have prior := before hD
          omega
      exact ((Finset.mem_filter.mp hk).2 ⟨h,grows hD hh eq,eq⟩).elim
  · intro x fires
    have on (g : ℕ) : g ∈ D → gateVal n C g x = true := by
      induction g using Nat.strong_induction_on with
      | ind g ih =>
        intro hg
        obtain ⟨gl,go,_⟩ := junkData (dirty hg)
        apply (andValOperands least.1 gl go _).mpr
        intro i
        by_cases inner : ∃ h ∈ D, opnd C g i = n+h
        · obtain ⟨h,hh,eq⟩ := inner
          have bd := opndBound least.1 gl i
          rw [eq]
          exact ih h (by omega) hh
        · have entry : (g,i) ∈ F := Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hg,Finset.mem_univ _⟩,inner⟩
          obtain ⟨w,hw,hx⟩ := fires (g,i) entry
          exact sideVal hw hx
    exact on r root

/-- When every non-centreless top is fed through the sole exceptional OR, its
single upstream dirty root separates all protected transversals. -/
theorem oneMixingExponential (h₄ : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hU : (Ustar G C).Nonempty) (empty : centreless G C = ∅)
    (count : (orN G C \ lam G C).card = 1) : 2^(Ustar G C).card ≤ (junk G C).card + 2 := by
  classical
  obtain ⟨m,only⟩ := Finset.card_eq_one.mp count
  obtain ⟨j,hj,less,t,pos,source⟩ := oneMixingSource hL hT hU empty only
  obtain ⟨F,num,shape,fires,safe⟩ := dirtyRootCNF hL hT only hj less pos
  let S (k : F) := side (n := n) C k.val.1 k.val.2
  have sh (k : F) : (S k).card ≤ 1 ∨
      ∃ z : Fin n, ∀ w ∈ S k, (G.deleteEdges ↑(Ustar G C)).Adj w z := shape k.val k.2
  have hp (u v : Fin n) (he : s(u,v) ∈ Ustar G C) (k : F) : u ∈ S k ∨ v ∈ S k :=
    fires u v he k.val k.2
  have oriented (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) :
      ∃ p b : Fin n, e = s(p,b) ∧ (G.deleteEdges ↑(Ustar G C)).Adj p t ∧ rejectsAt G S p := by
    obtain ⟨p,b,h,old,z⟩ := source e he
    refine ⟨p,b,h,old,?_⟩
    intro W hW independent
    let x : Fin n → Bool := fun u => decide (u ∈ W)
    have noEdge : graphFun G ∅ x = false := by
      apply Bool.eq_false_iff.mpr
      intro g
      simp [graphFun,x] at g
      obtain ⟨u,v,adj,hu,hv⟩ := g
      exact independent u hu v hv adj
    have off := z x (by simp [x,hW]) noEdge
    by_contra! hit
    have on := safe x (fun k hk => by
      obtain ⟨w,hw,hs⟩ := hit ⟨k,hk⟩
      exact ⟨w,hs,by simp [x,hw]⟩)
    exact Bool.false_ne_true (off.symm.trans on)
  have hsub : Ustar G C ⊆ G.edgeFinset := Finset.sdiff_subset
  have lower := anchoredClauseLower h₄ t sh hsub hp oriented
  have lower' : 2^(Ustar G C).card ≤ F.card + 1 := by simpa using lower
  omega

theorem oneMixingPays {h₄ : NoFourCycle G} (hL : IsLeastAO G C) (hT : TopForm G C)
    (hu : 3 ≤ (Ustar G C).card) (empty : centreless G C = ∅)
    (count : (orN G C \ lam G C).card = 1) :
    2*(Ustar G C).card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  have bound := oneMixingExponential h₄ hL hT (Finset.card_pos.mp (by omega)) empty count
  have power (k : ℕ) : 2*(k+3)+1 ≤ 2^(k+3) := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+3 = (k+3)+1 by omega,pow_succ]
      omega
  obtain ⟨k,hk⟩ : ∃ k, (Ustar G C).card = k+3 := ⟨(Ustar G C).card-3,by omega⟩
  have enough := power k
  rw [hk] at bound ⊢
  simp [empty,count]
  omega

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Direct OR paths below a wire are defined independently of its assignment. -/
private def promotionsAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (orN G C \ lam G C).filter fun h => (orIn n C (n+h)).Nonempty ∧ OrReaches n C w h

private theorem nonemptyOrData (ao : IsAO2 n C) {h : ℕ} (len : h < C.gates.length)
    (raw : (orIn n C (n+h)).Nonempty) :
    (gateAt C h).op = GateOp.or ∧ h ∈ orN G C := by
  classical
  obtain ⟨t,ht⟩ := raw
  have op : (gateAt C h).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem len) with ha | ho
    · rw [andRawEmpty ha] at ht
      exact (Finset.notMem_empty _ ht).elim
    · exact ho
  have failure : ¬ BelowF G C h := by
    intro below
    have hit := reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
    exact G.irrefl ((graphFun_pair G t t).mp (below _ hit))
  refine ⟨op,?_⟩
  simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨len,op,failure⟩

/-- On every assignment, a port with a reachable raw input is exactly a
disjunction of its raw literals and earlier nonempty exceptional OR outputs. -/
theorem nonemptyPortValue (ao : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
    (bound : w < n+C.gates.length) (raw : (orIn n C w).Nonempty) :
    val C (List.ofFn x) w = true ↔ (∃ t ∈ orIn n C w, x t = true) ∨
      ∃ h ∈ promotionsAt G C w, gateVal n C h x = true := by
  classical
  constructor
  · revert bound raw
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro bd hasRaw fires
      by_cases input : w < n
      · let t : Fin n := ⟨w,input⟩
        have mem : t ∈ orIn n C w := reach_mem_orIn t Relation.ReflTransGen.refl
        exact Or.inl ⟨t,mem,(val_ofFn C x t).symm.trans fires⟩
      obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
      have len : h < C.gates.length := by omega
      obtain ⟨op,ord⟩ := nonemptyOrData (G := G) ao len hasRaw
      by_cases ordinary : h ∈ lam G C
      · obtain ⟨_,r₀,r₁,_⟩ := Finset.mem_filter.mp ordinary
        obtain ⟨v,member,smaller,on⟩ := (val_or (n := n) (by simp) len op).mp fires
        obtain ⟨i,vi⟩ := inputsAsOpnd ao len member
        have rv : (orIn n C v).Nonempty := by
          rw [vi]
          fin_cases i
          · exact r₀
          · exact r₁
        have step : OrStep n C (n+h) v := ⟨h,len,rfl,op,member,smaller⟩
        rcases ih v smaller (by omega) rv on with ⟨t,ht,hx⟩ | ⟨j,hj,hx⟩
        · exact Or.inl ⟨t,reach_mem_orIn t (.head step (mem_orIn_reach t ht)),hx⟩
        · obtain ⟨hj',rj,route⟩ := Finset.mem_filter.mp hj
          exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨hj',rj,
            (orReaches_iff n C h j).mpr ⟨len,Or.inr ⟨op,v,member,smaller,route⟩⟩⟩,hx⟩
      · have own := (orReaches_iff n C h h).mpr ⟨len,Or.inl rfl⟩
        exact Or.inr ⟨h,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨ord,ordinary⟩,hasRaw,own⟩,fires⟩
  · rintro (⟨t,ht,xt⟩ | ⟨h,hh,on⟩)
    · exact reach_var_val x w t (mem_orIn_reach t ht) xt
    · have path := (orReaches_reach h w (Finset.mem_filter.mp hh).2.2).1
      exact orStep_up (n := n) (by simp) path on

private theorem endsAtInputOrAnd (ao : IsAO2 n C) (w : ℕ) (bd : w < n+C.gates.length) :
    (∃ t : Fin n, Relation.ReflTransGen (OrStep n C) w t.val) ∨
      ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        Relation.ReflTransGen (OrStep n C) w (n+j) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · exact Or.inl ⟨⟨w,input⟩,.refl⟩
    obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
    have len : h < C.gates.length := by omega
    rcases ao.1 _ (gateAt_mem len) with ha | ho
    · exact Or.inr ⟨h,len,ha,.refl⟩
    · have smaller := opndBound ao len 0
      have step : OrStep n C (n+h) (opnd C h 0) := ⟨h,len,rfl,ho,opndMem ao len _,smaller⟩
      rcases ih _ smaller (by omega) with ⟨t,r⟩ | ⟨j,jl,ja,r⟩
      · exact Or.inl ⟨t,.head step r⟩
      · exact Or.inr ⟨j,jl,ja,.head step r⟩

/-- A raw-empty wire in the OR cone of an AND operand is itself a dirty AND
or an exceptional OR with empty raw support. No intermediate ordinary gate
is needed to represent its value on any assignment. -/
theorem emptyPortSource (ao : IsAO2 n C) (top : TopForm G C) {a w : ℕ} {i : Fin 2}
    (len : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (context : Relation.ReflTransGen (OrStep n C) (opnd C a i) w)
    (empty : orIn n C w = ∅) :
    ∃ h, w = n+h ∧ (h ∈ junk G C ∨ h ∈ orN G C \ lam G C) := by
  have size := opndBound ao len i
  have below := orStep_le context
  have valid : w < n+C.gates.length := by omega
  have noInput (t : Fin n) (p : Relation.ReflTransGen (OrStep n C) w t.val) : False := by
    have found := reach_mem_orIn t p
    rw [empty] at found
    exact Finset.notMem_empty _ found
  have ge : n ≤ w := by
    by_contra! lt
    exact noInput ⟨w,lt⟩ .refl
  obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
  have hlen : h < C.gates.length := by omega
  rcases ao.1 _ (gateAt_mem hlen) with ha | ho
  · exact ⟨h,rfl,Or.inl (operandOrAndJunk ao top len hand (reach_orReaches context h rfl hlen) ha)⟩
  rcases endsAtInputOrAnd ao (n+h) valid with ⟨t,p⟩ | ⟨j,jl,ja,path⟩
  · exact (noInput t p).elim
  have junk := operandOrAndJunk ao top len hand (reach_orReaches (context.trans path) j rfl jl) ja
  obtain ⟨_,_,x,hx,hneg⟩ := junkData junk
  have dirty : ¬ BelowF G C h := by
    intro safe
    have on := orStep_up (n := n) (by simp) path (gateVal_eq_val n C j x ▸ hx)
    exact Bool.false_ne_true (hneg.symm.trans (safe x on))
  have inOr : h ∈ orN G C := by
    simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using
      And.intro hlen (And.intro ho dirty)
  have outside : h ∉ lam G C := by
    intro lamMem
    obtain ⟨_,⟨t,ht⟩,_⟩ := Finset.mem_filter.mp lamMem
    have step : OrStep n C (n+h) (opnd C h 0) :=
      ⟨h,hlen,rfl,ho,opndMem ao hlen _,opndBound ao hlen _⟩
    exact noInput t (.head step (mem_orIn_reach t ht))
  exact ⟨h,rfl,Or.inr (Finset.mem_sdiff.mpr ⟨inOr,outside⟩)⟩

/-- Raw support splits exactly at the two input wires of any binary OR. -/
theorem orRawUnion (ao : IsAO2 n C) {h : ℕ} (len : h < C.gates.length)
    (op : (gateAt C h).op = GateOp.or) :
    orIn n C (n+h) = side (n := n) C h 0 ∪ side C h 1 := by
  ext t
  constructor
  · intro ht
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with eq | ⟨v,step,rest⟩
    · have := t.isLt
      omega
    · obtain ⟨g,_,same,_,mem,_⟩ := step
      have gh : g = h := by omega
      subst g
      obtain ⟨i,rfl⟩ := inputsAsOpnd ao len mem
      have child := reach_mem_orIn t rest
      fin_cases i
      · exact Finset.mem_union.mpr (Or.inl child)
      · exact Finset.mem_union.mpr (Or.inr child)
  · intro hx
    have up (i : Fin 2) (mem : t ∈ side (n := n) C h i) : t ∈ orIn n C (n+h) := by
      have edge : OrStep n C (n+h) (opnd C h i) :=
        ⟨h,len,rfl,op,opndMem ao len i,opndBound ao len i⟩
      exact reach_mem_orIn t (.head edge (mem_orIn_reach t mem))
    rcases Finset.mem_union.mp hx with ha | hb
    · exact up 0 ha
    · exact up 1 hb

theorem promotionAtOperandEarlier (ao : IsAO2 n C) {a h : ℕ} {i : Fin 2}
    (len : a < C.gates.length) (hp : h ∈ promotionsAt G C (opnd C a i)) : h < a := by
  have path := (orReaches_reach h _ (Finset.mem_filter.mp hp).2.2).1
  have := orStep_le path
  have := opndBound ao len i
  omega

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux.Critical5857

open PEqualNP.EdgeOwnership

private abbrev G11 : SimpleGraph (Fin 11) := edgeGraph 11
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

/-- The four cases identified in the second group's 19:44 report. -/
private def pair : Fin 4 → Fin 3 → Fin 11 × Fin 11 :=
  ![![(0,9),(1,4),(3,6)],![(1,4),(2,5),(3,6)],
    ![(1,4),(2,5),(3,7)],![(1,4),(2,5),(6,7)]]

private def oldCover : Fin 4 → Finset (Fin 11) :=
  ![{5,7,8,10},{7,8,9,10},{6,8,9,10},{3,8,9,10}]

private def isolate : Fin 4 → Fin 11 := ![2,0,0,0]

private def other (k : Fin 4) (q : Fin 3 → Bool) : Finset (Fin 11) :=
  insert (isolate k) (Finset.univ.image fun i => if q i then (pair k i).2 else (pair k i).1)

private def removed (k : Fin 4) : Finset (Sym2 (Fin 11)) :=
  Finset.univ.image fun i => s((pair k i).1,(pair k i).2)

private def anchor : Fin 4 → Fin 4 → Fin 11 × Fin 11 :=
  ![![(5,2),(7,3),(8,1),(10,0)],![(7,3),(8,1),(9,0),(10,2)],
    ![(6,3),(8,1),(9,0),(10,2)],![(3,6),(8,1),(9,0),(10,2)]]

private def picked (k : Fin 4) (bits : Fin 4 → Bool) : Finset (Fin 11) :=
  Finset.univ.image fun i => if bits i then (anchor k i).1 else (anchor k i).2

private abbrev coversOld (k : Fin 4) (K : Finset (Fin 11)) : Prop :=
  ∀ u v, (G11.deleteEdges ↑(removed k)).Adj u v → u ∈ K ∨ v ∈ K

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem anchorCheck : (∀ k i, (G11.deleteEdges ↑(removed k)).Adj (anchor k i).1 (anchor k i).2) ∧
    (∀ k bits, (picked k bits).card = 4 ∧ (coversOld k (picked k bits) → picked k bits = oldCover k)) := by
  decide +kernel

/-- Four disjoint retained edges give sixteen possible covers of size at most
four, and only one choice actually covers every retained edge. -/
theorem uniqueOldFour (k : Fin 4) (K : Finset (Fin 11))
    (cover : coversOld k K) (size : K.card ≤ 4) : K = oldCover k := by
  let bits (i : Fin 4) : Bool := decide ((anchor k i).1 ∈ K)
  have contained : picked k bits ⊆ K := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    rcases cover _ _ (anchorCheck.1 k i) with ha | hb
    · simp [bits,ha]
    · by_cases ha : (anchor k i).1 ∈ K
      · simp [bits,ha]
      · simp [bits,ha,hb]
  have lower := (anchorCheck.2 k bits).1
  have eq := Finset.eq_of_subset_of_card_le contained (by omega)
  exact eq.symm.trans ((anchorCheck.2 k bits).2 (eq.symm ▸ cover))

/-- A labelled neighbour outside the old cover is forced into the unique star
whose selected centre is its other endpoint. -/
theorem forcedLeaf {V J : Type*} [DecidableEq V] (H : SimpleGraph V)
    (z : J → V) (P : J → Finset V) (distinct : Function.Injective z)
    (route : ∀ u v, H.Adj u v → ∃ j, (u = z j ∧ v ∈ P j) ∨ (v = z j ∧ u ∈ P j))
    (j : J) {w : V} (adj : H.Adj (z j) w) (outside : ∀ i, w ≠ z i) : w ∈ P j := by
  obtain ⟨i,(⟨eq,hw⟩ | ⟨eq,_⟩)⟩ := route (z j) w adj
  · have same := distinct eq
    simpa [same] using hw
  · exact (outside i eq).elim

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem fourTripleHits : ∀ k : Fin 4, ∀ z ∈ oldCover k, ∀ q : Fin 3 → Bool,
    (∀ u ∈ other k q, ∀ v ∈ other k q, ¬ G11.Adj u v) ∧
    ∃ w ∈ other k q, w ∉ oldCover k ∧ (G11.deleteEdges ↑(removed k)).Adj z w := by
  decide +kernel

end PEqualNP.Outside.L_meta_7465_aux.Critical5857

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Retain the orientation of each singleton side in the cover construction of
L-meta-6238. Then each retained edge comes with its actual opposite port. -/
theorem topIndexedStars (four : NoFourCycle G) (ao : IsAO2 n C) (empty : centreless G C = ∅) :
    ∃ (b : tops G C → Fin 2) (z : tops G C → Fin n),
      (∀ a : tops G C, side (n := n) C a (b a) = {z a}) ∧
      ∀ u v, (G.deleteEdges ↑(Ustar G C)).Adj u v → ∃ a : tops G C,
        (u = z a ∧ v ∈ side C a (1-b a)) ∨ (v = z a ∧ u ∈ side C a (1-b a)) := by
  classical
  have thin (a : tops G C) : (side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1 := by
    by_contra! both
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp both.1
    obtain ⟨v,hv,w,hw,hvw⟩ := Finset.one_lt_card.mp both.2
    exact forbidSecondNeighbor four hpq hvw (topAdj ao a.2 hp hv) (topAdj ao a.2 hq hv)
      (topAdj ao a.2 hq hw) (topAdj ao a.2 hp hw)
  have chooseSide (a : tops G C) : ∃ b : Fin 2, ∃ z : Fin n, side C a b = {z} := by
    have one (b : Fin 2) (upper : (side (n := n) C a b).card ≤ 1) : ∃ z : Fin n, side C a b = {z} := by
      have := Finset.card_pos.mpr (topSides empty a.2 b)
      exact Finset.card_eq_one.mp (by omega)
    rcases thin a with h | h
    · exact ⟨0,one 0 h⟩
    · exact ⟨1,one 1 h⟩
  choose b z singleton using chooseSide
  refine ⟨b,z,singleton,?_⟩
  have orientation (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have raw (a : tops G C) {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
      (u = z a ∧ v ∈ side C a (1-b a)) ∨ (v = z a ∧ u ∈ side C a (1-b a)) := by
    have eq := singleton a
    rcases orientation (b a) with h | h
    · rw [h] at eq
      exact Or.inl ⟨by simpa [eq] using hu,by simpa [h] using hv⟩
    · rw [h] at eq
      exact Or.inr ⟨by simpa [eq] using hv,by simpa [h] using hu⟩
  intro u v h
  obtain ⟨adj,retained⟩ := SimpleGraph.deleteEdges_adj.mp h
  have star : s(u,v) ∈ starEdges G C := by
    by_contra hn
    exact retained (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr adj,hn⟩)
  obtain ⟨a,ha,cross⟩ := Finset.mem_biUnion.mp star
  obtain ⟨⟨p,q⟩,pq,e⟩ := Finset.mem_image.mp cross
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp pq
  have route := raw ⟨a,ha⟩ hp hq
  refine ⟨⟨a,ha⟩,?_⟩
  rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact route
  · exact route.symm

private theorem injectiveFullImage {J V : Type*} [Fintype J] [DecidableEq V] (z : J → V)
    (size : (Finset.univ.image z).card = Fintype.card J) : Function.Injective z := by
  classical
  intro a b hab
  by_contra different
  let remaining := (Finset.univ : Finset J).erase a
  have subset : Finset.univ.image z ⊆ remaining.image z := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases same : i = a
    · subst i
      exact Finset.mem_image.mpr ⟨b,Finset.mem_erase.mpr ⟨Ne.symm different,Finset.mem_univ _⟩,hab.symm⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨same,Finset.mem_univ _⟩,rfl⟩
  have le := (Finset.card_le_card subset).trans Finset.card_image_le
  have count : remaining.card+1 = Fintype.card J := by
    simpa [remaining] using Finset.card_erase_add_one (Finset.mem_univ a)
  omega

namespace Critical5857

set_option maxHeartbeats 0 in
private theorem criticalFourCycle : NoFourCycle G11 := by
  unfold NoFourCycle
  decide +kernel

/-- In every critical case the selected centres are exactly the old four-cover.
At every maximal negative assignment the other operand of every top fires. -/
theorem criticalTopRows (k : Fin 4) (C : Circuit) (least : IsLeastAO G11 C)
    (empty : centreless G11 C = ∅) (size : (tops G11 C).card = 4)
    (edges : Ustar G11 C = removed k) :
    ∃ (b : tops G11 C → Fin 2) (z : tops G11 C → Fin 11),
      (∀ a : tops G11 C, side (n := 11) C a (b a) = {z a}) ∧ (∀ a, z a ∈ oldCover k) ∧
      ∀ (a : tops G11 C) (bits : Fin 3 → Bool), ∃ w ∈ other k bits, w ∈ side C a (1-b a) := by
  classical
  obtain ⟨b,z,singleton,served⟩ := topIndexedStars criticalFourCycle least.1 empty
  let Q := Finset.univ.image z
  have route (u v : Fin 11) (h : (G11.deleteEdges ↑(removed k)).Adj u v) :
      ∃ a : tops G11 C, (u = z a ∧ v ∈ side C a (1-b a)) ∨ (v = z a ∧ u ∈ side C a (1-b a)) := by
    apply served
    simpa [edges] using h
  have member (a : tops G11 C) : z a ∈ Q := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have cover : coversOld k Q := by
    intro u v uv
    obtain ⟨a,⟨rfl,_⟩ | ⟨rfl,_⟩⟩ := route u v uv
    · exact Or.inl (member a)
    · exact Or.inr (member a)
  have sizeQ : Q.card ≤ 4 := Finset.card_image_le.trans (by simp [size])
  have eq := uniqueOldFour k Q cover sizeQ
  have count (i : Fin 4) : (oldCover i).card = 4 := by revert i; decide +kernel
  have distinct := injectiveFullImage z (by change Q.card = _; rw [eq,count]; simp [size])
  have inOld (a : tops G11 C) : z a ∈ oldCover k := eq ▸ member a
  refine ⟨b,z,singleton,inOld,?_⟩
  intro a bits
  obtain ⟨w,hw,out,adj⟩ := (fourTripleHits k (z a) (inOld a) bits).2
  have leaf := forcedLeaf (G11.deleteEdges ↑(removed k)) z (fun i => side C i (1-b i))
    distinct route a adj (fun i he => out (he.symm ▸ inOld i))
  exact ⟨w,hw,leaf⟩

end Critical5857

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- On the specified positive/negative samples, select only the nonempty-raw
exceptional ORs that feed the centre sides of tops. -/
theorem starPromotionSeparation {I K : Type*} (least : IsLeastAO G C)
    (b : tops G C → Fin 2) (z : tops G C → Fin n)
    (singleton : ∀ a : tops G C, side (n := n) C a (b a) = {z a})
    (pair : I → Fin n × Fin n) (pos : ∀ i, G.Adj (pair i).1 (pair i).2)
    (outside : ∀ i a, z a ≠ (pair i).1 ∧ z a ≠ (pair i).2)
    (neg : K → Fin n → Bool) (noEdge : ∀ k, graphFun G ∅ (neg k) = false)
    (leaves : ∀ (a : tops G C) (k : K), ∃ w ∈ side C a (1-b a), neg k w = true) :
    ∃ selected : Finset ℕ,
      (∀ h ∈ selected, h ∈ orN G C \ lam G C ∧ (orIn n C (n+h)).Nonempty ∧
        ∃ a : tops G C, OrReaches n C (opnd C a (b a)) h) ∧
      (∀ i, ∃ h ∈ selected, gateVal n C h (pairInput (pair i).1 (pair i).2) = true) ∧
      ∀ k h, h ∈ selected → gateVal n C h (neg k) = false := by
  classical
  let atCentre (a : tops G C) := promotionsAt G C (opnd C a (b a))
  let selected := Finset.univ.biUnion atCentre
  have source {h : ℕ} (hh : h ∈ selected) : ∃ a : tops G C, h ∈ atCentre a := by
    obtain ⟨a,_,found⟩ := Finset.mem_biUnion.mp hh
    exact ⟨a,found⟩
  refine ⟨selected,?_,?_,?_⟩
  · intro h hh
    obtain ⟨a,ha⟩ := source hh
    obtain ⟨exception,nonempty,path⟩ := Finset.mem_filter.mp ha
    exact ⟨exception,nonempty,a,path⟩
  · intro i
    obtain ⟨a,ha,fire⟩ := acceptedTop least (pos i)
    let root : tops G C := ⟨a,ha⟩
    have data := topData ha
    have on := (andValOperands least.1 data.1 data.2.1 _).mp fire (b root)
    have limit := opndBound least.1 data.1 (b root)
    have nonempty : (orIn n C (opnd C a (b root))).Nonempty := by
      change (side (n := n) C root (b root)).Nonempty
      rw [singleton]
      exact Finset.singleton_nonempty _
    rcases (nonemptyPortValue (G := G) least.1 _ _ (by omega) nonempty).mp on with
      ⟨t,mem,onlit⟩ | ⟨h,atPort,onh⟩
    · change t ∈ side (n := n) C root (b root) at mem
      have same : t = z root := by simpa [singleton] using mem
      have hcase := (pairInput_true _ _ _).mp onlit
      exact ((hcase.imp (fun e => same.symm.trans e) (fun e => same.symm.trans e)).elim
        (outside i root).1 (outside i root).2).elim
    · exact ⟨h,Finset.mem_biUnion.mpr ⟨root,Finset.mem_univ _,atPort⟩,onh⟩
  · intro k h hh
    obtain ⟨a,ha⟩ := source hh
    obtain ⟨w,hw,hx⟩ := leaves a k
    have path := (orReaches_reach h _ (Finset.mem_filter.mp ha).2.2).1
    apply Bool.eq_false_iff.mpr
    intro on
    have fire := firingTop least.1 a.2 path hw (neg k) on hx
    exact Bool.false_ne_true ((noEdge k).symm.trans fire)

namespace Critical5857

set_option maxHeartbeats 0 in
private theorem criticalEnds : ∀ k i, G11.Adj (pair k i).1 (pair k i).2 ∧
    (pair k i).1 ∉ oldCover k ∧ (pair k i).2 ∉ oldCover k := by
  decide +kernel

theorem criticalSelected (k : Fin 4) (C : Circuit) (least : IsLeastAO G11 C)
    (empty : centreless G11 C = ∅) (size : (tops G11 C).card = 4)
    (edges : Ustar G11 C = removed k) :
    ∃ selected : Finset ℕ,
      (∀ h ∈ selected, h ∈ orN G11 C \ lam G11 C ∧ (orIn 11 C (11+h)).Nonempty ∧
        ∃ a ∈ tops G11 C, ∃ i : Fin 2, OrReaches 11 C (opnd C a i) h) ∧
      (∀ i, ∃ h ∈ selected, gateVal 11 C h (pairInput (pair k i).1 (pair k i).2) = true) ∧
      ∀ bits : Fin 3 → Bool, ∀ h ∈ selected,
        gateVal 11 C h (fun t => decide (t ∈ other k bits)) = false := by
  obtain ⟨b,z,one,old,hits⟩ := criticalTopRows k C least empty size edges
  let neg (bits : Fin 3 → Bool) (t : Fin 11) := decide (t ∈ other k bits)
  have noEdge (bits : Fin 3 → Bool) : graphFun G11 ∅ (neg bits) = false := by
    apply Bool.eq_false_iff.mpr
    intro on
    have present : ∀ i : Fin 4, (oldCover i).Nonempty := by decide +kernel
    obtain ⟨centre,mem⟩ := present k
    have independent := (fourTripleHits k centre mem bits).1
    simp [graphFun,neg] at on
    obtain ⟨u,v,uv,hu,hv⟩ := on
    exact independent u hu v hv uv
  have outside (i : Fin 3) (a : tops G11 C) : z a ≠ (pair k i).1 ∧ z a ≠ (pair k i).2 := by
    obtain ⟨_,hp,hq⟩ := criticalEnds k i
    exact ⟨fun eq => hp (eq ▸ old a), fun eq => hq (eq ▸ old a)⟩
  have otherHits (a : tops G11 C) (bits : Fin 3 → Bool) :
      ∃ w ∈ side C a (1-b a), neg bits w = true := by
    obtain ⟨w,hw,hport⟩ := hits a bits
    exact ⟨w,hport,by simp [neg,hw]⟩
  obtain ⟨S,form,positive,negative⟩ := starPromotionSeparation least b z one (pair k)
    (fun i => (criticalEnds k i).1) outside neg noEdge otherHits
  refine ⟨S,?_,positive,negative⟩
  intro h hh
  obtain ⟨ex,nonempty,a,path⟩ := form h hh
  exact ⟨ex,nonempty,a,a.2,b a,path⟩

end Critical5857

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux.ThreeMatching

/-- A clause is a mask of formal raw OR ports. After substitution each
such atom is itself a disjunction of original input variables. -/
abbrev CNF := List Nat

def lit (a : Nat) (v : Nat → Prop) : Prop := ∃ i, a.testBit i = true ∧ v i
def holds (f : CNF) (v : Nat → Prop) : Prop := ∀ a ∈ f, lit a v

def insertClause (a : Nat) (cs : CNF) : CNF :=
  if cs.any (fun b => (b &&& a) == b) then cs
  else a :: cs.filter (fun b => !((a &&& b) == a))

def minimize (cs : CNF) : CNF := cs.foldl (fun found a => insertClause a found) []
def conj (p q : CNF) : CNF := minimize (p++q)
def disj (p q : CNF) : CNF := minimize (p.flatMap (fun a => q.map (fun b => a ||| b)))

private theorem lit_mono {a b : Nat} (h : a &&& b = a) (v : Nat → Prop) :
    lit a v → lit b v := by
  rintro ⟨i,hi,hv⟩
  have e := congrArg (fun k : Nat => k.testBit i) h
  have hb : b.testBit i = true := by simpa [Nat.testBit_and,hi] using e
  exact ⟨i,hb,hv⟩

private theorem lit_join (a b : Nat) (v : Nat → Prop) :
    lit (a ||| b) v ↔ lit a v ∨ lit b v := by
  constructor
  · rintro ⟨i,hi,hv⟩
    rcases (show a.testBit i = true ∨ b.testBit i = true by simpa [Nat.testBit_or] using hi) with ha | hb
    · exact Or.inl ⟨i,ha,hv⟩
    · exact Or.inr ⟨i,hb,hv⟩
  · rintro (⟨i,ha,hv⟩ | ⟨i,hb,hv⟩)
    · exact ⟨i,by simp [Nat.testBit_or,ha],hv⟩
    · exact ⟨i,by simp [Nat.testBit_or,hb],hv⟩

private theorem insert_holds (a : Nat) (cs : CNF) (v : Nat → Prop) :
    holds (insertClause a cs) v ↔ holds cs v ∧ lit a v := by
  classical
  unfold insertClause
  split
  next h =>
    obtain ⟨b,hb,he⟩ := List.any_eq_true.mp h
    have his : b &&& a = b := by simpa using he
    exact ⟨fun hf => ⟨hf,lit_mono his v (hf b hb)⟩,And.left⟩
  next _ =>
    constructor
    · intro good
      have first : lit a v := good a (by simp)
      refine ⟨?_,first⟩
      intro b hb
      by_cases hab : a &&& b = a
      · exact lit_mono hab v first
      · exact good b (by simp [hb,hab])
    · rintro ⟨good,first⟩ b hb
      rcases List.mem_cons.mp hb with rfl | kept
      · exact first
      · exact good _ (List.mem_filter.mp kept).1

private theorem minimize_holds (cs : CNF) (v : Nat → Prop) :
    holds (minimize cs) v ↔ holds cs v := by
  have fold (xs initial : CNF) :
      holds (xs.foldl (fun found a => insertClause a found) initial) v ↔ holds initial v ∧ holds xs v := by
    induction xs generalizing initial with
    | nil => simp [holds]
    | cons a rest ih =>
      rw [List.foldl_cons,ih,insert_holds]
      simp only [holds,List.mem_cons,forall_eq_or_imp]
      tauto
  simpa [minimize,holds] using fold cs []

theorem conj_holds (p q : CNF) (v : Nat → Prop) :
    holds (conj p q) v ↔ holds p v ∧ holds q v := by
  rw [conj,minimize_holds]
  constructor
  · intro good
    exact ⟨fun a ha => good a (List.mem_append_left q ha),
      fun a ha => good a (List.mem_append_right p ha)⟩
  · rintro ⟨hp, hq⟩ a ha
    rcases List.mem_append.mp ha with left | right
    · exact hp a left
    · exact hq a right

theorem disj_holds (p q : CNF) (v : Nat → Prop) :
    holds (disj p q) v ↔ holds p v ∨ holds q v := by
  classical
  rw [disj,minimize_holds]
  constructor
  · intro all
    by_cases hp : holds p v
    · exact Or.inl hp
    · right
      obtain ⟨a,ha,bad⟩ := (show ∃ a ∈ p, ¬ lit a v by simpa [holds] using hp)
      intro b hb
      have hl := all (a ||| b) (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)
      exact ((lit_join a b v).mp hl).resolve_left bad
  · intro alt c hc
    obtain ⟨a,ha,entry⟩ := List.mem_flatMap.mp hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp entry
    apply (lit_join a b v).mpr
    rcases alt with hp | hq
    · exact Or.inl (hp _ ha)
    · exact Or.inr (hq _ hb)

inductive Kind where
  | andGate | emptyOr | nonemptyOr
deriving DecidableEq

private def rawOptions (i : Nat) (previous : List CNF) : List CNF :=
  previous.foldl (fun pool p => pool ++ pool.map (fun f => disj f p)) [[2^i]]

/-- Every specified selection of earlier nonempty-raw promotions appears in
the enumerator. The same symbolic formula works for every assignment. -/
theorem rawOptionsComplete (i : Nat) (previous : List (Nat × CNF)) (chosen : Nat → Prop) :
    ∃ f ∈ rawOptions i (previous.map Prod.snd), ∀ v : Nat → Prop,
      holds f v ↔ v i ∨ ∃ q ∈ previous, chosen q.1 ∧ holds q.2 v := by
  classical
  induction previous using List.reverseRecOn with
  | nil =>
    refine ⟨[2^i],by simp [rawOptions],?_⟩
    intro v
    simp [holds,lit,Nat.testBit_two_pow]
  | append_singleton ps q ih =>
    obtain ⟨f,hf,e⟩ := ih
    let opts := rawOptions i (ps.map Prod.snd)
    have grow : rawOptions i ((ps++[q]).map Prod.snd) = opts ++ opts.map (fun g => disj g q.2) := by
      simp [opts,rawOptions,List.foldl_append]
    by_cases take : chosen q.1
    · refine ⟨disj f q.2,?_,?_⟩
      · rw [grow]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
      · intro v
        rw [disj_holds,e]
        simp [List.mem_append, take, or_assoc]
    · refine ⟨f,?_,?_⟩
      · rw [grow]
        exact List.mem_append_left _ hf
      · intro v
        rw [e]
        simp [List.mem_append,take]

inductive PortMode where
  | rawOnly | directOnly | either
deriving DecidableEq

def leftMode : Kind → PortMode
  | .andGate => .either
  | .emptyOr => .directOnly
  | .nonemptyOr => .rawOnly

def rightMode : Kind → PortMode
  | .emptyOr => .directOnly
  | _ => .either

def ports (mode : PortMode) (i : Nat) (direct promoted : List CNF) : List CNF :=
  match mode with
  | .rawOnly => rawOptions i promoted
  | .directOnly => direct
  | .either => rawOptions i promoted ++ direct

def applyGate (op : Kind) (l r : CNF) : CNF := match op with
  | .andGate => conj l r
  | _ => disj l r

def gateOptions (op : Kind) (index : Nat) (direct promoted : List CNF) : List CNF :=
  (ports (leftMode op) (2*index) direct promoted).flatMap (fun a =>
    (ports (rightMode op) (2*index+1) direct promoted).map (applyGate op a))

def outcomes : List Kind → Nat → List CNF → List CNF → Bool → List CNF
  | [], _, _, recent, useBoth =>
    match recent with
    | [] => []
    | latest :: earlier => if useBoth then earlier.map (disj latest) else [latest]
  | op :: tail, index, direct, promoted, useBoth =>
    (gateOptions op index direct promoted).flatMap (fun f => match op with
      | .nonemptyOr => outcomes tail (index+1) direct (f::promoted) useBoth
      | _ => outcomes tail (index+1) (f::direct) promoted useBoth)

private def allKindLists : Nat → List (List Kind)
  | 0 => [[]]
  | k+1 => [] :: [Kind.andGate, Kind.emptyOr, Kind.nonemptyOr].flatMap
      (fun tag => (allKindLists k).map (fun tail => tag::tail))

private theorem listed (size : Nat) (ops : List Kind) (bound : ops.length ≤ size) : ops ∈ allKindLists size := by
  induction size generalizing ops with
  | zero =>
    have eq : ops = [] := List.length_eq_zero_iff.mp (by omega)
    simp [allKindLists,eq]
  | succ k ih =>
    cases ops with
    | nil => simp [allKindLists]
    | cons tag tail =>
      have ht := ih tail (by simpa using bound)
      have member : tag ∈ [Kind.andGate,Kind.emptyOr,Kind.nonemptyOr] := by cases tag <;> simp
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨tag,member,List.mem_map.mpr ⟨tail,ht,rfl⟩⟩)

private def relevantKindList (ops : List Kind) : Bool := decide
  (ops.getLast? = some Kind.nonemptyOr ∧ ops.count Kind.andGate ≤ 3 ∧
    ops.count Kind.emptyOr + ops.count Kind.nonemptyOr ≤ 2)

private def checkAll : Bool := (allKindLists 5).all (fun ops =>
  !relevantKindList ops || [false,true].all (fun both =>
    (outcomes ops 0 [] [] both).all (fun c => decide (c.length ≤ 6))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prefixBounds : checkAll = true := by
  decide +kernel

theorem sixClauses (ops : List Kind) (both : Bool) {f : CNF} (length : ops.length ≤ 5)
    (last : ops.getLast? = some Kind.nonemptyOr) (ands : ops.count Kind.andGate ≤ 3)
    (ors : ops.count Kind.emptyOr + ops.count Kind.nonemptyOr ≤ 2)
    (h : f ∈ outcomes ops 0 [] [] both) : f.length ≤ 6 := by
  have all := (List.all_eq_true.mp prefixBounds) ops (listed 5 ops length)
  have eligible : relevantKindList ops = true := by simp [relevantKindList,last,ands,ors]
  rw [eligible] at all
  have bounds :
      (∀ c ∈ outcomes ops 0 [] [] false, c.length ≤ 6) ∧
      (∀ c ∈ outcomes ops 0 [] [] true, c.length ≤ 6) := by
    simpa using all
  cases both with
  | false => exact bounds.1 f h
  | true => exact bounds.2 f h

/-- Every matching transversal misses a distinct clause of an output that
accepts its pair inputs. Extra vertices are allowed on negative assignments. -/
theorem substitutionLower {V J : Type*} [Fintype J] (f : CNF) (raw : Nat → Set V)
    (ends : J → Bool → V) (neg : (J → Bool) → Set V)
    (contains : ∀ bits i, ends i (bits i) ∈ neg bits)
    (positive : ∀ i, holds f (fun a => ends i false ∈ raw a ∨ ends i true ∈ raw a))
    (negative : ∀ bits, ¬ holds f (fun a => ∃ v ∈ raw a, v ∈ neg bits)) :
    2^Fintype.card J ≤ f.length := by
  classical
  have missed (bits : J → Bool) : ∃ k : Fin f.length,
      ∀ i, ¬ ∃ a, (f.get k).testBit a = true ∧ ends i (bits i) ∈ raw a := by
    obtain ⟨c,hc,hmiss⟩ := (show ∃ c ∈ f, ¬ lit c (fun a => ∃ v ∈ raw a, v ∈ neg bits) by
      simpa [holds] using negative bits)
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hc
    refine ⟨k,?_⟩
    rintro i ⟨a,ha,hit⟩
    rw [hk] at ha
    exact hmiss ⟨a,ha,ends i (bits i),hit,contains bits i⟩
  choose witness miss using missed
  have inj : Function.Injective witness := by
    intro x y same
    funext i
    have hx := miss x i
    have hy := miss y i
    rw [← same] at hy
    obtain ⟨a,ha,edge⟩ := positive i (f.get (witness x)) (List.get_mem _ _)
    cases bx : x i <;> cases by' : y i
    · rfl
    · rw [bx] at hx
      rw [by'] at hy
      rcases edge with h | h
      · exact (hx ⟨a,ha,h⟩).elim
      · exact (hy ⟨a,ha,h⟩).elim
    · rw [bx] at hx
      rw [by'] at hy
      rcases edge with h | h
      · exact (hy ⟨a,ha,h⟩).elim
      · exact (hx ⟨a,ha,h⟩).elim
    · rfl
  simpa using Fintype.card_le_of_injective witness inj

end PEqualNP.Outside.L_meta_7465_aux.ThreeMatching

namespace PEqualNP.Outside.L_meta_7465_aux.ThreeMatching

variable {X : Type*}

private abbrev Meaning (X : Type*) := X → Prop

def represents (raw : Nat → Meaning X) (f : CNF) (u : Meaning X) : Prop :=
  ∀ x, holds f (fun i => raw i x) ↔ u x

def known (raw signal : Nat → Meaning X) (ids : List Nat) (table : List (Nat × CNF)) : Prop :=
  table.map Prod.fst = ids ∧ ∀ q ∈ table, represents raw q.2 (signal q.1)

inductive PortLaw (raw signal : Nat → Meaning X) (mode : PortMode) (atom : Nat)
    (direct promoted : List Nat) (w : Meaning X) : Prop where
  | ordinary (allowed : mode ≠ .directOnly) (chosen : Finset Nat)
      (before : ∀ g ∈ chosen, g ∈ promoted)
      (value : ∀ x, w x ↔ raw atom x ∨ ∃ g ∈ chosen, signal g x)
  | exactGate (allowed : mode ≠ .rawOnly) (g : Nat) (before : g ∈ direct)
      (value : ∀ x, w x ↔ signal g x)

private theorem portComplete {raw signal : Nat → Meaning X} {mode atom di pr w}
    (port : PortLaw raw signal mode atom di pr w) {ds ps : List (Nat × CNF)}
    (dc : known raw signal di ds) (pc : known raw signal pr ps) :
    ∃ f ∈ ports mode atom (ds.map Prod.snd) (ps.map Prod.snd), represents raw f w := by
  classical
  cases port with
  | ordinary allowed chosen before value =>
    obtain ⟨f,hf,law⟩ := rawOptionsComplete atom ps (fun i => i ∈ chosen)
    refine ⟨f,?_,?_⟩
    · cases mode <;> simp_all [ports]
    · intro x
      rw [law,value]
      constructor
      · rintro (p | ⟨q,hq,hchosen,hits⟩)
        · exact Or.inl p
        · exact Or.inr ⟨q.1,hchosen,((pc.2 q hq) x).mp hits⟩
      · rintro (p | ⟨g,hg,hits⟩)
        · exact Or.inl p
        · have seen := before g hg
          rw [← pc.1] at seen
          obtain ⟨q,hq,eq⟩ := List.mem_map.mp seen
          exact Or.inr ⟨q,hq,eq ▸ hg,((pc.2 q hq) x).mpr (eq ▸ hits)⟩
  | exactGate allowed g before value =>
    rw [← dc.1] at before
    obtain ⟨q,hq,eq⟩ := List.mem_map.mp before
    refine ⟨q.2,?_,?_⟩
    · have present : q.2 ∈ ds.map Prod.snd := List.mem_map.mpr ⟨q,hq,rfl⟩
      cases mode <;> simp_all [ports]
    · intro x
      rw [(dc.2 q hq) x,value,eq]

def semanticGate (op : Kind) (l r : Prop) : Prop := match op with
  | .andGate => l ∧ r
  | _ => l ∨ r

private theorem applyGate_rep {raw : Nat → Meaning X} {f g : CNF} {l r : Meaning X}
    (op : Kind) (left : represents raw f l) (right : represents raw g r) :
    represents raw (applyGate op f g) (fun x => semanticGate op (l x) (r x)) := by
  intro x
  cases op <;> simp [applyGate,semanticGate,conj_holds,disj_holds,left x,right x]

private def rememberDirect {V : Type*} (op : Kind) (x : V) (vs : List V) : List V :=
  match op with | .nonemptyOr => vs | _ => x::vs

private def rememberPromoted {V : Type*} (op : Kind) (x : V) (vs : List V) : List V :=
  match op with | .nonemptyOr => x::vs | _ => vs

private def finished (signal : Nat → Meaning X) (promoted : List Nat) (both : Bool) (out : Meaning X) : Prop :=
  match promoted with
  | [] => False
  | g::gs => if both then ∃ h ∈ gs, ∀ x, out x ↔ signal g x ∨ signal h x
    else ∀ x, out x ↔ signal g x

/-- Chronological, assignment-independent representation of the charged gates
from a real circuit. The port decompositions hold for every assignment. -/
def follows (raw signal : Nat → Meaning X) (both : Bool) (out : Meaning X) :
    List (Nat × Kind) → Nat → List Nat → List Nat → Prop
  | [], _, _, promoted => finished signal promoted both out
  | (g,op)::rest, i, direct, promoted =>
    ∃ l r : Meaning X,
      PortLaw raw signal (leftMode op) (2*i) direct promoted l ∧
      PortLaw raw signal (rightMode op) (2*i+1) direct promoted r ∧
      (∀ x, signal g x ↔ semanticGate op (l x) (r x)) ∧
      follows raw signal both out rest (i+1) (rememberDirect op g direct) (rememberPromoted op g promoted)

private theorem consKnown {raw signal : Nat → Meaning X} {table : List (Nat × CNF)}
    {ids g f} (old : known raw signal ids table) (code : represents raw f (signal g)) :
    known raw signal (g::ids) ((g,f)::table) := by
  refine ⟨by simp [old.1],?_⟩
  intro q hq
  rcases List.mem_cons.mp hq with rfl | h
  · exact code
  · exact old.2 q h

theorem followsHasOutput {raw signal : Nat → Meaning X} {both : Bool} {out : Meaning X}
    (events : List (Nat × Kind)) (i : Nat) (di pr : List Nat) (ds ps : List (Nat × CNF))
    (dc : known raw signal di ds) (pc : known raw signal pr ps)
    (trace : follows raw signal both out events i di pr) :
    ∃ f ∈ outcomes (events.map Prod.snd) i (ds.map Prod.snd) (ps.map Prod.snd) both,
      represents raw f out := by
  induction events generalizing i di pr ds ps with
  | nil =>
    cases ps with
    | nil =>
      have eq : pr = [] := pc.1.symm
      subst pr
      exact trace.elim
    | cons q qs =>
      have eq : pr = q.1 :: qs.map Prod.fst := pc.1.symm
      subst pr
      have head := pc.2 q (by simp)
      cases both with
      | false =>
        refine ⟨q.2,by simp [outcomes],?_⟩
        intro x
        exact (head x).trans (trace x).symm
      | true =>
        obtain ⟨h,hh,relation⟩ := trace
        obtain ⟨p,hp,eq⟩ := List.mem_map.mp hh
        have later := pc.2 p (List.mem_cons_of_mem _ hp)
        refine ⟨disj q.2 p.2,?_,?_⟩
        · simp only [List.map_nil,List.map_cons,outcomes,ite_true]
          exact List.mem_map.mpr ⟨p.2,List.mem_map.mpr ⟨p,hp,rfl⟩,rfl⟩
        · intro x
          rw [disj_holds,head x,later x,relation x,eq]
  | cons stage rest ih =>
    obtain ⟨g,op⟩ := stage
    obtain ⟨l,r,ll,rr,evaluation,next⟩ := trace
    obtain ⟨f,hf,fc⟩ := portComplete ll dc pc
    obtain ⟨h,hh,hc⟩ := portComplete rr dc pc
    let code := applyGate op f h
    have member : code ∈ gateOptions op i (ds.map Prod.snd) (ps.map Prod.snd) :=
      List.mem_flatMap.mpr ⟨f,hf,List.mem_map.mpr ⟨h,hh,rfl⟩⟩
    have good : represents raw code (signal g) := fun x =>
      (applyGate_rep op fc hc x).trans (evaluation x).symm
    have dnext : known raw signal (rememberDirect op g di) (rememberDirect op (g,code) ds) := by
      cases op <;> first | exact dc | exact consKnown dc good
    have pnext : known raw signal (rememberPromoted op g pr) (rememberPromoted op (g,code) ps) := by
      cases op <;> first | exact pc | exact consKnown pc good
    obtain ⟨result,record,correct⟩ := ih _ _ _ _ _ dnext pnext next
    refine ⟨result,List.mem_flatMap.mpr ⟨code,member,?_⟩,correct⟩
    cases op <;> exact record

end PEqualNP.Outside.L_meta_7465_aux.ThreeMatching

namespace PEqualNP.Outside.L_meta_7465_aux

open ThreeMatching
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private def liesUnderAnd (n : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ ∃ i : Fin 2, OrReaches n C (opnd C a i) h

/-- Exceptional OR gates outside every AND operand are irrelevant to every
port of an AND or one of its OR predecessors. -/
private noncomputable def activeGates (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ := by
  classical
  exact junk G C ∪ (orN G C \ lam G C).filter (liesUnderAnd n C)

private noncomputable def gateKind (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : ℕ) : ThreeMatching.Kind := by
  classical
  exact if h ∈ junk G C then .andGate else
    if (orIn n C (n+h)).Nonempty then .nonemptyOr else .emptyOr

private theorem exceptionNotJunk {h : ℕ} (he : h ∈ orN G C \ lam G C) : h ∉ junk G C := by
  intro j
  have a := (junkData j).2.1
  have o := (orData he).2.1
  rw [a] at o
  cases o

private theorem activeLength {h : ℕ} (hs : h ∈ activeGates G C) : h < C.gates.length := by
  classical
  rcases Finset.mem_union.mp hs with j | ex
  · exact (junkData j).1
  · exact (orData (Finset.mem_filter.mp ex).1).1

private theorem underForPort (ao : IsAO2 n C) {g : ℕ} (hg : g ∈ activeGates G C) (i : Fin 2) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a b) (opnd C g i) := by
  classical
  rcases Finset.mem_union.mp hg with j | ex
  · exact ⟨g,(junkData j).1,(junkData j).2.1,i,.refl⟩
  · obtain ⟨exc,a,al,ha,b,wire⟩ := Finset.mem_filter.mp ex
    have len := (orData exc).1
    have edge : OrStep n C (n+g) (opnd C g i) :=
      ⟨g,len,rfl,(orData exc).2.1,opndMem ao len _,opndBound ao len _⟩
    exact ⟨a,al,ha,b,((orReaches_reach g _ wire).1).tail edge⟩

/-- Convert one actual operand, on every Boolean assignment, into one of the
port forms used in the finite symbolic enumeration. -/
theorem actualPortLaw (ao : IsAO2 n C) (top : TopForm G C) {g : ℕ}
    (hg : g ∈ activeGates G C) (i : Fin 2) (mode : PortMode) (atom : ℕ)
    (atomVal : ℕ → (Fin n → Bool) → Prop) (direct promoted : List ℕ)
    (atomEq : ∀ x, atomVal atom x ↔ ∃ t ∈ side (n := n) C g i, x t = true)
    (rawFits : (side (n := n) C g i).Nonempty → mode ≠ .directOnly)
    (emptyFits : side (n := n) C g i = ∅ → mode ≠ .rawOnly)
    (previousP : ∀ h ∈ activeGates G C, h < g → gateKind G C h = .nonemptyOr → h ∈ promoted)
    (previousD : ∀ h ∈ activeGates G C, h < g → gateKind G C h ≠ .nonemptyOr → h ∈ direct) :
    PortLaw atomVal (fun h x => gateVal n C h x = true) mode atom direct promoted
      (fun x => val C (List.ofFn x) (opnd C g i) = true) := by
  classical
  obtain ⟨a,alen,aAnd,b,parent⟩ := underForPort ao hg i
  have len := activeLength hg
  have small := opndBound ao len i
  by_cases raw : (side (n := n) C g i).Nonempty
  · let U := promotionsAt G C (opnd C g i)
    refine PortLaw.ordinary (rawFits raw) U ?_ ?_
    · intro h hh
      obtain ⟨exception,nonempty,hr⟩ := Finset.mem_filter.mp hh
      have trans := parent.trans (orReaches_reach h _ hr).1
      have under : liesUnderAnd n C h := ⟨a,alen,aAnd,b,reach_orReaches trans h rfl (orData exception).1⟩
      apply previousP h (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨exception,under⟩))
        (promotionAtOperandEarlier ao len hh)
      simp [gateKind,exceptionNotJunk exception,nonempty]
    · intro x
      rw [atomEq]
      exact nonemptyPortValue (G := G) ao x _ (by omega) raw
  · have zero := Finset.not_nonempty_iff_eq_empty.mp raw
    obtain ⟨h,wire,junkOr⟩ := emptyPortSource ao top alen aAnd parent zero
    have less : h < g := by omega
    have hz : orIn n C (n+h) = ∅ := by simpa [side,wire] using zero
    have inList : h ∈ direct := by
      rcases junkOr with junk | ex
      · exact previousD h (Finset.mem_union_left _ junk) less (by simp [gateKind,junk])
      · have path : OrReaches n C (opnd C a b) h := reach_orReaches parent h wire (orData ex).1
        have under : liesUnderAnd n C h := ⟨a,alen,aAnd,b,path⟩
        apply previousD h (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ex,under⟩)) less
        simp [gateKind,exceptionNotJunk ex,hz]
    refine PortLaw.exactGate (emptyFits zero) h inList ?_
    intro x
    rw [wire]
    rfl

private noncomputable def orderedPort (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (i : Fin 2) : Fin 2 := by
  classical
  exact if gateKind G C g = .nonemptyOr ∧ side (n := n) C g 0 = ∅ then 1-i else i

private def portMode (op : ThreeMatching.Kind) (i : Fin 2) := if i = 0 then leftMode op else rightMode op

private theorem portEligibility (ao : IsAO2 n C) {g : ℕ} (hg : g ∈ activeGates G C) (i : Fin 2) :
    ((side (n := n) C g (orderedPort G C g i)).Nonempty → portMode (gateKind G C g) i ≠ .directOnly) ∧
    (side (n := n) C g (orderedPort G C g i) = ∅ → portMode (gateKind G C g) i ≠ .rawOnly) := by
  classical
  rcases Finset.mem_union.mp hg with j | sex
  · fin_cases i <;> simp [gateKind,j,orderedPort,portMode,leftMode,rightMode]
  · have ex := (Finset.mem_filter.mp sex).1
    have nj := exceptionNotJunk ex
    have union := orRawUnion ao (orData ex).1 (orData ex).2.1
    by_cases raw : (orIn n C (n+g)).Nonempty
    · have atLeast : (side (n := n) C g 0).Nonempty ∨ (side (n := n) C g 1).Nonempty := by
        simpa [union] using raw
      by_cases z : side (n := n) C g 0 = ∅
      · have right : (side (n := n) C g 1).Nonempty := by simpa [z] using atLeast
        fin_cases i <;> simp [gateKind,nj,raw,orderedPort,portMode,leftMode,rightMode,z,right.ne_empty]
      · fin_cases i <;> simp [gateKind,nj,raw,orderedPort,portMode,leftMode,rightMode,z]
    · have bothEmpty := Finset.not_nonempty_iff_eq_empty.mp raw
      rw [union] at bothEmpty
      have each := Finset.union_eq_empty.mp bothEmpty
      fin_cases i <;> simp [gateKind,nj,raw,orderedPort,portMode,leftMode,rightMode,each.1,each.2]

private theorem orValTwo (ao : IsAO2 n C) {g : ℕ} (len : g < C.gates.length)
    (op : (gateAt C g).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C g x = true ↔ val C (List.ofFn x) (opnd C g 0) = true ∨
      val C (List.ofFn x) (opnd C g 1) = true := by
  change val C (List.ofFn x) (n+g) = true ↔ _
  rw [val_or (n := n) (by simp) len op]
  constructor
  · rintro ⟨w,hw,_,fire⟩
    obtain ⟨i,rfl⟩ := inputsAsOpnd ao len hw
    fin_cases i
    · exact Or.inl fire
    · exact Or.inr fire
  · rintro (left | right)
    · exact ⟨_,opndMem ao len 0,opndBound ao len 0,left⟩
    · exact ⟨_,opndMem ao len 1,opndBound ao len 1,right⟩

private theorem stageMeaning (ao : IsAO2 n C) {g : ℕ} (hg : g ∈ activeGates G C) (x : Fin n → Bool) :
    gateVal n C g x = true ↔ semanticGate (gateKind G C g)
      (val C (List.ofFn x) (opnd C g (orderedPort G C g 0)) = true)
      (val C (List.ofFn x) (opnd C g (orderedPort G C g 1)) = true) := by
  classical
  rcases Finset.mem_union.mp hg with j | sex
  · simpa [semanticGate,gateKind,j,orderedPort] using
      andValBoth ao (junkData j).1 (junkData j).2.1 x
  · have ex := (Finset.mem_filter.mp sex).1
    have nj := exceptionNotJunk ex
    have gate := orValTwo ao (orData ex).1 (orData ex).2.1 x
    by_cases raw : (orIn n C (n+g)).Nonempty
    · by_cases z : side (n := n) C g 0 = ∅
      · simpa [semanticGate,gateKind,nj,raw,orderedPort,z,or_comm] using gate
      · simpa [semanticGate,gateKind,nj,raw,orderedPort,z] using gate
    · simpa [semanticGate,gateKind,nj,raw,orderedPort] using gate

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open ThreeMatching
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private noncomputable def promotedKeys (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (priorGates : List ℕ) := priorGates.reverse.filter fun h => decide (gateKind G C h = .nonemptyOr)
private noncomputable def directKeys (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (priorGates : List ℕ) := priorGates.reverse.filter fun h => decide (gateKind G C h ≠ .nonemptyOr)

private noncomputable def rawAt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (gates : List ℕ) (index : ℕ) : Set (Fin n) :=
  let g := gates.getD (index/2) 0
  let b : Fin 2 := ⟨index % 2,Nat.mod_lt _ (by decide)⟩
  ↑(side (n := n) C g (orderedPort G C g b))

private theorem rawAtCurrent (priorGates rest : List ℕ) (g : ℕ) (b : Fin 2) :
    rawAt G C (priorGates ++ g::rest) (2*priorGates.length+b.val) = ↑(side (n := n) C g (orderedPort G C g b)) := by
  have div : (2*priorGates.length+b.val)/2 = priorGates.length := by have := b.isLt; omega
  have rem : (2*priorGates.length+b.val) % 2 = b.val := by have := b.isLt; omega
  have item : (priorGates++g::rest).getD priorGates.length 0 = g := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]
  unfold rawAt
  simp only [div,item]
  have matchB : (⟨(2*priorGates.length+b.val) % 2,Nat.mod_lt _ (by decide)⟩ : Fin 2) = b := Fin.ext rem
  rw [matchB]

/-- Encode an initial segment of actual charged gates in their original order.
Every raw atom is the support of a fixed original input port. -/
theorem representOrdered (ao : IsAO2 n C) (top : TopForm G C) (order : List ℕ) (both : Bool)
    (out : (Fin n → Bool) → Prop) (active : ∀ g ∈ order, g ∈ activeGates G C)
    (closed : ∀ g ∈ order, ∀ h ∈ activeGates G C, h < g → h ∈ order)
    (sorted : order.Pairwise (· < ·))
    (done : ThreeMatching.finished (fun h x => gateVal n C h x = true) (promotedKeys G C order) both out) :
    ∃ f ∈ outcomes (order.map (gateKind G C)) 0 [] [] both,
      ∀ x, holds f (fun j => ∃ v ∈ rawAt G C order j, x v = true) ↔ out x := by
  classical
  let atom (j : ℕ) (x : Fin n → Bool) := ∃ v ∈ rawAt G C order j, x v = true
  let signal (g : ℕ) (x : Fin n → Bool) := gateVal n C g x = true
  let label (g : ℕ) := (g,gateKind G C g)
  have trace (rest : List ℕ) : ∀ priorGates : List ℕ, order = priorGates++rest →
      follows atom signal both out (rest.map label) priorGates.length (directKeys G C priorGates) (promotedKeys G C priorGates) := by
    induction rest with
    | nil =>
      intro priorGates eq
      have same : order = priorGates := by simpa using eq
      simpa [follows,same,signal] using done
    | cons g tail ih =>
      intro priorGates eq
      have memg : g ∈ order := by simp [eq]
      have hg := active g memg
      have earlier {h : ℕ} (hh : h ∈ activeGates G C) (less : h < g) : h ∈ priorGates := by
        have all := closed g memg h hh less
        rw [eq] at all
        rcases List.mem_append.mp all with left | right
        · exact left
        · rcases List.mem_cons.mp right with same | after
          · omega
          · have tailOrder : (g::tail).Pairwise (· < ·) := (List.pairwise_append.mp (eq ▸ sorted)).2.1
            have gt := (List.pairwise_cons.mp tailOrder).1 _ after
            omega
      let operand (b : Fin 2) (x : Fin n → Bool) := val C (List.ofFn x) (opnd C g (orderedPort G C g b)) = true
      have encoded (b : Fin 2) : PortLaw atom signal (portMode (gateKind G C g) b) (2*priorGates.length+b.val)
            (directKeys G C priorGates) (promotedKeys G C priorGates) (operand b) := by
        have fits := portEligibility ao hg b
        refine actualPortLaw ao top hg (orderedPort G C g b) _ _ atom _ _ ?_ fits.1 fits.2 ?_ ?_
        · intro x
          simp only [atom,eq,rawAtCurrent]
          rfl
        · intro h hh less kind
          simp [promotedKeys,earlier hh less,kind]
        · intro h hh less kind
          simp [directKeys,earlier hh less,kind]
      have dnext : directKeys G C (priorGates++[g]) =
          ThreeMatching.rememberDirect (gateKind G C g) g (directKeys G C priorGates) := by
        cases kind : gateKind G C g <;> simp [directKeys,List.reverse_append,ThreeMatching.rememberDirect,kind]
      have pnext : promotedKeys G C (priorGates++[g]) =
          ThreeMatching.rememberPromoted (gateKind G C g) g (promotedKeys G C priorGates) := by
        cases kind : gateKind G C g <;> simp [promotedKeys,List.reverse_append,ThreeMatching.rememberPromoted,kind]
      have step := ih (priorGates++[g]) (by simpa [List.append_assoc] using eq)
      refine ⟨operand 0,operand 1,?_,?_,?_,?_⟩
      · simpa [portMode] using encoded 0
      · simpa [portMode] using encoded 1
      · exact stageMeaning ao hg
      · simpa [dnext,pnext] using step
  have initial := trace order [] (by simp)
  have d0 : known atom signal [] [] := by simp [known]
  obtain ⟨f,hit,rep⟩ := followsHasOutput (order.map label) 0 [] [] [] [] d0 d0 (by
    simpa [directKeys,promotedKeys] using initial)
  exact ⟨f,by simpa [label,Function.comp_def] using hit,rep⟩

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open ThreeMatching
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem listBound {V : Type*} [DecidableEq V] (xs : List V) (D : Finset V)
    (distinct : xs.Nodup) (inside : ∀ x ∈ xs, x ∈ D) : xs.length ≤ D.card := by
  have sub : xs.toFinset ⊆ D := fun x hx => inside _ (List.mem_toFinset.mp hx)
  rw [← List.toFinset_card_of_nodup distinct]
  exact Finset.card_le_card sub

private theorem counts (xs : List Nat) (tag : Nat → ThreeMatching.Kind) :
    (xs.map tag).count Kind.andGate = (xs.filter (fun g => decide (tag g = .andGate))).length ∧
    (xs.map tag).count Kind.emptyOr + (xs.map tag).count Kind.nonemptyOr =
      (xs.filter (fun g => decide (tag g ≠ .andGate))).length ∧
    xs.length = (xs.map tag).count Kind.andGate + (xs.map tag).count Kind.emptyOr +
      (xs.map tag).count Kind.nonemptyOr := by
  induction xs with
  | nil => simp
  | cons g rest ih =>
    obtain ⟨left,right,all⟩ := ih
    cases h : tag g <;> simp [h] at right ⊢ <;> omega

/-- A selection of nonempty exceptional outputs below AND operands in a
three-dirty-AND, two-exceptional-OR circuit has a positive CNF of at most
six clauses. Each atom is a fixed disjunction of original input variables. -/
theorem selectedSix (ao : IsAO2 n C) (top : TopForm G C) (selected : Finset ℕ)
    (present : selected.Nonempty) (dirtyLimit : (junk G C).card ≤ 3)
    (orLimit : (orN G C \ lam G C).card ≤ 2)
    (used : ∀ h ∈ selected, h ∈ orN G C \ lam G C ∧ (orIn n C (n+h)).Nonempty ∧ liesUnderAnd n C h) :
    ∃ raw : Nat → Set (Fin n), ∃ f : CNF, f.length ≤ 6 ∧
      ∀ x, holds f (fun j => ∃ v ∈ raw j, x v = true) ↔ ∃ g ∈ selected, gateVal n C g x = true := by
  classical
  let m := selected.max' present
  have hm : m ∈ selected := Finset.max'_mem selected present
  have promoted {h : ℕ} (hh : h ∈ selected) : gateKind G C h = .nonemptyOr := by
    obtain ⟨ex,raw,_⟩ := used h hh
    simp [gateKind,exceptionNotJunk ex,raw]
  have activeSelected {h : ℕ} (hh : h ∈ selected) : h ∈ activeGates G C := by
    obtain ⟨ex,_,under⟩ := used h hh
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ex,under⟩)
  let early := (List.range m).filter (fun g => decide (g ∈ activeGates G C))
  let order := early++[m]
  have earlyMem (g : ℕ) : g ∈ early ↔ g < m ∧ g ∈ activeGates G C := by simp [early]
  have inOrder (g : ℕ) : g ∈ order ↔ g ∈ early ∨ g = m := by simp [order]
  have inActive (g : ℕ) (hg : g ∈ order) : g ∈ activeGates G C := by
    rcases (inOrder g).mp hg with e | rfl
    · exact ((earlyMem g).mp e).2
    · exact activeSelected hm
  have down (g : ℕ) (hg : g ∈ order) (h : ℕ) (hh : h ∈ activeGates G C) (lt : h < g) : h ∈ order := by
    apply (inOrder h).mpr
    left
    apply (earlyMem h).mpr
    rcases (inOrder g).mp hg with e | rfl
    · exact ⟨lt.trans ((earlyMem g).mp e).1,hh⟩
    · exact ⟨lt,hh⟩
  have sorted : order.Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨List.Pairwise.filter _ List.pairwise_lt_range,by simp,?_⟩
    intro u hu v hv
    have eq : v = m := by simpa using hv
    simpa [eq] using ((earlyMem u).mp hu).1
  have nodup : order.Nodup := sorted.imp Nat.ne_of_lt
  let tags := order.map (gateKind G C)
  have realAnd {g : ℕ} (member : g ∈ order) : gateKind G C g = .andGate ↔ g ∈ junk G C := by
    by_cases j : g ∈ junk G C
    · simp [gateKind,j]
    · rcases Finset.mem_union.mp (inActive g member) with impossible | ex
      · exact (j impossible).elim
      · by_cases raw : (orIn n C (n+g)).Nonempty <;> simp [gateKind,j,raw]
  have cts := counts order (gateKind G C)
  have ands : tags.count Kind.andGate ≤ 3 := by
    change (order.map (gateKind G C)).count Kind.andGate ≤ 3
    rw [cts.1]
    apply (listBound _ (junk G C) (nodup.filter _ ) ?_).trans dirtyLimit
    intro g h
    obtain ⟨member,k⟩ := List.mem_filter.mp h
    exact (realAnd member).mp (of_decide_eq_true k)
  have ors : tags.count Kind.emptyOr + tags.count Kind.nonemptyOr ≤ 2 := by
    change (order.map (gateKind G C)).count Kind.emptyOr + (order.map (gateKind G C)).count Kind.nonemptyOr ≤ 2
    rw [cts.2.1]
    apply (listBound _ (orN G C \ lam G C) (nodup.filter _ ) ?_).trans orLimit
    intro g h
    obtain ⟨member,k⟩ := List.mem_filter.mp h
    have different := of_decide_eq_true k
    rcases Finset.mem_union.mp (inActive g member) with j | ex
    · exact (different ((realAnd member).mpr j)).elim
    · exact (Finset.mem_filter.mp ex).1
  have len : tags.length ≤ 5 := by
    have count : order.length = tags.count Kind.andGate + tags.count Kind.emptyOr +
        tags.count Kind.nonemptyOr := cts.2.2
    change (order.map (gateKind G C)).length ≤ 5
    rw [List.length_map]
    omega
  have tagM := promoted hm
  have last : tags.getLast? = some Kind.nonemptyOr := by simp [tags,order,tagM]
  have head : promotedKeys G C order = m :: promotedKeys G C early := by
    simp [promotedKeys,order,List.reverse_append,tagM]
  let signal (g : ℕ) (x : Fin n → Bool) := gateVal n C g x = true
  let out (x : Fin n → Bool) := ∃ g ∈ selected, signal g x
  have intent : ∃ both : Bool, ThreeMatching.finished signal (promotedKeys G C order) both out := by
    rw [head]
    by_cases extra : ∃ h ∈ selected, h ≠ m
    · obtain ⟨h,hh,ne⟩ := extra
      have topBound : h ≤ m := Finset.le_max' _ _ hh
      have old : h ∈ promotedKeys G C early := by
        have entry := (earlyMem h).mpr ⟨by omega,activeSelected hh⟩
        simp [promotedKeys,entry,promoted hh]
      have num : selected.card ≤ 2 :=
        (Finset.card_le_card (show selected ⊆ orN G C \ lam G C from fun i hi => (used i hi).1)).trans orLimit
      have erased : (selected.erase m).card ≤ 1 := by
        have := Finset.card_erase_add_one hm
        omega
      refine ⟨true,h,old,?_⟩
      intro x
      constructor
      · rintro ⟨q,hq,hx⟩
        by_cases same : q = m
        · exact Or.inl (same ▸ hx)
        · have other := Finset.card_le_one.mp erased q (Finset.mem_erase.mpr ⟨same,hq⟩)
              h (Finset.mem_erase.mpr ⟨ne,hh⟩)
          exact Or.inr (other ▸ hx)
      · rintro (h₁ | h₂)
        · exact ⟨m,hm,h₁⟩
        · exact ⟨h,hh,h₂⟩
    · refine ⟨false,?_⟩
      intro x
      constructor
      · rintro ⟨g,hg,fire⟩
        have eq : g = m := by by_contra ne; exact extra ⟨g,hg,ne⟩
        exact eq ▸ fire
      · exact fun fire => ⟨m,hm,fire⟩
  obtain ⟨both,done⟩ := intent
  obtain ⟨f,chosen,rep⟩ := representOrdered ao top order both out inActive down sorted done
  exact ⟨rawAt G C order,f,sixClauses tags both len last ands ors chosen,rep⟩

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The numerical hypotheses of the four-triple problem leave exactly three
dirty ANDs and two exceptional ORs, once the one-source estimates are applied. -/
theorem criticalBudget (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (residual : (Ustar G C).card = 3)
    (dirty : 3 ≤ (junk G C).card)
    (fourTops : 4 ≤ (tops G C \ centreless G C).card)
    (budget : (tops G C \ centreless G C).card +
      (2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) ≤ 9)
    (someSource : (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty) :
    centreless G C = ∅ ∧ (tops G C).card = 4 ∧ (junk G C).card = 3 ∧
      (orN G C \ lam G C).card = 2 := by
  have u : (Ustar G C).Nonempty := Finset.card_pos.mp (by omega)
  by_cases has : (centreless G C).Nonempty
  · have pos := Finset.card_pos.mpr has
    have hc : (centreless G C).card = 1 := by omega
    have none : orN G C \ lam G C = ∅ := Finset.card_eq_zero.mp (by omega)
    have j : (junk G C).card = 3 := by omega
    have cost := oneCentreClauseBound four least top u hc none
    rw [residual,j] at cost
    omega
  have empty : centreless G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp has
  have op := Finset.card_pos.mpr (someSource.resolve_left has)
  by_cases one : (orN G C \ lam G C).card = 1
  · have cost := oneMixingExponential four least top u empty one
    rw [residual] at cost
    omega
  simp [empty] at fourTops budget
  exact ⟨empty,by omega,by omega,by omega⟩

end PEqualNP.Outside.L_meta_7465_aux

namespace PEqualNP.Outside.L_meta_7465_aux.Critical5857

open PEqualNP.Outside.L_meta_7465_aux.ThreeMatching
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_7465_aux.Routing

private theorem contradictionOnRows (k : Fin 4) (C : Circuit) (least : IsLeastAO G11 C)
    (top : TopForm G11 C) (empty : centreless G11 C = ∅) (size : (tops G11 C).card = 4)
    (edges : Ustar G11 C = removed k) (dirty : (junk G11 C).card ≤ 3)
    (exception : (orN G11 C \ lam G11 C).card ≤ 2) : False := by
  classical
  obtain ⟨S,form,positive,negative⟩ := criticalSelected k C least empty size edges
  have present : S.Nonempty := by
    obtain ⟨g,hg,_⟩ := positive 0
    exact ⟨g,hg⟩
  have selectedForm (g : ℕ) (hg : g ∈ S) :
      g ∈ orN G11 C \ lam G11 C ∧ (orIn 11 C (11+g)).Nonempty ∧ liesUnderAnd 11 C g := by
    obtain ⟨ex,raw,a,ha,b,route⟩ := form g hg
    exact ⟨ex,raw,a,(topData ha).1,(topData ha).2.1,b,route⟩
  obtain ⟨raw,f,upper,representation⟩ := selectedSix least.1 top S present dirty exception selectedForm
  let ends (i : Fin 3) (b : Bool) := if b then (pair k i).2 else (pair k i).1
  let negatives (bits : Fin 3 → Bool) : Set (Fin 11) := ↑(other k bits)
  have contained (bits : Fin 3 → Bool) (i : Fin 3) : ends i (bits i) ∈ negatives bits :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have pos (i : Fin 3) : holds f (fun j => ends i false ∈ raw j ∨ ends i true ∈ raw j) := by
    have yes := (representation (pairInput (pair k i).1 (pair k i).2)).mpr (positive i)
    have base (j : ℕ) : (∃ v ∈ raw j, pairInput (pair k i).1 (pair k i).2 v = true) ↔
        ends i false ∈ raw j ∨ ends i true ∈ raw j := by
      constructor
      · rintro ⟨w,hw,hx⟩
        rcases (pairInput_true _ _ _).mp hx with rfl | rfl
        · exact Or.inl hw
        · exact Or.inr hw
      · rintro (a | b)
        · exact ⟨_,a,pairInput_left _ _⟩
        · exact ⟨_,b,pairInput_right _ _⟩
    have eq := funext (fun j => propext (base j))
    rwa [eq] at yes
  have neg (bits : Fin 3 → Bool) : ¬ holds f (fun a => ∃ v ∈ raw a, v ∈ negatives bits) := by
    intro good
    let assignment (v : Fin 11) := decide (v ∈ other k bits)
    have hit : holds f (fun a => ∃ v ∈ raw a, assignment v = true) := by
      simpa [assignment,negatives] using good
    obtain ⟨g,hg,on⟩ := (representation assignment).mp hit
    exact Bool.false_ne_true ((negative bits g hg).symm.trans on)
  have lower := substitutionLower f raw ends negatives contained pos neg
  have eight : 8 ≤ f.length := by simpa using lower
  omega

theorem criticalGoal (C : Circuit) (least : IsLeastAO G11 C) (top : TopForm G11 C)
    (dirty : 3 ≤ (junk G11 C).card)
    (listed : Ustar G11 C ∈
      [{s((0 : Fin 11),9),s((1 : Fin 11),4),s((3 : Fin 11),6)},
       {s((1 : Fin 11),4),s((2 : Fin 11),5),s((6 : Fin 11),7)},
       {s((1 : Fin 11),4),s((2 : Fin 11),5),s((3 : Fin 11),7)},
       {s((1 : Fin 11),4),s((2 : Fin 11),5),s((3 : Fin 11),6)}])
    (fourTops : 4 ≤ (tops G11 C \ centreless G11 C).card)
    (budget : (tops G11 C \ centreless G11 C).card +
      (2*(centreless G11 C).card + (junk G11 C).card + (orN G11 C \ lam G11 C).card) ≤ 9)
    (source : (centreless G11 C).Nonempty ∨ (orN G11 C \ lam G11 C).Nonempty) : False := by
  have choice : ∃ k : Fin 4, Ustar G11 C = removed k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with a | b | c | d
    · exact ⟨0,a.trans (by decide +kernel)⟩
    · exact ⟨3,b.trans (by decide +kernel)⟩
    · exact ⟨2,c.trans (by decide +kernel)⟩
    · exact ⟨1,d.trans (by decide +kernel)⟩
  obtain ⟨k,hk⟩ := choice
  have removedThree : ∀ j : Fin 4, (removed j).card = 3 := by decide +kernel
  have num : (Ustar G11 C).card = 3 := by rw [hk,removedThree]
  obtain ⟨empty,nTops,nDirty,nOr⟩ := criticalBudget criticalFourCycle least top num dirty fourTops budget source
  exact contradictionOnRows k C least top empty nTops hk nDirty.le nOr.le

end PEqualNP.Outside.L_meta_7465_aux.Critical5857

theorem PEqualNP.Outside.L_meta_7465 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x6 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;       have x7 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ x6).card;       have x8 : ℕ := (2 : ℕ) * x6.card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;       x2.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → x5 ∈ [{s((0 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ)))}, {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), s((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))}, {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))}, {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ)))}] → (4 : ℕ) ≤ x7 → x7 + x8 ≤ (9 : ℕ) → x6.Nonempty ∨ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty → False := by
  dsimp only
  intro C least top small dirty listed fourTops budget source
  exact PEqualNP.Outside.L_meta_7465_aux.Critical5857.criticalGoal C least top dirty listed fourTops budget source
