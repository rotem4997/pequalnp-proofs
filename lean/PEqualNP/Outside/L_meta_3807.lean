import PEqualNP.Defs

-- The wire evaluation, OR reachability, cone, and four-cycle lemmas in GateRules
-- are adapted from the project's checked file L_meta_1878. The following bridge
-- uses them to read the two raw OR supports of each dirty gate in an antichain.

namespace PEqualNP.Outside.L_meta_3807.GateRules

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

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

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership

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

open PEqualNP.CleanedNonEdge

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

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

lemma fin2_cases : ∀ (i b : Fin 2), b = i ∨ b = 1 - i := by decide


end PEqualNP.Outside.L_meta_3807.GateRules

namespace PEqualNP.Outside.L_meta_3807.Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3807.GateRules

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem input_iff_operand {a w : ℕ} (hAO : IsAO2 n C) (ha : a < C.gates.length) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  have hlen := hAO.2.2 _ (gateAt_mem ha)
  constructor
  · intro hw
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
    refine ⟨⟨i, hlen ▸ hi⟩, ?_⟩
    exact (List.getD_eq_getElem _ 0 hi).trans he
  · rintro ⟨b, rfl⟩
    have hb : (b : ℕ) < (gateAt C a).inputs.length := hlen.symm ▸ b.isLt
    rw [opnd, List.getD_eq_getElem _ 0 hb]
    exact List.getElem_mem _

theorem and_true_iff_operands {a : ℕ} (hAO : IsAO2 n C) (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      ∀ b : Fin 2, wireVal n C (opnd C a b) x = true := by
  change val C (List.ofFn x) (n + a) = true ↔ _
  rw [val_and (n := n) (by simp) ha hand]
  constructor
  · intro h b
    exact (h _ ((input_iff_operand hAO ha).mpr ⟨b, rfl⟩)).2
  · intro h w hw
    obtain ⟨b, rfl⟩ := (input_iff_operand hAO ha).mp hw
    exact ⟨hAO.2.1 a ha _ hw, h b⟩

theorem operand_true_iff {a : ℕ} (hAO : IsAO2 n C) (hTop : TopForm G C)
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C a b) x = true ↔
      (∃ v ∈ side C a b, x v = true) ∨
      ∃ j < a, j ∈ junk G C ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j x = true := by
  have hin := (input_iff_operand hAO ha).mpr (⟨b, rfl⟩ : ∃ i : Fin 2, opnd C a i = opnd C a b)
  have hlt := hAO.2.1 a ha _ hin
  constructor
  · intro hw
    obtain ⟨w, path, hv, last⟩ := or_trace (n := n) (C := C) (x := List.ofFn x)
      (by simp) (opnd C a b) hw
    rcases last with hraw | ⟨j, hj, rfl, hnotor⟩
    · let u : Fin n := ⟨w, hraw⟩
      exact Or.inl ⟨u, reach_mem_orIn u path, (val_ofFn C x u).symm.trans hv⟩
    · have hop : (gateAt C j).op = GateOp.and := (hAO.1 _ (gateAt_mem hj)).resolve_right hnotor
      have hcone := operand_cone ha hin hlt path
      have hbelow : ¬ BelowF G C j := fun h => hTop j hj a ha hop h hand hcone
      have hex : ∃ z, gateVal n C j z = true ∧ graphFun G ∅ z = false := by
        by_contra hn
        apply hbelow
        intro z hz
        by_contra hfalse
        exact hn ⟨z, hz, Bool.eq_false_iff.mpr hfalse⟩
      have hjunk : j ∈ junk G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hj, hex⟩
      have hle := orStep_le path
      exact Or.inr ⟨j, by omega, hjunk, reach_orReaches path j rfl hj, hv⟩
  · rintro (⟨v, hv, hx⟩ | ⟨j, _, _, hr, hx⟩)
    · exact reach_var_val x _ v (mem_orIn_reach v hv) hx
    · exact orStep_up (n := n) (x := List.ofFn x) (by simp) (orReaches_reach j _ hr).1 hx


end PEqualNP.Outside.L_meta_3807.Bridge

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules


variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev Reach (n : ℕ) (C : Circuit) := Relation.ReflTransGen (OrStep n C)
def ParallelJunk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ g ∈ junk G C, ∀ h ∈ junk G C, ¬InCone n C g h

def Hits (S : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ v ∈ S, x v = true

theorem opt_mem (arch : IsAO2 n C) {g : ℕ} (hg : g<C.gates.length) (b : Fin 2) :
    opnd C g b ∈ (gateAt C g).inputs := (input_iff_operand arch hg).mpr ⟨b,rfl⟩

theorem junk_raw (arch : IsAO2 n C) (top : TopForm G C) (par : ParallelJunk G C)
    {g : ℕ} (hg : g ∈ junk G C) (x : Fin n → Bool) :
    gateVal n C g x = true ↔ ∀ b : Fin 2, Hits (side C g b) x := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨hgi,ha,_⟩ := Finset.mem_filter.mp hg
  have gl := Finset.mem_range.mp hgi
  rw [and_true_iff_operands arch gl ha x]
  constructor
  · intro h b
    rcases (operand_true_iff arch top gl ha b x).mp (h b) with H | ⟨j,_,hj,reach,_⟩
    · exact H
    · have hm := opt_mem arch gl b
      exact (par j hj g hg (operand_cone gl hm (arch.2.1 g gl _ hm) (orReaches_reach j _ reach).1)).elim
  · intro h b
    exact (operand_true_iff arch top gl ha b x).mpr (Or.inl (h b))

theorem bits_of_top (arch : IsAO2 n C) {t : ℕ} (ht : t ∈ tops G C) (x : Fin n → Bool)
    (h : ∀ b : Fin 2, wireVal n C (opnd C t b) x=true) : graphFun G ∅ x=true := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨hlt,hop,below⟩ := Finset.mem_filter.mp ht
  exact below x ((and_true_iff_operands arch (Finset.mem_range.mp hlt) hop x).mpr h)

theorem compatible (arch : IsAO2 n C) {t g h : ℕ} (ht : t ∈ tops G C) (b : Fin 2)
    (left : Reach n C (opnd C t b) (n+g)) (right : Reach n C (opnd C t (1-b)) (n+h))
    (x : Fin n → Bool) (gx : gateVal n C g x=true) (hx : gateVal n C h x=true) :
    graphFun G ∅ x = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply bits_of_top arch ht x
  intro a
  rcases fin2_cases b a with rfl|rfl
  · exact orStep_up (n:=n) (C:=C) (x:=List.ofFn x) (by simp) left gx
  · exact orStep_up (n:=n) (C:=C) (x:=List.ofFn x) (by simp) right hx

theorem rawDown {w z : ℕ} (path : Reach n C w z) : orIn n C z ⊆ orIn n C w := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro u hu
  exact reach_mem_orIn u (path.trans (mem_orIn_reach u hu))

theorem step_decomp (arch : IsAO2 n C) {w z : ℕ} (step : OrStep n C w z) :
    ∃ j<C.gates.length, w=n+j ∧ (gateAt C j).op=GateOp.or ∧
      ∃ b : Fin 2, z=opnd C j b ∧ z<w := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨j,hj,rfl,ho,hm,lt⟩ := step
  obtain ⟨b,hr⟩ := (input_iff_operand arch hj).mp hm
  exact ⟨j,hj,rfl,ho,b,hr.symm,lt⟩

theorem non_or_path {w q : ℕ} (path : Reach n C w q)
    (stop : ∀ j<C.gates.length, w=n+j → (gateAt C j).op ≠ GateOp.or) : w=q := by
  letI : DecidableEq GateOp := gateOpDecEq
  rcases Relation.ReflTransGen.cases_head path with h|⟨z,⟨j,hj,h0,ho,_⟩,_⟩
  · exact h
  · exact (stop j hj h0 ho).elim

theorem rawBranch (arch : IsAO2 n C) {w : ℕ} (wide : 9 < (orIn n C w).card) :
    ∃ j<C.gates.length, w=n+j ∧ ∀ v ∈ orIn n C w, ∃ b : Fin 2,
      v ∈ orIn n C (opnd C j b) ∧ opnd C j b < w ∧ Reach n C w (opnd C j b) := by
  letI : DecidableEq GateOp := gateOpDecEq
  classical
  by_cases ex : ∃ j<C.gates.length, w=n+j ∧ (gateAt C j).op=GateOp.or
  · obtain ⟨j,hj,rfl,ho⟩ := ex
    refine ⟨j,hj,rfl,?_⟩
    intro v hv
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with eq|⟨z,st,path⟩
    · have vlt := v.isLt
      omega
    · obtain ⟨k,hk,ek,_,b,ez,lt⟩ := step_decomp arch st
      have eq : k=j := by omega
      subst k
      subst z
      exact ⟨b,reach_mem_orIn v path,lt,Relation.ReflTransGen.single st⟩
  · have unique (v : Fin n) (hv : v ∈ orIn n C w) : w=v.val :=
      non_or_path (mem_orIn_reach v hv) (fun j hj eq op => ex ⟨j,hj,eq,op⟩)
    have sm : (orIn n C w).card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy => Fin.ext ((unique x hx).symm.trans (unique y hy)))
    omega

def other (b : Fin 2) := 1-b

def Outside (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) (B : Finset (Fin n)) :=
  B.filter (fun x => ¬G.Adj u x)

def Atom (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (b : Fin 2) (u : Fin n) : Prop :=
  g ∈ junk G C ∧ u ∈ side C g b ∧ (side (n:=n) C g b).card ≤ 9 ∧
  (u ∈ side C g (other b) ∨
    (9 < (side (n:=n) C g (other b)).card ∧ 4 < (Outside G u (side C g (other b))).card))

noncomputable def labels (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  by classical exact Finset.univ.filter fun u => ∃ g b, Atom G C g b u ∧ Reach n C w (n+g)

theorem mem_labels {w : ℕ} {u : Fin n} :
    u ∈ labels G C w ↔ ∃ g b, Atom G C g b u ∧ Reach n C w (n+g) := by classical simp [labels]

theorem labelsDown {w z : ℕ} (path : Reach n C w z) : labels G C z ⊆ labels G C w := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro u hu
  obtain ⟨g,b,ha,h⟩ := mem_labels.mp hu
  exact mem_labels.mpr ⟨g,b,ha,path.trans h⟩

theorem other_other (b : Fin 2) : other (other b) = b := by fin_cases b <;> decide

theorem atom_center_mem {g : ℕ} {b c : Fin 2} {u v : Fin n} (a : Atom G C g b u) (h : Atom G C g c v) :
    v ∈ side C g b := by
  letI : DecidableEq GateOp := gateOpDecEq
  rcases fin2_cases b c with rfl | eq
  · exact h.2.1
  · have ec : c = other b := eq
    subst c
    rcases h.2.2.2 with lit | ⟨big,_⟩
    · rwa [show other (1-b) = b from other_other b] at lit
    · rw [show other (1-b) = b from other_other b] at big
      exact (Nat.not_lt_of_ge a.2.2.1 big).elim

theorem labelBranch (arch : IsAO2 n C) {w : ℕ} (wide : 9 < (labels G C w).card) :
    ∃ j<C.gates.length, w=n+j ∧ ∀ v ∈ labels G C w, ∃ b : Fin 2,
      v ∈ labels G C (opnd C j b) ∧ opnd C j b < w ∧ Reach n C w (opnd C j b) := by
  letI : DecidableEq GateOp := gateOpDecEq
  classical
  by_cases ex : ∃ j<C.gates.length, w=n+j ∧ (gateAt C j).op=GateOp.or
  · obtain ⟨j,hj,rfl,ho⟩ := ex
    refine ⟨j,hj,rfl,?_⟩
    intro v hv
    obtain ⟨g,b,atg,hr⟩ := mem_labels.mp hv
    rcases Relation.ReflTransGen.cases_head hr with eq|⟨z,st,path⟩
    · have same : j=g := by omega
      subst g
      have hand := (Finset.mem_filter.mp atg.1).2.1
      simp [ho] at hand
    · obtain ⟨k,hk,ek,_,d,ez,lt⟩ := step_decomp arch st
      have eq : k=j := by omega
      subst k
      subst z
      exact ⟨d,mem_labels.mpr ⟨g,b,atg,path⟩,lt,Relation.ReflTransGen.single st⟩
  · obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0<(labels G C w).card)
    obtain ⟨g,b,atg,hr⟩ := mem_labels.mp hu
    have stop : ∀ j<C.gates.length, w=n+j → (gateAt C j).op≠GateOp.or := fun j hj e q => ex ⟨j,hj,e,q⟩
    have e0 := non_or_path hr stop
    have sub : labels G C w ⊆ side (n:=n) C g b := by
      intro v hv
      obtain ⟨k,d,hk,ht⟩ := mem_labels.mp hv
      have e1 := non_or_path ht stop
      have eq : k=g := by omega
      subst k
      exact atom_center_mem atg hk
    have cr := Finset.card_le_card sub
    have sm := atg.2.2.1
    omega

end PEqualNP.Outside.L_meta_3807.Bridge

-- In a graph of codegree at most one, large sets contain independent
-- representatives, even when the sets overlap.

namespace PEqualNP.Outside.L_meta_3807.Transversal

variable {V : Type*}

theorem two_transversal (G : SimpleGraph V)
    (codeg : ∀ a b : V, a ≠ b → ∀ x y : V,
      G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y)
    (A B : Finset V) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    ∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b := by
  classical
  obtain ⟨a, ha, a', ha', aa'⟩ := Finset.one_lt_card.mp hA
  obtain ⟨b, hb, b', hb', bb'⟩ := Finset.one_lt_card.mp hB
  by_contra missing
  have edge (x) (hx : x ∈ A) (y) (hy : y ∈ B) : G.Adj x y := by
    by_contra nonedge
    exact missing ⟨x, hx, y, hy, nonedge⟩
  exact bb' (codeg a a' aa' b b' (edge _ ha _ hb) (edge _ ha' _ hb)
    (edge _ ha _ hb') (edge _ ha' _ hb'))

theorem three_transversal (G : SimpleGraph V)
    (codeg : ∀ a b : V, a ≠ b → ∀ x y : V,
      G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y)
    (A B C : Finset V) (hA : 5 ≤ A.card) (hB : 5 ≤ B.card) (hC : 5 ≤ C.card) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := two_transversal G codeg A B (by omega) (by omega)
  let D : Finset V := {a, b}
  have sizeD : D.card ≤ 2 := by
    exact (Finset.card_insert_le a {b}).trans (by simp)
  have remaining (S : Finset V) (enough : 5 ≤ S.card) : 2 ≤ (S \ D).card := by
    have lost : S.card ≤ (S \ D).card + D.card := Finset.card_le_card_sdiff_add_card
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := two_transversal G codeg (A \ D) (B \ D)
    (remaining A hA) (remaining B hB)
  obtain ⟨huA, huD⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hvB, hvD⟩ := Finset.mem_sdiff.mp hv
  have outside (w : V) (hw : w ∉ D) : a ≠ w ∧ b ≠ w := by
    constructor
    · rintro rfl
      exact hw (by simp [D])
    · rintro rfl
      exact hw (by simp [D])
  let both (x y : V) := C.filter fun z => G.Adj x z ∧ G.Adj y z
  have small (x y : V) (xy : x ≠ y) : (both x y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz t ht
    obtain ⟨_, hzx, hzy⟩ := Finset.mem_filter.mp hz
    obtain ⟨_, htx, hty⟩ := Finset.mem_filter.mp ht
    exact codeg x y xy z t hzx hzy htx hty
  by_contra missing
  have hits (x) (hx : x ∈ A) (y) (hy : y ∈ B) (xy : ¬ G.Adj x y) (z) (hz : z ∈ C) :
      G.Adj x z ∨ G.Adj y z := by
    by_contra! neither
    exact missing ⟨x, hx, y, hy, z, hz, xy, neither.1, neither.2⟩
  have cover : C ⊆ (both a u ∪ both a v) ∪ (both b u ∪ both b v) := by
    intro z hz
    have first := hits a ha b hb hab z hz
    have second := hits u huA v hvB huv z hz
    simp only [Finset.mem_union, both, Finset.mem_filter]
    tauto
  have four := Finset.card_le_card cover
  have two1 := Finset.card_union_le (both a u) (both a v)
  have two2 := Finset.card_union_le (both b u) (both b v)
  have joined := Finset.card_union_le (both a u ∪ both a v) (both b u ∪ both b v)
  have au := small a u (outside u huD).1
  have av := small a v (outside v hvD).1
  have bu := small b u (outside u huD).2
  have bv := small b v (outside v hvD).2
  omega

end PEqualNP.Outside.L_meta_3807.Transversal

namespace PEqualNP.Outside.L_meta_3807.PairCharge

variable {V : Type*} [DecidableEq V]

def small (S : Finset V) : Finset V := if S.card ≤ 9 then S else ∅

theorem small_card (S : Finset V) : (small S).card ≤ 9 := by
  unfold small
  split <;> simp_all

def boundary (A : Nat → Finset V) (child : Nat → Fin 2 → Nat) (j : Nat) : Finset V :=
  small (A (child j 0)) ∪ small (A (child j 1))

theorem boundary_card (A : Nat → Finset V) (child : Nat → Fin 2 → Nat) (j : Nat) :
    (boundary A child j).card ≤ 18 := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (small_card _) (small_card _))

theorem into_boundary {A : Nat → Finset V} {child : Nat → Fin 2 → Nat}
    {j : Nat} {b : Fin 2} {x : V} (hx : x ∈ A (child j b))
    (h : (A (child j b)).card ≤ 9) : x ∈ boundary A child j := by
  have hsmall : x ∈ small (A (child j b)) := by rw [small,if_pos h]; exact hx
  fin_cases b
  · exact Finset.mem_union_left _ hsmall
  · exact Finset.mem_union_right _ hsmall

def rect (S P : Finset V) : Finset (Sym2 V) :=
  (S ×ˢ P).image fun p => s(p.1,p.2)

theorem into_rect {S P : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ P) :
    s(x,y) ∈ rect S P := Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩

theorem rect_card (S P : Finset V) : (rect S P).card ≤ S.card * P.card := by
  unfold rect
  simpa only [Finset.card_product] using
    (Finset.card_image_le (s:=S ×ˢ P) (f:=fun (p : V × V) => s(p.1,p.2)))

theorem family_card {I W : Type*} [DecidableEq W] (t : Finset I) (F : I → Finset W)
    (k : Nat) (limits : ∀ i ∈ t, (F i).card ≤ k) : (t.biUnion F).card ≤ k * t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hi,Nat.mul_succ]
    have hi' := limits i (Finset.mem_insert_self _ _)
    have ht := ih (fun u hu => limits u (Finset.mem_insert_of_mem hu))
    exact (Finset.card_union_le _ _).trans (by omega)

def Steps (n m : Nat) (A : Nat → Finset V) (child : Nat → Fin 2 → Nat)
    (reach : Nat → Nat → Prop) : Prop :=
  ∀ w, w < n+m → 9 < (A w).card → ∃ j < m, w=n+j ∧
    ∀ x ∈ A w, ∃ b, x ∈ A (child j b) ∧ child j b < w ∧ reach w (child j b)

theorem frontier {n m : Nat} {A : Nat → Finset V} {child : Nat → Fin 2 → Nat}
    {reach : Nat → Nat → Prop} (rr : ∀ w, reach w w)
    (rt : ∀ {i j k}, reach i j → reach j k → reach i k)
    (steps : Steps n m A child reach) (w : Nat) (hw : w<n+m) (big : 9<(A w).card)
    {x : V} (hx : x∈A w) : ∃ j<m, reach w (n+j) ∧ 9<(A (n+j)).card ∧ x∈boundary A child j := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    obtain ⟨j,hj,eq,desc⟩ := steps w hw big
    obtain ⟨b,hb,lt,r⟩ := desc x hx
    by_cases sm : (A (child j b)).card ≤ 9
    · exact ⟨j,hj,eq ▸ rr w,eq ▸ big,into_boundary hb sm⟩
    · obtain ⟨k,hk,rk,large,mem⟩ := ih _ lt (lt_trans lt hw) (by omega) hb
      exact ⟨k,hk,rt r rk,large,mem⟩

def largeEdges (n m : Nat) (A : Nat → Finset V) (child : Nat → Fin 2 → Nat)
    (partner : Nat → Finset V) : Finset (Sym2 V) :=
  (Finset.range m).biUnion fun j => if 9<(A (n+j)).card then
    rect (boundary A child j) (partner (n+j)) else ∅

theorem frontierBudget (n m k : Nat) (A : Nat → Finset V) (child : Nat → Fin 2 → Nat)
    (partner : Nat → Finset V)
    (hp : ∀ j<m, 9<(A (n+j)).card → (partner (n+j)).card ≤ k) :
    (largeEdges n m A child partner).card ≤ (18*k)*m := by
  unfold largeEdges
  calc
    _ ≤ (18*k)*(Finset.range m).card := by
      apply family_card
      intro j hj
      split
      next big =>
        exact (rect_card _ _).trans (Nat.mul_le_mul (boundary_card ..) (hp j (Finset.mem_range.mp hj) big))
      next => simp
    _ = _ := by rw [Finset.card_range]

theorem into_largeEdges {n m : Nat} {A : Nat → Finset V} {child : Nat → Fin 2 → Nat}
    {partner : Nat → Finset V} {j : Nat} (hj : j<m) (big : 9<(A (n+j)).card)
    {x y : V} (hx : x∈boundary A child j) (hy : y∈partner (n+j)) :
    s(x,y) ∈ largeEdges n m A child partner := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j,Finset.mem_range.mpr hj,by simpa only [if_pos big] using into_rect hx hy⟩

def smallEdges (T : Finset Nat) (root : Nat → Fin 2 → Nat) (A : Nat → Finset V) :
    Finset (Sym2 V) := T.biUnion fun t => rect (small (A (root t 0))) (small (A (root t 1)))

theorem bound (n m : Nat) (A : Nat → Finset V) (child root : Nat → Fin 2 → Nat)
    (T : Finset Nat) (E : Finset (Sym2 V)) (reach : Nat → Nat → Prop)
    (partner : Nat → Finset V)
    (rr : ∀ w, reach w w) (rt : ∀ {i j k}, reach i j → reach j k → reach i k)
    (steps : Steps n m A child reach) (hT : T⊆Finset.range m)
    (hroot : ∀ t∈T, ∀ b, root t b < n+m)
    (hp : ∀ j<m, 9<(A (n+j)).card → (partner (n+j)).card ≤ 6)
    (opp : ∀ t∈T, ∀ b : Fin 2, ∀ w, reach (root t b) w → 9<(A w).card →
      A (root t (1-b)) ⊆ partner w)
    (cover : ∀ e∈E, ∃ t∈T, ∃ x∈A (root t 0), ∃ y∈A (root t 1), e=s(x,y)) :
    E.card ≤ 189 * m := by
  classical
  have hL := frontierBudget n m 6 A child partner hp
  have hS : (smallEdges T root A).card ≤ 81 * T.card := by
    apply family_card
    intro t ht
    exact (rect_card _ _).trans (Nat.mul_le_mul (small_card _) (small_card _))
  have subset : E ⊆ largeEdges n m A child partner ∪ smallEdges T root A := by
    intro e he
    obtain ⟨t,ht,x,hx,y,hy,rfl⟩ := cover e he
    by_cases h0 : 9 < (A (root t 0)).card
    · obtain ⟨j,hj,r,large,mem⟩ := frontier rr rt steps _ (hroot t ht 0) h0 hx
      exact Finset.mem_union_left _ (into_largeEdges hj large mem (opp t ht 0 _ r large (by simpa using hy)))
    by_cases h1 : 9 < (A (root t 1)).card
    · obtain ⟨j,hj,r,large,mem⟩ := frontier rr rt steps _ (hroot t ht 1) h1 hy
      have hxy := into_largeEdges hj large mem (opp t ht 1 _ r large (by simpa using hx))
      rw [Sym2.eq_swap]
      exact Finset.mem_union_left _ hxy
    · apply Finset.mem_union_right _
      apply Finset.mem_biUnion.mpr
      exact ⟨t,ht,into_rect (by simpa [small, Nat.le_of_not_gt h0] using hx)
        (by simpa [small, Nat.le_of_not_gt h1] using hy)⟩
  have hcard := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
  have htm : T.card ≤ m := by simpa using Finset.card_le_card hT
  omega

end PEqualNP.Outside.L_meta_3807.PairCharge

namespace PEqualNP.Outside.L_meta_3807.PairCharge

variable {V : Type*} [DecidableEq V]

theorem heavyUnique {S N M : Finset V} (big : 9 < S.card)
    (left : (S \ N).card ≤ 4) (right : (S \ M).card ≤ 4)
    (common : (N∩M).card ≤ 1) : False := by
  have sub : S ⊆ ((S \ N) ∪ (S \ M)) ∪ (N ∩ M) := by
    intro x hx
    by_cases a : x∈N <;> by_cases b : x∈M <;> simp_all
  have p := Finset.card_le_card sub
  have q := Finset.card_union_le (S \ N) (S \ M)
  have r := Finset.card_union_le ((S \ N) ∪ (S \ M)) (N∩M)
  omega

theorem threeCenters {P : Finset V} {N : V → Finset V} {a b c : V}
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (codeg : ∀ x y : V, x≠y → (N x ∩ N y).card ≤ 1)
    (Ea Eb Ec : Finset V) (ha : Ea.card≤1) (hb : Eb.card≤1) (hc : Ec.card≤1)
    (compatible : ∀ y∈P, ∃ Y : Finset V, Y.card≤1 ∧
      (y∈N a ∨ y∈Ea ∨ a∈Y) ∧ (y∈N b ∨ y∈Eb ∨ b∈Y) ∧ (y∈N c ∨ y∈Ec ∨ c∈Y)) :
    P.card ≤ 6 := by
  classical
  let F := (Ea ∪ Eb) ∪ Ec
  let K := ((N a ∩ N b) ∪ (N a ∩ N c)) ∪ (N b ∩ N c)
  have sub : P ⊆ F ∪ K := by
    intro y hy
    obtain ⟨Y,one,h1,h2,h3⟩ := compatible y hy
    have uq := Finset.card_le_one.mp one
    have dab : ¬(a∈Y ∧ b∈Y) := fun h => ab (uq a h.1 b h.2)
    have dac : ¬(a∈Y ∧ c∈Y) := fun h => ac (uq a h.1 c h.2)
    have dbc : ¬(b∈Y ∧ c∈Y) := fun h => bc (uq b h.1 c h.2)
    simp only [F,K,Finset.mem_union,Finset.mem_inter]
    tauto
  have f1 := Finset.card_union_le Ea Eb
  have f2 := Finset.card_union_le (Ea ∪ Eb) Ec
  have k1 := Finset.card_union_le (N a ∩ N b) (N a ∩ N c)
  have k2 := Finset.card_union_le ((N a ∩ N b) ∪ (N a ∩ N c)) (N b ∩ N c)
  have t := (Finset.card_le_card sub).trans (Finset.card_union_le F K)
  have c1 := codeg a b ab
  have c2 := codeg a c ac
  have c3 := codeg b c bc
  dsimp only [F,K] at t
  omega

end PEqualNP.Outside.L_meta_3807.PairCharge

namespace PEqualNP.Outside.L_meta_3807.PairCharge

variable {V : Type*} [DecidableEq V]

theorem sameLight {m : Nat} (S : Nat → Fin 2 → Finset V) (E : Finset (Sym2 V))
    (cover : ∀ e∈E, ∃ j<m, ∃ x∈small (S j 0), ∃ y∈small (S j 1), e=s(x,y)) :
    E.card ≤ 81*m := by
  let R := fun j => rect (small (S j 0)) (small (S j 1))
  have sub : E ⊆ (Finset.range m).biUnion R := by
    intro e he
    obtain ⟨j,hj,x,hx,y,hy,rfl⟩ := cover e he
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hj,into_rect hx hy⟩
  have lim : ∀ j∈Finset.range m, (R j).card≤81 := by
    intro j hj
    exact (rect_card _ _).trans (Nat.mul_le_mul (small_card _) (small_card _))
  simpa only [Finset.card_range] using (Finset.card_le_card sub).trans (family_card _ R 81 lim)

theorem sameLightAny {m : Nat} (S : Nat → Fin 2 → Finset V) (E : Finset (Sym2 V))
    (cover : ∀ e∈E, ∃ j<m, ∃ a b : Fin 2, ∃ x∈small (S j a), ∃ y∈small (S j b), e=s(x,y)) :
    E.card ≤ 324*m := by
  let U := fun j => small (S j 0) ∪ small (S j 1)
  have inc (j : Nat) (b : Fin 2) : small (S j b) ⊆ U j := by
    fin_cases b
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have uc (j : Nat) : (U j).card≤18 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (small_card _) (small_card _))
  let R := fun j => rect (U j) (U j)
  have sub : E ⊆ (Finset.range m).biUnion R := by
    intro e he
    obtain ⟨j,hj,a,b,x,hx,y,hy,rfl⟩ := cover e he
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hj,into_rect (inc j a hx) (inc j b hy)⟩
  have lim : ∀ j∈Finset.range m, (R j).card≤324 := by
    intro j hj
    exact (rect_card _ _).trans (Nat.mul_le_mul (uc j) (uc j))
  simpa only [Finset.card_range] using (Finset.card_le_card sub).trans (family_card _ R 324 lim)

end PEqualNP.Outside.L_meta_3807.PairCharge

namespace PEqualNP.Outside.L_meta_3807.PairCharge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem heavyBound {n m : Nat} (A : Nat → Finset V) (child : Nat → Fin 2 → Nat)
    (reach : Nat → Nat → Prop) (N : V → Finset V) (E : Finset (Sym2 V))
    (rr : ∀ w, reach w w) (rt : ∀ {i j k}, reach i j → reach j k → reach i k)
    (mono : ∀ {w v}, reach w v → A v ⊆ A w)
    (steps : Steps n m A child reach)
    (codeg : ∀ u v : V, u≠v → (N u ∩ N v).card≤1)
    (cover : ∀ e∈E, ∃ u v w, e=s(u,v) ∧ w<n+m ∧ 9<(A w).card ∧
      (A w \ N u).card≤4 ∧ v∈A w) : E.card ≤ 18*m := by
  classical
  let P (w : Nat) : Finset V := Finset.univ.filter fun u => (A w \ N u).card ≤ 4
  have hp : ∀ j<m, 9<(A (n+j)).card → (P (n+j)).card ≤ 1 := by
    intro j hj big
    apply Finset.card_le_one.mpr
    intro u hu v hv
    by_contra neq
    exact heavyUnique big (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 (codeg u v neq)
  have sub : E ⊆ largeEdges n m A child P := by
    intro e he
    obtain ⟨u,v,w,rfl,hw,big,near,hv⟩ := cover e he
    obtain ⟨j,hj,r,hlarge,hmem⟩ := frontier rr rt steps w hw big hv
    have hn : (A (n+j) \ N u).card ≤ 4 := by
      apply (Finset.card_le_card ?_).trans near
      intro x hx
      obtain ⟨ha,hno⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨mono r ha,hno⟩
    have hu : u∈P (n+j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    rw [Sym2.eq_swap]
    exact into_largeEdges hj hlarge hmem hu
  simpa only [Nat.mul_one] using (Finset.card_le_card sub).trans (frontierBudget n m 1 A child P hp)

end PEqualNP.Outside.L_meta_3807.PairCharge

-- Two dirty gates feeding opposite sides of a clean top give four raw OR
-- clauses. For each endpoint, one clause meets the other endpoint and has
-- at most four vertices outside the first endpoint's neighborhood.

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules
open PEqualNP.Outside.L_meta_3807
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev Codeg (G : SimpleGraph (Fin n)) := ∀ a b : Fin n, a ≠ b → ∀ x y,
    G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y

theorem codeg_of_girth (hg : ∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5≤w.length) : Codeg G := by
  intro a b ab x y ax bx ay by'
  by_contra xy
  exact no4 G hg a x b y ax bx.symm by' ay.symm ab xy

def nbs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) := Finset.univ.filter (G.Adj u)
theorem mem_nbs (u v : Fin n) : v∈nbs G u ↔ G.Adj u v := by simp [nbs]

theorem codeg_card (h4 : Codeg G) (a b : Fin n) (h : a≠b) : ((nbs G a)∩(nbs G b)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [Finset.mem_inter,mem_nbs] at hx hy
  exact h4 a b h x y hx.1 hx.2 hy.1 hy.2

def Occurs (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) := ∃ a ∈ X, ∃ b ∈ X, G.Adj a b

theorem true_on_set (X : Finset (Fin n)) :
    graphFun G ∅ (fun v => decide (v∈X))=true ↔ Occurs G X := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, Occurs]
  tauto

theorem noQuad {u v a b : Fin n} (uv : ¬G.Adj u v) (ua : ¬G.Adj u a) (ub : ¬G.Adj u b)
    (va : ¬G.Adj v a) (vb : ¬G.Adj v b) (ab : ¬G.Adj a b) : ¬Occurs G {u,v,a,b} := by
  rintro ⟨x,hx,y,hy,e⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    first | exact G.irrefl e | exact uv e | exact ua e | exact ub e | exact va e | exact vb e | exact ab e |
      exact uv e.symm | exact ua e.symm | exact ub e.symm | exact va e.symm | exact vb e.symm | exact ab e.symm

theorem noSingleton (u : Fin n) : ¬Occurs G {u} := by
  rintro ⟨x,hx,y,hy,he⟩
  simp only [Finset.mem_singleton] at hx hy
  subst x; subst y; exact G.irrefl he

theorem outside_eq (u : Fin n) (B : Finset (Fin n)) : Outside G u B = B \ nbs G u := by
  ext x; simp [Outside,nbs]

def SafeFour (G : SimpleGraph (Fin n)) (f : Fin 4 → Finset (Fin n)) : Prop :=
  ∀ X : Finset (Fin n), (∀ i, ∃x ∈ f i, x∈X) → Occurs G X

theorem missingSmall {u v : Fin n} (h4 : Codeg G) {f : Fin 4 → Finset (Fin n)} (safe : SafeFour G f)
    (hit : ∀ i, u ∈ f i ∨ v ∈ f i) : ∃j, u ∉ f j ∧ v ∈ f j ∧ (Outside G u (f j)).card ≤ 4 := by
  classical
  obtain ⟨p,hp⟩ : ∃ i, u∈f i := by
    by_contra! h
    apply noSingleton (G:=G) v
    exact safe {v} (fun i => ⟨v,(hit i).resolve_left (h i),by simp⟩)
  obtain ⟨q,hq⟩ : ∃ i, u∉f i := by
    by_contra! h
    exact noSingleton (G:=G) u (safe {u} (fun i => ⟨u,h i,by simp⟩))
  by_contra! h
  have wide (i : Fin 4) (miss : u ∉ f i) : 5 ≤ (Outside G u (f i)).card := h i miss ((hit i).resolve_left miss)
  let F (i : Fin 3) := if u ∈ f (p.succAbove i) then Outside G u (f q) else Outside G u (f (p.succAbove i))
  have all (i : Fin 3) : 5 ≤ (F i).card := by dsimp only [F]; split <;> apply wide <;> assumption
  obtain ⟨a,ha,b,hb,c,hc,ab,ac,bc⟩ := PEqualNP.Outside.L_meta_3807.Transversal.three_transversal G h4 (F 0) (F 1) (F 2) (all 0) (all 1) (all 2)
  let V : Fin 3 → Fin n := ![a,b,c]
  have vm (i : Fin 3) : V i ∈ F i := by fin_cases i <;> first | exact ha | exact hb | exact hc
  have nadj (i : Fin 3) : ¬G.Adj u (V i) := by
    have hh := vm i
    dsimp only [F] at hh
    split at hh <;> exact (Finset.mem_filter.mp hh).2
  apply noQuad (nadj 0) (nadj 1) (nadj 2) ab ac bc
  apply safe {u,a,b,c}
  intro i
  by_cases h0 : u∈f i
  · exact ⟨u,h0,by simp⟩
  · have ine : i≠p := fun eq => h0 (eq ▸ hp)
    obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq ine
    have hm := vm j
    simp only [F,if_neg h0,Outside,Finset.mem_filter] at hm
    refine ⟨V j,hm.1,?_⟩
    fin_cases j <;> simp [V]

def four (n : Nat) (C : Circuit) (g h : Nat) : Fin 4 → Finset (Fin n) :=
  ![side C g 0,side C g 1,side C h 0,side C h 1]

theorem fourSafe (arch : IsAO2 n C) (top : TopForm G C) (par : ParallelJunk G C)
    {t g h : Nat} (ht : t∈tops G C) (hg : g∈junk G C) (hh : h∈junk G C)
    (r0 : Reach n C (opnd C t 0) (n+g)) (r1 : Reach n C (opnd C t 1) (n+h)) : SafeFour G (four n C g h) := by
  intro X hit
  apply (true_on_set X).mp
  apply compatible arch ht 0 r0 r1
  · apply (junk_raw arch top par hg _).mpr; intro b
    fin_cases b
    · obtain ⟨u,hu,hX⟩ := hit 0; exact ⟨u,hu,decide_eq_true hX⟩
    · obtain ⟨u,hu,hX⟩ := hit 1; exact ⟨u,hu,decide_eq_true hX⟩
  · apply (junk_raw arch top par hh _).mpr; intro b
    fin_cases b
    · obtain ⟨u,hu,hX⟩ := hit 2; exact ⟨u,hu,decide_eq_true hX⟩
    · obtain ⟨u,hu,hX⟩ := hit 3; exact ⟨u,hu,decide_eq_true hX⟩

theorem twoHits (arch : IsAO2 n C) (top : TopForm G C) (par : ParallelJunk G C)
    {g : Nat} (hg : g∈junk G C) {u v : Fin n} (gx : gateVal n C g (pairInput u v)=true) (b : Fin 2) :
    u∈side C g b ∨ v∈side C g b := by
  obtain ⟨x,hx,it⟩ := (junk_raw arch top par hg _).mp gx b
  rcases (pairInput_true u v x).mp it with rfl|rfl <;> tauto

end PEqualNP.Outside.L_meta_3807.Bridge

-- The two counts follow the same OR wires with different vertex labels.
-- Wide raw supports have one possible center. Wide sets of centers have
-- at most six partners on the opposite side of a clean top.

namespace PEqualNP.Outside.L_meta_3807.PairCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules PEqualNP.Outside.L_meta_3807.Bridge


variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

noncomputable def partners (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : Nat) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun y => ∃ t∈tops G C, ∃ b : Fin 2,
    Reach n C (opnd C t b) w ∧ y∈labels G C (opnd C t (1-b))

theorem mem_partners {y : Fin n} {w : Nat} : y∈partners G C w ↔
    ∃ t∈tops G C, ∃ b : Fin 2, Reach n C (opnd C t b) w ∧ y∈labels G C (opnd C t (1-b)) := by
  letI : DecidableEq GateOp := gateOpDecEq
  classical
  simp [partners]

def AtomLaw (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (exc : Nat → Fin 2 → Fin n → Finset (Fin n)) : Prop :=
  ∀ {t g h : Nat} {i j b : Fin 2} {x y : Fin n}, t∈tops G C → Atom G C g i x → Atom G C h j y →
    Reach n C (opnd C t b) (n+g) → Reach n C (opnd C t (1-b)) (n+h) →
      G.Adj x y ∨ y∈exc g i x ∨ x∈exc h j y

def CodegreeOne (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :=
  ∀ u v : Fin n, u≠v → (G.neighborFinset u ∩ G.neighborFinset v).card≤1

theorem partner_card (sq : CodegreeOne G) (exc : Nat → Fin 2 → Fin n → Finset (Fin n))
    (one : ∀ {g i x}, Atom G C g i x → (exc g i x).card≤1)
    (law : AtomLaw G C exc) {w : Nat} (wide : 9<(labels G C w).card) :
    (partners G C w).card≤6 := by
  letI : DecidableEq GateOp := gateOpDecEq
  classical
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp (show 2<(labels G C w).card by omega)
  obtain ⟨ga,ia,aa,ra⟩ := mem_labels.mp ha
  obtain ⟨gb,ib,bb,rb⟩ := mem_labels.mp hb
  obtain ⟨gc,ic,cc,rc⟩ := mem_labels.mp hc
  apply threeCenters ab ac bc sq (exc ga ia a) (exc gb ib b) (exc gc ic c) (one aa) (one bb) (one cc)
  intro y hy
  obtain ⟨t,ht,z,rz,hy⟩ := mem_partners.mp hy
  obtain ⟨g,i,ay,ry⟩ := mem_labels.mp hy
  refine ⟨exc g i y,one ay,?_,?_,?_⟩
  · simpa only [SimpleGraph.mem_neighborFinset] using law ht aa ay (rz.trans ra) ry
  · simpa only [SimpleGraph.mem_neighborFinset] using law ht bb ay (rz.trans rb) ry
  · simpa only [SimpleGraph.mem_neighborFinset] using law ht cc ay (rz.trans rc) ry

theorem light (arch : IsAO2 n C) (sq : CodegreeOne G)
    (exc : Nat → Fin 2 → Fin n → Finset (Fin n))
    (one : ∀ {g i x}, Atom G C g i x → (exc g i x).card≤1) (law : AtomLaw G C exc)
    (E : Finset (Sym2 (Fin n)))
    (cover : ∀ e∈E, ∃ t∈tops G C, ∃ x∈labels G C (opnd C t 0),
       ∃ y∈labels G C (opnd C t 1), e=s(x,y)) : E.card ≤ 189 * C.size := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply bound n C.gates.length (labels G C) (opnd C) (opnd C) (tops G C) E
    (Reach n C) (partners G C) (fun _ => .refl) (fun h e => h.trans e)
    (fun _ _ h => labelBranch arch h) (fun t ht => (Finset.mem_filter.mp ht).1)
    (fun t ht b => ?_) (fun j _ h => partner_card sq exc one law h)
    (fun t ht b w r _ y hy => mem_partners.mpr ⟨t,ht,b,r,hy⟩) cover
  have hl := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have lt := arch.2.1 t hl _ (opt_mem arch hl b)
  omega

theorem heavy (arch : IsAO2 n C) (sq : CodegreeOne G) (E : Finset (Sym2 (Fin n)))
    (cover : ∀ e∈E, ∃ u v g, ∃ b : Fin 2, e=s(u,v) ∧ g<C.gates.length ∧
      9<(side (n:=n) C g b).card ∧ (Outside G u (side C g b)).card≤4 ∧ v∈side C g b) :
    E.card ≤ 18*C.size := by
  letI : DecidableEq GateOp := gateOpDecEq
  classical
  apply heavyBound (n:=n) (m:=C.gates.length) (orIn n C) (opnd C) (Reach n C) (fun u => G.neighborFinset u) E
    (fun _ => .refl) (fun h e => h.trans e) (fun h => rawDown h)
    (fun _ _ h => rawBranch arch h) sq
  intro e he
  obtain ⟨u,v,g,b,rfl,hg,big,near,hv⟩ := cover e he
  have lt := arch.2.1 g hg _ (opt_mem arch hg b)
  refine ⟨u,v,opnd C g b,rfl,by omega,big,?_,hv⟩
  have eq : (orIn n C (opnd C g b) \ G.neighborFinset u) = Outside G u (side C g b) := by
    ext z
    simp [Outside,side]
  rw [eq]
  exact near

end PEqualNP.Outside.L_meta_3807.PairCharge

-- A light atom is either a single literal or a literal joined to one
-- remaining raw OR. At most one other center can block all but one of
-- its available nonneighbors.

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def exc (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : Nat) (i : Fin 2) (x : Fin n) : Finset (Fin n) :=
  if x∈side C g (other i) then ∅ else
    Finset.univ.filter fun y => (Outside G y (Outside G x (side C g (other i)))).card ≤ 1

theorem far_two {g : Nat} {i : Fin 2} {x y : Fin n}
    (lit : x∉side C g (other i)) (abs : y∉exc G C g i x) :
    2≤(Outside G y (Outside G x (side C g (other i)))).card := by
  simp only [exc,if_neg lit,Finset.mem_filter,Finset.mem_univ,true_and] at abs
  omega

theorem exc_one (sq : Codeg G) {g : Nat} {i : Fin 2} {x : Fin n}
    (a : Atom G C g i x) : (exc G C g i x).card ≤ 1 := by
  classical
  by_cases lit : x∈side C g (other i)
  · simp [exc,lit]
  simp only [Atom,lit,false_or] at a
  let S := Outside G x (side C g (other i))
  have wide : 4 < S.card := a.2.2.2.2
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra uv
  simp only [exc,if_neg lit,Finset.mem_filter,Finset.mem_univ,true_and] at hu hv
  change (Outside G u S).card≤1 at hu
  change (Outside G v S).card≤1 at hv
  have common := codeg_card sq u v uv
  have sub : S ⊆ (Outside G u S ∪ Outside G v S) ∪ (nbs G u ∩ nbs G v) := by
    intro z hz
    by_cases h1 : G.Adj u z <;> by_cases h2 : G.Adj v z <;> simp_all [Outside,mem_nbs]
  have l1 := Finset.card_union_le (Outside G u S) (Outside G v S)
  have l2 := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  omega

end PEqualNP.Outside.L_meta_3807.Bridge

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules
open PEqualNP.Outside.L_meta_3807

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem out_pair {B : Finset (Fin n)} {x y a : Fin n} (ha : a ∈ Outside G y (Outside G x B)) :
    a∈B ∧ ¬G.Adj x a ∧ ¬G.Adj y a := by simpa [Outside, and_assoc] using ha

theorem atom_signal (arch : IsAO2 n C) (top : TopForm G C) (par : ParallelJunk G C)
    {g : Nat} {i : Fin 2} {x a : Fin n} (ha : Atom G C g i x)
    (am : a∈side C g (other i)) (X : Finset (Fin n)) (xm : x∈X) (aX : a∈X) :
    gateVal n C g (fun z => decide (z∈X)) = true := by
  apply (junk_raw arch top par ha.1 _).mpr
  intro b
  rcases fin2_cases i b with rfl|rfl
  · exact ⟨x,ha.2.1,decide_eq_true xm⟩
  · exact ⟨a,am,decide_eq_true aX⟩

theorem atomLawOf (arch : IsAO2 n C) (top : TopForm G C) (par : ParallelJunk G C) (sq : Codeg G)
    (E : Nat → Fin 2 → Fin n → Finset (Fin n))
    (far : ∀ {g i x y}, x∉side C g (other i) → y∉E g i x →
      2≤(Outside G y (Outside G x (side C g (other i)))).card) : PairCharge.AtomLaw G C E := by
  intro t g h i j o x y ht a b le ri
  by_contra! bad
  obtain ⟨nxy,ney,nex⟩ := bad
  have nyx : ¬G.Adj y x := fun q => nxy q.symm
  let B := side (n:=n) C g (other i)
  let D := side (n:=n) C h (other j)
  let K := Outside G y (Outside G x B)
  let L := Outside G x (Outside G y D)
  have witnesses : ∃ u∈B, ∃ v∈D, ¬G.Adj x u ∧ ¬G.Adj y u ∧ ¬G.Adj x v ∧ ¬G.Adj y v ∧ ¬G.Adj u v := by
    by_cases lx : x∈B
    · by_cases ly : y∈D
      · exact ⟨x,lx,y,ly,G.irrefl,nyx,nxy,G.irrefl,nxy⟩
      · have sz : 2≤L.card := far ly nex
        obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<L.card by omega)
        obtain ⟨vm,yv,xv⟩ := out_pair hv
        exact ⟨x,lx,v,vm,G.irrefl,nyx,xv,yv,xv⟩
    · by_cases ly : y∈D
      · have sz : 2≤K.card := far lx ney
        obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0<K.card by omega)
        obtain ⟨um,xu,yu⟩ := out_pair hu
        exact ⟨u,um,y,ly,xu,yu,nxy,G.irrefl,fun e => yu e.symm⟩
      · obtain ⟨u,hu,v,hv,uv⟩ := PEqualNP.Outside.L_meta_3807.Transversal.two_transversal G sq K L (far lx ney) (far ly nex)
        obtain ⟨um,xu,yu⟩ := out_pair hu
        obtain ⟨vm,yv,xv⟩ := out_pair hv
        exact ⟨u,um,v,vm,xu,yu,xv,yv,uv⟩
  obtain ⟨u,hu,v,hv,xu,yu,xv,yv,uv⟩ := witnesses
  apply noQuad nxy xu xv yu yv uv
  apply (true_on_set {x,y,u,v}).mp
  apply compatible arch ht o le ri
  · exact atom_signal arch top par a hu _ (by simp) (by simp)
  · exact atom_signal arch top par b hv _ (by simp) (by simp)

end PEqualNP.Outside.L_meta_3807.Bridge

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules
open PEqualNP.Outside.L_meta_3807

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def HeavyP (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) :=
  ∃ u v g, ∃ b : Fin 2, e=s(u,v) ∧ g<C.gates.length ∧
    9<(side (n:=n) C g b).card ∧ (Outside G u (side C g b)).card≤4 ∧ v∈side C g b

def SameP (n : Nat) (C : Circuit) (e : Sym2 (Fin n)) :=
  ∃ j<C.gates.length, ∃ a b : Fin 2, ∃ x∈PairCharge.small (side C j a),
     ∃ y∈PairCharge.small (side C j b), e=s(x,y)

def LightP (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) :=
  ∃ t∈tops G C, ∃ x∈labels G C (opnd C t 0), ∃ y∈labels G C (opnd C t 1), e=s(x,y)

theorem small_mem {S : Finset (Fin n)} {x : Fin n} (hm : x∈S) (sm : S.card≤9) :
    x∈PairCharge.small S := by simpa [PairCharge.small,sm] using hm

theorem gate_lt {g : Nat} (hg : g∈junk G C) : g<C.gates.length :=
  Finset.mem_range.mp (Finset.mem_filter.mp hg).1

theorem promote {u v : Fin n} {g : Nat} {b : Fin 2}
    (nh : ¬HeavyP G C s(u,v)) (ns : ¬SameP n C s(u,v)) (hg : g∈junk G C)
    (uv : ∀ i, u∈side C g i ∨ v∈side C g i)
    (um : u∈side C g b) (near : (Outside G v (side C g b)).card≤4) : Atom G C g b u := by
  have sm : (side (n:=n) C g b).card≤9 := by
    by_contra! big
    exact nh ⟨v,u,g,b,Sym2.eq_swap,gate_lt hg,big,near,um⟩
  refine ⟨hg,um,sm,?_⟩
  by_cases lit : u∈side C g (other b)
  · exact Or.inl lit
  have vm := (uv (other b)).resolve_left lit
  right
  constructor
  · by_contra! small
    exact ns ⟨g,gate_lt hg,b,other b,u,small_mem um sm,v,small_mem vm small,rfl⟩
  · by_contra! close
    by_cases small : (side (n:=n) C g (other b)).card≤9
    · exact ns ⟨g,gate_lt hg,b,other b,u,small_mem um sm,v,small_mem vm small,rfl⟩
    · exact nh ⟨u,v,g,other b,rfl,gate_lt hg,by omega,close,vm⟩

theorem picked {u v : Fin n} {g h : Nat}
    (nh : ¬HeavyP G C s(u,v)) (ns : ¬SameP n C s(u,v)) (sq : Codeg G)
    (safe : SafeFour G (four n C g h)) (hg : g∈junk G C) (hh : h∈junk G C)
    (gHit : ∀ i, u∈side C g i ∨ v∈side C g i) (hHit : ∀ i, u∈side C h i ∨ v∈side C h i) :
    ∃ k b, (k=g ∨ k=h) ∧ Atom G C k b u := by
  have hits (i : Fin 4) : v∈four n C g h i ∨ u∈four n C g h i := by
    fin_cases i
    · exact (gHit 0).symm
    · exact (gHit 1).symm
    · exact (hHit 0).symm
    · exact (hHit 1).symm
  obtain ⟨i,_,hm,near⟩ := missingSmall sq safe hits
  fin_cases i
  · exact ⟨g,0,Or.inl rfl,promote nh ns hg gHit hm near⟩
  · exact ⟨g,1,Or.inl rfl,promote nh ns hg gHit hm near⟩
  · exact ⟨h,0,Or.inr rfl,promote nh ns hh hHit hm near⟩
  · exact ⟨h,1,Or.inr rfl,promote nh ns hh hHit hm near⟩

theorem edgeCover (arch : IsAO2 n C) (top : TopForm G C) (par : ParallelJunk G C)
    (sq : Codeg G) {t g h : Nat} {u v : Fin n} (ht : t∈tops G C) (hg : g∈junk G C) (hh : h∈junk G C)
    (r0 : Reach n C (opnd C t 0) (n+g)) (r1 : Reach n C (opnd C t 1) (n+h))
    (gx : gateVal n C g (pairInput u v)=true) (hx : gateVal n C h (pairInput u v)=true) :
    HeavyP G C s(u,v) ∨ SameP n C s(u,v) ∨ LightP G C s(u,v) := by
  by_cases heavy : HeavyP G C s(u,v)
  · exact Or.inl heavy
  right
  by_cases same : SameP n C s(u,v)
  · exact Or.inl same
  right
  have safe := fourSafe arch top par ht hg hh r0 r1
  have ga := twoHits arch top par hg gx
  have ha := twoHits arch top par hh hx
  have swap : s(v,u) = s(u,v) := Sym2.eq_swap
  obtain ⟨k,i,ki,ax⟩ := picked heavy same sq safe hg hh ga ha
  obtain ⟨l,j,lj,ay⟩ := picked (u:=v) (v:=u) (by rwa [swap]) (by rwa [swap]) sq safe hg hh
    (fun b => (ga b).symm) (fun b => (ha b).symm)
  have ne : k≠l := by
    rintro rfl
    exact same ⟨k,gate_lt ax.1,i,j,u,small_mem ax.2.1 ax.2.2.1,v,small_mem ay.2.1 ay.2.2.1,rfl⟩
  rcases ki with rfl|rfl <;> rcases lj with rfl|rfl
  · exact (ne rfl).elim
  · exact ⟨t,ht,u,mem_labels.mpr ⟨_,i,ax,r0⟩,v,mem_labels.mpr ⟨_,j,ay,r1⟩,rfl⟩
  · exact ⟨t,ht,v,mem_labels.mpr ⟨_,j,ay,r0⟩,u,mem_labels.mpr ⟨_,i,ax,r1⟩,Sym2.eq_swap⟩
  · exact (ne rfl).elim

end PEqualNP.Outside.L_meta_3807.Bridge

-- The three edge classes contribute at most 18, 324, and 189 times the
-- circuit size. Their union covers every edge in the posted filter.

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules
open PEqualNP.Outside.L_meta_3807.PairCharge

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def HeavyCase (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v g, ∃ b : Fin 2, e=s(u,v) ∧ g<C.gates.length ∧ 9<(side (n:=n) C g b).card ∧
    (Outside G u (side C g b)).card≤4 ∧ v∈side C g b

def SameCase (n : Nat) (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ g<C.gates.length, ∃ a b : Fin 2, ∃ u∈side (n:=n) C g a, ∃ v∈side C g b,
    (side (n:=n) C g a).card≤9 ∧ (side (n:=n) C g b).card≤9 ∧ e=s(u,v)

def LabelCase (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ t∈tops G C, ∃ x∈labels G C (opnd C t 0), ∃ y∈labels G C (opnd C t 1), e=s(x,y)

theorem countCases (arch : IsAO2 n C) (sq : Codeg G) (law : AtomLaw G C (exc G C))
    (E : Finset (Sym2 (Fin n)))
    (cases : ∀ e∈E, HeavyCase G C e ∨ SameCase n C e ∨ LabelCase G C e) :
    E.card ≤ 531*C.size := by
  classical
  have h4 : CodegreeOne G := by
    intro u v uv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset] at hx hy
    exact sq u v uv x y hx.1 hx.2 hy.1 hy.2
  let H := E.filter (HeavyCase G C)
  let S := E.filter (SameCase n C)
  let L := E.filter (LabelCase G C)
  have h : H.card ≤ 18 * C.size := heavy arch h4 H (fun e he => (Finset.mem_filter.mp he).2)
  have l : L.card ≤ 189 * C.size := light arch h4 (exc G C) (fun a => exc_one sq a) law L
    (fun e he => (Finset.mem_filter.mp he).2)
  have s : S.card ≤ 324 * C.gates.length := by
    apply sameLightAny (fun j b => side (n:=n) C j b)
    intro e he
    obtain ⟨g,hg,a,b,u,hu,v,hv,sa,sb,eq⟩ := (Finset.mem_filter.mp he).2
    refine ⟨g,hg,a,b,u,?_,v,?_,eq⟩
    · simpa [small,sa] using hu
    · simpa [small,sb] using hv
  change S.card ≤ 324 * C.size at s
  have sub : E ⊆ H ∪ S ∪ L := by
    intro e he
    rcases cases e he with x|x|x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,x⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,x⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,x⟩)
  have c1 := Finset.card_union_le H S
  have c2 := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  omega

end PEqualNP.Outside.L_meta_3807.Bridge

namespace PEqualNP.Outside.L_meta_3807.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Outside.L_meta_3807.GateRules
open PEqualNP.Outside.L_meta_3807

variable {n : Nat} {C : Circuit}

theorem in_small {S : Finset (Fin n)} {u : Fin n} (hu : u∈PairCharge.small S) : u∈S ∧ S.card≤9 := by
  by_cases sm : S.card≤9
  · exact ⟨by simpa [PairCharge.small,sm] using hu,sm⟩
  · simp [PairCharge.small,sm] at hu

theorem sameCase_of {e : Sym2 (Fin n)} (hs : SameP n C e) : SameCase n C e := by
  obtain ⟨g,hg,a,b,u,hu,v,hv,eq⟩ := hs
  exact ⟨g,hg,a,b,u,(in_small hu).1,v,(in_small hv).1,(in_small hu).2,(in_small hv).2,eq⟩

end PEqualNP.Outside.L_meta_3807.Bridge

open PEqualNP.Outside.L_meta_3807.GateRules PEqualNP.Outside.L_meta_3807.Bridge

open Classical in
theorem PEqualNP.Outside.L_meta_3807 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → {x12 ∈ PEqualNP.TopForm.Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x7, ∃ x16 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x17 ∈ PEqualNP.TopForm.junk x3 x7, x16 ≠ x17 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (0 : Fin (2 : ℕ))) x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (1 : Fin (2 : ℕ))) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  refine ⟨531,?_⟩
  intro n G inst girth _ C least top _ par
  classical
  have sq := codeg_of_girth girth
  have law : PEqualNP.Outside.L_meta_3807.PairCharge.AtomLaw G C (exc G C) := atomLawOf least.1 top par sq (exc G C) (fun lit abs => far_two lit abs)
  refine (countCases least.1 sq law _ ?_).trans ?_
  · intro e he
    obtain ⟨_,u,v,rfl,t,ht,g,hg,h,hh,_,r0,r1,gx,hx⟩ := Finset.mem_filter.mp he
    rcases edgeCover least.1 top par sq ht hg hh (orReaches_reach _ _ r0).1 (orReaches_reach _ _ r1).1 gx hx with heavy|same|light
    · exact Or.inl heavy
    · exact Or.inr (Or.inl (sameCase_of same))
    · exact Or.inr (Or.inr light)
  · omega
