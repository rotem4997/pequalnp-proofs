import PEqualNP.Defs
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_18392.Routing

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

end PEqualNP.Outside.L_meta_18392.Routing

namespace PEqualNP.Outside.L_meta_18392.Mix.Routing

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

end PEqualNP.Outside.L_meta_18392.Mix.Routing

namespace PEqualNP.Outside.L_meta_18392.Mix

open PEqualNP.TopForm

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

end PEqualNP.Outside.L_meta_18392.Mix

namespace PEqualNP.Outside.L_meta_18392.Mix

open PEqualNP.TopForm

section CleanClauses

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {I : Type*} {S : I → Finset (Fin n)} {U : Finset (Sym2 (Fin n))}

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

theorem singleTopNeighborUnique (h₄ : NoFourCycle G) (neg : rejectsIndependent G S)
    (shape : ∀ j, (S j).card ≤ 1 ∨ ∃ z : Fin n, ∀ w ∈ S j, (G.deleteEdges ↑U).Adj w z)
    {a b c : Fin n} (ab : G.Adj a b) (ac : G.Adj a c) (removed : s(b,a) ∈ U)
    (pos₁ : ∀ j, a ∈ S j ∨ b ∈ S j) (pos₂ : ∀ j, a ∈ S j ∨ c ∈ S j) : b = c := by
  obtain ⟨j,ha,_⟩ := missingPair (a := a) (b := a) neg G.irrefl
  by_contra hbc
  exact incompatibleOldClause h₄ j (shape j) hbc ab ac removed
    ((pos₁ j).resolve_left ha) ((pos₂ j).resolve_left ha)

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

end PEqualNP.Outside.L_meta_18392.Mix

namespace PEqualNP.Outside.L_meta_18392.Mix

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_18392.Mix.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

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

end PEqualNP.Outside.L_meta_18392.Mix

namespace PEqualNP.Outside.L_meta_18392.Mix

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

end PEqualNP.Outside.L_meta_18392.Mix

namespace PEqualNP.Outside.L_meta_18392.Mix

private def boundarySlots (n : ℕ) (D : Finset ℕ) (wire : ℕ → Fin 2 → ℕ) :
    Finset (ℕ × Fin 2) := by
  classical
  exact (D.product (Finset.univ : Finset (Fin 2))).filter
    (fun k => ¬ ∃ h ∈ D, wire k.1 k.2 = n+h)

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

end PEqualNP.Outside.L_meta_18392.Mix

namespace PEqualNP.Outside.L_meta_18392.Mix

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_18392.Mix.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

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

end PEqualNP.Outside.L_meta_18392.Mix

namespace PEqualNP.Outside.L_meta_18392.Cone

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_18392.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma rawShapeNoOutside (ao : IsAO2 n C) (none : orN G C \ lam G C = ∅)
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

lemma noOutsideDirect (ao : IsAO2 n C) (none : orN G C \ lam G C = ∅)
    {w j : ℕ} (hj : j ∈ junk G C) (hr : OrReaches n C w j) : w = n + j := by
  rcases lastOrBefore (orReaches_reach j _ hr).1 with he | ⟨m,hm,ho,hi,hb,_⟩
  · exact he
  · have hop := lastOrOutside ao hj hm ho hi hb
    rw [none] at hop
    exact (Finset.notMem_empty _ hop).elim

def oldSupport (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset (Fin n)) : Prop :=
  S.card ≤ 1 ∨ ∃ q : Fin n, ∀ v ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj v q

lemma rawOperand (ao : IsAO2 n C) (top : TopForm G C) {g : ℕ} (hg : g < C.size)
    (andG : (gateAt C g).op = .and) (b : Fin 2)
    (noJunk : ¬∃ j ∈ junk G C, OrReaches n C (opnd C g b) j)
    (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C g b) = true ↔
      ∃ u ∈ orIn n C (opnd C g b), x u = true := by
  constructor
  · intro hv
    obtain ⟨w, hr, hwv, hw⟩ := or_trace (n := n) (by simp) (opnd C g b) hv
    rcases hw with raw | ⟨j, hj, rfl, ho⟩
    · let u : Fin n := ⟨w, raw⟩
      refine ⟨u, reach_mem_orIn u hr, ?_⟩
      exact (val_ofFn C x u).symm.trans hwv
    · have hjAnd := (ao.1 _ (gateAt_mem hj)).resolve_right ho
      have hr' := reach_orReaches hr j rfl hj
      exact (noJunk ⟨j, operandOrAndJunk ao top hg andG hr' hjAnd, hr'⟩).elim
  · rintro ⟨u, hu, hx⟩
    exact reach_var_val x _ u (mem_orIn_reach u hu) hx

lemma conjunctionSupport (ao : IsAO2 n C) (top : TopForm G C)
    (none : orN G C \ lam G C = ∅) :
    ∀ g < C.size, (gateAt C g).op = .and →
      ∃ S : Finset (Finset (Fin n)), (∀ R ∈ S, oldSupport G C R) ∧
        ∀ x : Fin n → Bool, gateVal n C g x = true ↔ ∀ R ∈ S, ∃ u ∈ R, x u = true := by
  intro g
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    intro hg hAnd
    have parts (b : Fin 2) :
        ∃ S : Finset (Finset (Fin n)), (∀ R ∈ S, oldSupport G C R) ∧
          ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) = true ↔
            ∀ R ∈ S, ∃ u ∈ R, x u = true := by
      by_cases hJ : ∃ j ∈ junk G C, OrReaches n C (opnd C g b) j
      · obtain ⟨j, hj, hReach⟩ := hJ
        have hDirect := noOutsideDirect ao none hj hReach
        have hBound := opndBound ao hg b
        rw [hDirect] at hBound
        obtain ⟨hlen, hop, _⟩ := junkData hj
        obtain ⟨S, shape, ev⟩ := ih j (by omega) hlen hop
        exact ⟨S, shape, fun x => by rw [hDirect, ← gateVal_eq_val]; exact ev x⟩
      · let R := orIn n C (opnd C g b)
        refine ⟨{R}, ?_, ?_⟩
        · intro T ht
          have eq : T = R := Finset.mem_singleton.mp ht
          subst T
          exact rawShapeNoOutside ao none (lt_trans (opndBound ao hg b) (by unfold Circuit.size at hg; omega))
        · intro x
          simpa only [Finset.mem_singleton, forall_eq] using rawOperand ao top hg hAnd b hJ x
    obtain ⟨S, shapeS, evS⟩ := parts 0
    obtain ⟨T, shapeT, evT⟩ := parts 1
    refine ⟨S ∪ T, ?_, ?_⟩
    · intro R hR
      exact (Finset.mem_union.mp hR).elim (shapeS R) (shapeT R)
    · intro x
      rw [andValBoth ao hg hAnd x, evS x, evT x]
      constructor
      · intro h R hR
        exact (Finset.mem_union.mp hR).elim (h.1 R) (h.2 R)
      · intro h
        exact ⟨fun R hR => h R (Finset.mem_union_left _ hR),
          fun R hR => h R (Finset.mem_union_right _ hR)⟩

lemma centrelessCovers (least : IsLeastAO G C) (top : TopForm G C)
    (none : orN G C \ lam G C = ∅)
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) :
    ∃ g ∈ centreless G C, gateVal n C g (pairInput u v) = true := by
  obtain ⟨g, hg, b, j, hj, on, reach, _⟩ := residualTrace least top he
  have dir := noOutsideDirect least.1 none hj reach
  have empty : side (n := n) C g b = ∅ := by
    change orIn n C (opnd C g b) = ∅
    rw [dir, andRawEmpty (junkData hj).2.1]
  refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, on⟩
  fin_cases b
  · exact Or.inl empty
  · exact Or.inr empty

end PEqualNP.Outside.L_meta_18392.Cone

namespace PEqualNP.Outside.L_meta_18392.Profile

def supportData : List (ℕ × ℕ) := [(1, 0), (2, 0), (4, 0), (5, 34), (8, 0), (16, 0), (17, 514), (18, 264),
    (20, 544), (21, 546), (32, 0), (33, 2049), (34, 1032), (48, 1280), (50, 1288), (64, 0),
    (65, 8194), (68, 8224), (69, 8226), (72, 4224), (80, 8704), (81, 8706), (84, 8736), (85, 8738),
    (128, 0), (129, 16385), (136, 4160), (160, 18432), (161, 18433), (192, 192), (256, 0), (257, 32769),
    (258, 260), (260, 1040), (272, 12), (288, 34816), (289, 34817), (384, 49152), (385, 49153), (416, 51200),
    (417, 51201), (512, 0), (514, 32776), (516, 2064), (520, 16512), (528, 33024), (530, 33032), (544, 33792),
    (546, 33800), (560, 34048), (562, 34056), (576, 20480), (584, 20608), (768, 3072), (772, 3088), (1024, 0),
    (1026, 516), (1032, 8256), (1056, 48), (1152, 12288), (1160, 12352), (1280, 768), (1282, 772), (1536, 3)]

def edgeRows : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136,
    272, 1040, 288, 544, 192, 1088, 640, 768]

def negativeRows : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113,
    135, 149, 163, 177, 269, 325, 389, 526,
    540, 582, 596, 1066, 1186, 1288, 1408, 1546]

def compatible (i : Fin 16) : ℕ :=
  ([36026598006522441, 9187344685394298881, 2080276015510498, 7016610400212877314, 2112815087648524, 18140508103731314692, 6772991643844624, 1873499507090522128,
    27023791434498912, 11422923075168002208, 7205761593555028992, 9520598617144980480, 2062590377984, 16543973231682945024, 10982007900754411520, 16174706680141971456] : List ℕ).getD i.val 0

def oldFree (i : Fin 16) : ℕ :=
  ([9223370591296288767, 9223372036843961783, 13763000439769399295, 18445261914855419775, 18140490494365401087, 18158513697544862967, 17149707380422868991, 18442222881358741503,
    11527420638796947327, 11457157452014812351, 18417611405030035455, 18419711927102994431, 16710606417290592255, 16573246628707237887, 18439969020061941759, 18444520893410443263] : List ℕ).getD i.val 0

def missing (i : Fin 24) : ℕ :=
  ([12441935781945189408, 17125367120222262274, 12171024337298686244, 16854737150548279302, 13736738266529408048, 18420169604807529490, 13465826821878579508, 18149539635133415446,
    12014110721648927792, 16697542059926000658, 11743199826892456244, 16426912640142049302, 10200624569380828322, 11495427053965046962, 9772800196279334066, 3206565120745516129,
    7890308720322780163, 4503601812955212913, 9187345412535622675, 29320018977588077, 33840797887464317, 4483809424179183, 9005000248262655, 2194660634477] : List ℕ).getD i.val 0

def blocked (a : ℕ) : Prop := ∃ z : Fin 24, a &&& missing z = 0

local instance (a : ℕ) : Decidable (blocked a) := by unfold blocked; infer_instance

def exceptional : Fin 4 → Fin 16 × Fin 16 := ![(1,10), (2,11), (5,15), (9,11)]

def paired (i j : Fin 16) : ℕ := compatible i &&& compatible j

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
lemma correctCompatibility : ∀ i : Fin 16, ∀ s : Fin 64,
    have q := supportData.getD s.val (0,0)
    (compatible i).testBit s.val = (!q.2.testBit i.val && decide (q.1 &&& edgeRows.getD i.val 0 ≠ 0)) ∧
    (oldFree i).testBit s.val = !q.2.testBit i.val := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
lemma correctMissing : ∀ i : Fin 24, ∀ s : Fin 64,
    (missing i).testBit s.val =
      decide ((supportData.getD s.val (0,0)).1 &&& negativeRows.getD i.val 0 = 0) := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma triples : ∀ i j k : Fin 16, i < j → j < k →
    blocked (paired i j &&& compatible k) := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma pairs : ∀ i j : Fin 16, i < j → ¬ blocked (paired i j) →
    ∃ p : Fin 4, exceptional p = (i,j) := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma coexisting : ∀ p q : Fin 4, p < q →
    let a := exceptional p
    let b := exceptional q
    ¬ blocked (paired a.1 a.2 &&& oldFree b.1 &&& oldFree b.2) →
    ¬ blocked (paired b.1 b.2 &&& oldFree a.1 &&& oldFree a.2) →
    p = 1 ∧ q = 3 := by
  decide

def accepts (S : Finset (Fin 64)) (i : Fin 16) : Prop :=
  ∀ s ∈ S, (compatible i).testBit s.val = true

def avoids (S : Finset (Fin 64)) (i : Fin 16) : Prop :=
  ∀ s ∈ S, (oldFree i).testBit s.val = true

def safe (S : Finset (Fin 64)) : Prop :=
  ∀ r : Fin 24, ∃ s ∈ S, (missing r).testBit s.val = true

lemma cannot_block {S : Finset (Fin 64)} {p : ℕ} (hS : safe S)
    (inProfile : ∀ s ∈ S, p.testBit s.val = true) : ¬ blocked p := by
  rintro ⟨r, hr⟩
  obtain ⟨s, mem, hmiss⟩ := hS r
  have hbit := congrArg (fun w : ℕ => w.testBit s.val) hr
  exact Bool.noConfusion (show true = false by
    simpa only [Nat.testBit_and, Nat.zero_testBit, inProfile s mem, hmiss, Bool.and_true] using hbit)

lemma not_three {S : Finset (Fin 64)} (safeS : safe S) {i j k : Fin 16}
    (hi : accepts S i) (hj : accepts S j) (hk : accepts S k) (hij : i < j) (hjk : j < k) : False := by
  apply cannot_block safeS _ (triples i j k hij hjk)
  intro s hs
  simp only [paired, Nat.testBit_and, hi s hs, hj s hs, hk s hs, Bool.and_true]

lemma pair_index {S : Finset (Fin 64)} (safeS : safe S) {i j : Fin 16}
    (hi : accepts S i) (hj : accepts S j) (hij : i < j) :
    ∃ p : Fin 4, exceptional p = (i, j) := by
  apply pairs i j hij
  apply cannot_block safeS
  intro s hs
  simp only [paired, Nat.testBit_and, hi s hs, hj s hs, Bool.and_true]

lemma dual_pair {S T : Finset (Fin 64)} (hS : safe S) (hT : safe T)
    {p q : Fin 4} (horder : p < q)
    (p1 : accepts S (exceptional p).1) (p2 : accepts S (exceptional p).2)
    (q1 : accepts T (exceptional q).1) (q2 : accepts T (exceptional q).2)
    (crossQ1 : avoids S (exceptional q).1) (crossQ2 : avoids S (exceptional q).2)
    (crossP1 : avoids T (exceptional p).1) (crossP2 : avoids T (exceptional p).2) :
    p = 1 ∧ q = 3 := by
  apply coexisting p q horder
  · apply cannot_block hS
    intro s hs
    simp only [paired, Nat.testBit_and, p1 s hs, p2 s hs, crossQ1 s hs, crossQ2 s hs,
      Bool.and_true]
  · apply cannot_block hT
    intro s hs
    simp only [paired, Nat.testBit_and, q1 s hs, q2 s hs, crossP1 s hs, crossP2 s hs,
      Bool.and_true]

lemma cardinal_two {A : Finset (Fin 16)} {S : Finset (Fin 64)} (hS : safe S)
    (hA : ∀ i ∈ A, accepts S i) : A.card ≤ 2 := by
  by_contra! tooLarge
  have hA0 : A.Nonempty := Finset.card_pos.mp (by omega)
  let x := A.min' hA0
  have hx : x ∈ A := A.min'_mem hA0
  let B := A.erase x
  have hBcard : B.card = A.card - 1 := Finset.card_erase_of_mem hx
  have hB0 : B.Nonempty := Finset.card_pos.mp (by omega)
  let y := B.min' hB0
  have hy : y ∈ B := B.min'_mem hB0
  let D := B.erase y
  have hDcard : D.card = B.card - 1 := Finset.card_erase_of_mem hy
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
  have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
  have hzB : z ∈ B := (Finset.mem_erase.mp hz).2
  have hzA : z ∈ A := (Finset.mem_erase.mp hzB).2
  have hxy : x < y := lt_of_le_of_ne (A.min'_le y hyA) (Finset.mem_erase.mp hy).1.symm
  have hyz : y < z := lt_of_le_of_ne (B.min'_le z hzB) (Finset.mem_erase.mp hz).1.symm
  exact not_three hS (hA x hx) (hA y hyA) (hA z hzA) hxy hyz

lemma pair_card_two {A : Finset (Fin 16)} {S : Finset (Fin 64)} (hS : safe S)
    (hA : ∀ i ∈ A, accepts S i) (hcard : A.card = 2) :
    ∃ p : Fin 4, A = {(exceptional p).1, (exceptional p).2} := by
  have hA0 : A.Nonempty := Finset.card_pos.mp (by omega)
  let x := A.min' hA0
  have hx := A.min'_mem hA0
  have hBcard : (A.erase x).card = 1 := by rw [Finset.card_erase_of_mem hx, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hBcard
  have hy' : y ∈ A.erase x := hy ▸ Finset.mem_singleton_self y
  have hyA := (Finset.mem_erase.mp hy').2
  have hxy := lt_of_le_of_ne (A.min'_le y hyA) (Finset.mem_erase.mp hy').1.symm
  obtain ⟨p, hp⟩ := pair_index hS (hA x hx) (hA y hyA) hxy
  refine ⟨p, ?_⟩
  rw [hp, Prod.fst, Prod.snd, ← hy]
  exact (Finset.insert_erase hx).symm

lemma exceptional_anchor : ∀ p : Fin 4,
    (if p = 1 ∨ p = 3 then (11 : Fin 16) else (exceptional p).1) ∈
      ({(exceptional p).1, (exceptional p).2} : Finset (Fin 16)) := by decide

lemma collective {ι : Type} (indices : Finset ι) (U : Finset (Fin 16))
    (A : ι → Finset (Fin 16)) (S : ι → Finset (Fin 64))
    (covered : U ⊆ indices.biUnion A) (contained : ∀ i ∈ indices, A i ⊆ U)
    (truth : ∀ i ∈ indices, ∀ j ∈ A i, accepts (S i) j)
    (below : ∀ i ∈ indices, safe (S i))
    (old : ∀ i ∈ indices, ∀ j ∈ U, avoids (S i) j) :
    U.card ≤ indices.card + 1 := by
  classical
  have hcard (i : ι) (hi : i ∈ indices) : (A i).card ≤ 2 :=
    cardinal_two (below i hi) (truth i hi)
  by_cases pairPresent : ∃ i ∈ indices, (A i).card = 2
  · obtain ⟨i, hi, sizeI⟩ := pairPresent
    obtain ⟨p, codeI⟩ := pair_card_two (below i hi) (truth i hi) sizeI
    let z := if p = 1 ∨ p = 3 then (11 : Fin 16) else (exceptional p).1
    have guard (j : ι) (hj : j ∈ indices) (sizeJ : (A j).card = 2) : z ∈ A j := by
      obtain ⟨q, codeJ⟩ := pair_card_two (below j hj) (truth j hj) sizeJ
      have leftI : (exceptional p).1 ∈ A i := by rw [codeI]; simp
      have rightI : (exceptional p).2 ∈ A i := by rw [codeI]; simp
      have leftJ : (exceptional q).1 ∈ A j := by rw [codeJ]; simp
      have rightJ : (exceptional q).2 ∈ A j := by rw [codeJ]; simp
      have ifGiven (i j : ι) (hi : i ∈ indices) (hj : j ∈ indices)
          (p q : Fin 4) (hpq : p < q)
          (pi : (exceptional p).1 ∈ A i) (pi' : (exceptional p).2 ∈ A i)
          (qj : (exceptional q).1 ∈ A j) (qj' : (exceptional q).2 ∈ A j) :
          p = 1 ∧ q = 3 :=
        dual_pair (below i hi) (below j hj) hpq
          (truth i hi _ pi) (truth i hi _ pi') (truth j hj _ qj) (truth j hj _ qj')
          (old i hi _ (contained j hj qj)) (old i hi _ (contained j hj qj'))
          (old j hj _ (contained i hi pi)) (old j hj _ (contained i hi pi'))
      rcases lt_trichotomy p q with h | h | h
      · obtain ⟨hp, hq⟩ := ifGiven i j hi hj p q h leftI rightI leftJ rightJ
        subst p
        subst q
        rw [codeJ]
        decide
      · subst q
        rw [codeJ]
        exact exceptional_anchor p
      · obtain ⟨hq, hp⟩ := ifGiven j i hj hi q p h leftJ rightJ leftI rightI
        subst p
        subst q
        rw [codeJ]
        decide
    have each (i : ι) (hi : i ∈ indices) : ((A i).erase z).card ≤ 1 := by
      by_cases eq : (A i).card = 2
      · rw [Finset.card_erase_of_mem (guard i hi eq), eq]
      · exact (Finset.card_le_card (Finset.erase_subset _ _)).trans (by have := hcard i hi; omega)
    have sub : U ⊆ insert z (indices.biUnion fun i => (A i).erase z) := by
      intro k hk
      rcases Finset.mem_biUnion.mp (covered hk) with ⟨i, hi, hk'⟩
      by_cases e : k = z
      · simp [e]
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_erase.mpr ⟨e, hk'⟩⟩)
    calc
      U.card ≤ (insert z (indices.biUnion fun i => (A i).erase z)).card := Finset.card_le_card sub
      _ ≤ (indices.biUnion fun i => (A i).erase z).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ i ∈ indices, ((A i).erase z).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ indices.card + 1 := by
        exact Nat.add_le_add_right ((Finset.sum_le_sum each).trans (by simp)) _
  · have each (i : ι) (hi : i ∈ indices) : (A i).card ≤ 1 := by
      have ne : (A i).card ≠ 2 := fun he => pairPresent ⟨i, hi, he⟩
      have := hcard i hi
      omega
    calc
      U.card ≤ (indices.biUnion A).card := Finset.card_le_card covered
      _ ≤ ∑ i ∈ indices, (A i).card := Finset.card_biUnion_le
      _ ≤ indices.card := (Finset.sum_le_sum each).trans (by simp)
      _ ≤ indices.card + 1 := Nat.le_succ _

end PEqualNP.Outside.L_meta_18392.Profile

namespace PEqualNP.Outside.L_meta_18392.Profile

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def graphEdges : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def graph := edgeGraph 11 graphEdges

local instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def ea (i : Fin 16) : Fin 11 := Fin.ofNat 11 (graphEdges.getD i.val (0,0)).1
def eb (i : Fin 16) : Fin 11 := Fin.ofNat 11 (graphEdges.getD i.val (0,0)).2
def edgeFor (i : Fin 16) : Sym2 (Fin 11) := s(ea i,eb i)

def supportSet (i : Fin 64) : Finset (Fin 11) :=
  Finset.univ.filter fun u => (supportData.getD i.val (0,0)).1.testBit u.val

def demands (j : Fin 64) (i : Fin 16) : Bool :=
  (supportData.getD j.val (0,0)).2.testBit i.val

def negative (r : Fin 24) (u : Fin 11) : Bool :=
  (negativeRows.getD r.val 0).testBit u.val

set_option maxRecDepth 32768 in
lemma singletonStock : ∀ v : Fin 11, ∃ i : Fin 64,
    supportSet i = {v} ∧ ∀ e, demands i e = false := by decide +kernel

def recordedNeighbors : Fin 11 → Finset (Fin 11) := ![{9, 10}, {4, 8}, {5, 10}, {6, 7}, {1, 8, 10}, {2, 8, 9}, {3, 7, 10}, {3, 6, 9}, {1, 4, 5, 9}, {0, 5, 7, 8}, {0, 2, 4, 6}]
def slotsAt : Fin 11 → Finset (Fin 64) := ![{41, 55, 63}, {5, 30, 34}, {10, 55, 58}, {15, 24, 29}, {1, 30, 32, 55, 56, 61, 62}, {2, 30, 33, 41, 43, 53, 54}, {4, 24, 26, 55, 57, 59, 60}, {4, 15, 19, 41, 44, 51, 52}, {1, 5, 7, 10, 12, 13, 14, 41, 42, 45, 46, 47, 48, 49, 50}, {0, 10, 11, 24, 25, 27, 28, 30, 31, 35, 36, 37, 38, 39, 40}, {0, 2, 3, 5, 6, 8, 9, 15, 16, 17, 18, 20, 21, 22, 23}]

set_option maxRecDepth 32768 in
lemma neighborExact : ∀ q, graph.neighborFinset q = recordedNeighbors q := by
  intro q
  ext v
  simp only [SimpleGraph.mem_neighborFinset]
  have h : ∀ q v, graph.Adj q v ↔ v ∈ recordedNeighbors q := by decide +kernel
  exact h q v

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma powersetStock : ∀ q : Fin 11,
    (recordedNeighbors q).powerset = insert ∅ ((slotsAt q).image supportSet) := by
  intro q
  fin_cases q <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma stockDemand : ∀ q : Fin 11, ∀ s ∈ slotsAt q, ∀ e : Fin 16, demands s e = true →
      (ea e = q ∧ eb e ∈ supportSet s) ∨ (eb e = q ∧ ea e ∈ supportSet s) := by
  intro q
  fin_cases q <;> decide +kernel

lemma neighborStock (q : Fin 11) (R : Finset (Fin 11)) (hs : R ∈ (graph.neighborFinset q).powerset)
    (hR : R.Nonempty) :
    ∃ i : Fin 64, supportSet i = R ∧ ∀ e : Fin 16, demands i e = true →
      (ea e = q ∧ eb e ∈ R) ∨ (eb e = q ∧ ea e ∈ R) := by
  rw [neighborExact, powersetStock] at hs
  have h := (Finset.mem_insert.mp hs).resolve_left hR.ne_empty
  obtain ⟨s, hmem, rfl⟩ := Finset.mem_image.mp h
  exact ⟨s, rfl, stockDemand q s hmem⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma stockPositive : ∀ s : Fin 64, ∀ e : Fin 16,
    (supportData.getD s.val (0,0)).1 &&& edgeRows.getD e.val 0 ≠ 0 ↔
      ea e ∈ supportSet s ∨ eb e ∈ supportSet s := by
  intro s e
  fin_cases e <;> revert s
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma stockNegative : ∀ r : Fin 24, ∀ s : Fin 64,
    (missing r).testBit s.val = true ↔ ∀ v ∈ supportSet s, negative r v = false := by
  intro r
  fin_cases r <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma negSound : ∀ r : Fin 24, graphFun graph ∅ (negative r) = false := by decide +kernel

lemma edgeInj : Function.Injective edgeFor := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
lemma edgeStock : ∀ a b : Fin 11, graph.Adj a b ↔ ∃ i : Fin 16, edgeFor i = s(a,b) := by
  intro a
  fin_cases a <;> decide +kernel

end PEqualNP.Outside.L_meta_18392.Profile

namespace PEqualNP.Outside.L_meta_18392.Zero

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_18392.Cone PEqualNP.Outside.L_meta_18392.Profile
open PEqualNP.Outside.L_meta_18392.Routing (pairInput_true topData)

local instance : DecidableRel graph.Adj := by unfold graph; infer_instance

lemma stockSupport {C : Circuit} {R : Finset (Fin 11)} (hR : R.Nonempty)
    (shape : oldSupport graph C R) :
    ∃ s : Fin 64, supportSet s = R ∧
      ∀ i : Fin 16, edgeFor i ∈ Ustar graph C → demands s i = false := by
  rcases shape with one | ⟨q, hq⟩
  · have h := Finset.card_eq_one.mp (show R.card = 1 from le_antisymm one hR.card_pos)
    obtain ⟨v, rfl⟩ := h
    obtain ⟨s, eq, notDemand⟩ := singletonStock v
    exact ⟨s,eq,fun i _ => notDemand i⟩
  · have hn : R ∈ (graph.neighborFinset q).powerset := by
      apply Finset.mem_powerset.mpr
      intro u hu
      rw [SimpleGraph.mem_neighborFinset]
      exact (SimpleGraph.deleteEdges_adj.mp (hq u hu)).1.symm
    obtain ⟨s, eq, localDemand⟩ := neighborStock q R hn hR
    refine ⟨s, eq, ?_⟩
    intro i hi
    cases hd : demands s i
    · rfl
    · exfalso
      rcases localDemand i hd with ⟨a, b⟩ | ⟨a,b⟩
      · have h := (SimpleGraph.deleteEdges_adj.mp (hq (eb i) b)).2
        apply h
        change s(eb i, q) ∈ Ustar graph C
        simpa only [edgeFor, a, Sym2.eq_swap] using hi
      · have h := (SimpleGraph.deleteEdges_adj.mp (hq (ea i) b)).2
        apply h
        change s(ea i, q) ∈ Ustar graph C
        simpa only [edgeFor, a] using hi

lemma excludes {C : Circuit} (least : IsLeastAO graph C) (normal : TopForm graph C)
    (hJ : 2 ≤ (junk graph C).card) (none : orN graph C \ lam graph C = ∅) :
    2 * (Ustar graph C).card ≤ 2 * (centreless graph C).card + (junk graph C).card := by
  classical
  let U : Finset (Fin 16) := Finset.univ.filter (fun i => edgeFor i ∈ Ustar graph C)
  have codeMem (i : Fin 16) : i ∈ U ↔ edgeFor i ∈ Ustar graph C := by simp [U]
  have coverCode : U.image edgeFor = Ustar graph C := by
    ext uv
    constructor
    · intro huv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huv
      exact (codeMem i).mp hi
    · induction uv using Sym2.inductionOn with
      | _ u v =>
        intro huv
        have hadj : graph.Adj u v :=
          SimpleGraph.mem_edgeFinset.mp (Finset.sdiff_subset huv)
        obtain ⟨i, eq⟩ := (edgeStock u v).mp hadj
        exact Finset.mem_image.mpr ⟨i, (codeMem i).mpr (eq.symm ▸ huv), eq⟩
  have ucard : U.card = (Ustar graph C).card := by
    rw [← coverCode, Finset.card_image_of_injective _ edgeInj]
  let A := fun g => U.filter (fun i => gateVal 11 C g (pairInput (ea i) (eb i)) = true)
  let indices := (centreless graph C).filter (fun g => (A g).Nonempty)
  have gtop (g : ℕ) (hg : g ∈ indices) : g ∈ tops graph C :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1
  have covers : U ⊆ indices.biUnion A := by
    intro i hi
    obtain ⟨g, hg, on⟩ := centrelessCovers least normal none ((codeMem i).mp hi)
    have hit : i ∈ A g := Finset.mem_filter.mpr ⟨hi, on⟩
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, ⟨i, hit⟩⟩, hit⟩
  have clauses (g : ℕ) (hg : g ∈ indices) :
      ∃ S : Finset (Fin 64), safe S ∧ (∀ j ∈ A g, accepts S j) ∧
        ∀ j ∈ U, avoids S j := by
    have gdata := topData (gtop g hg)
    obtain ⟨W, shape, ev⟩ := conjunctionSupport least.1 normal none g
      gdata.1 gdata.2.1
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hg).2
    have witness (R : Finset (Fin 11)) (hR : R ∈ W) : R.Nonempty := by
      obtain ⟨u, hu, _⟩ := (ev _).mp (Finset.mem_filter.mp hj).2 R hR
      exact ⟨u, hu⟩
    have hslot (R : {R // R ∈ W}) := stockSupport (witness R R.2) (shape R R.2)
    let slot (R : {R // R ∈ W}) := Classical.choose (hslot R)
    have slotEq (R : {R // R ∈ W}) : supportSet (slot R) = R :=
      (Classical.choose_spec (hslot R)).1
    let S := W.attach.image slot
    refine ⟨S, ?_, ?_, ?_⟩
    · intro r
      have ng : gateVal 11 C g (negative r) ≠ true := by
        intro val
        exact Bool.noConfusion ((negSound r).symm.trans (gdata.2.2 _ val))
      have h : ¬ ∀ R ∈ W, ∃ u ∈ R, negative r u = true := fun hall =>
        ng ((ev (negative r)).mpr hall)
      push Not at h
      obtain ⟨R, hR, absent⟩ := h
      let w : {R // R ∈ W} := ⟨R, hR⟩
      refine ⟨slot w, Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, rfl⟩, ?_⟩
      apply (stockNegative r _).mpr
      rw [slotEq]
      intro v hv
      simpa using absent v hv
    · intro i hi s hs
      obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hs
      have hDemand : demands (slot R) i = false :=
        (Classical.choose_spec (hslot R)).2 i ((codeMem i).mp ((Finset.mem_filter.mp hi).1))
      have hHit : (supportData.getD (slot R).val (0,0)).1 &&& edgeRows.getD i.val 0 ≠ 0 := by
        apply (stockPositive (slot R) i).mpr
        obtain ⟨u, hu, hr⟩ := (ev _).mp (Finset.mem_filter.mp hi).2 R R.2
        rw [slotEq]
        rcases (pairInput_true _ _ _).mp hr with eq | eq
        · exact Or.inl (eq ▸ hu)
        · exact Or.inr (eq ▸ hu)
      rw [(correctCompatibility i (slot R)).1]
      change (!demands (slot R) i && decide _) = true
      rw [hDemand, decide_eq_true hHit]
      rfl
    · intro i hi s hs
      obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hs
      have hDemand : demands (slot R) i = false :=
        (Classical.choose_spec (hslot R)).2 i ((codeMem i).mp hi)
      rw [(correctCompatibility i (slot R)).2]
      change (!demands (slot R) i) = true
      rw [hDemand]
      rfl
  let S (g : ℕ) := if hg : g ∈ indices then Classical.choose (clauses g hg) else ∅
  have spec (g) (hg : g ∈ indices) :
      safe (S g) ∧ (∀ j ∈ A g, accepts (S g) j) ∧ ∀ j ∈ U, avoids (S g) j := by
    simp only [S, dite_eq_left hg]
    exact Classical.choose_spec (clauses g hg)
  have bound := collective indices U A S covers
    (fun _ _ => Finset.filter_subset _ _) (fun g hg => (spec g hg).2.1)
    (fun g hg => (spec g hg).1) (fun g hg => (spec g hg).2.2)
  rw [ucard] at bound
  have cc : indices.card ≤ (centreless graph C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

end PEqualNP.Outside.L_meta_18392.Zero

set_option maxRecDepth 32768 in
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18392 : (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;       have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;       have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;       have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;       (2 : ℕ) ≤ x6.card → (3 : ℕ) ≤ x8.card → x7.card = (0 : ℕ) ∨ x7.card = (1 : ℕ) ∧ x5.card = (0 : ℕ) → (2 : ℕ) * x8.card ≤ x9) := by
  intro G C least top Z J R U B dirty many low
  rcases low with zero | ⟨one, allRegular⟩
  · have none : orN G C \ lam G C = ∅ := Finset.card_eq_zero.mp zero
    have enough := PEqualNP.Outside.L_meta_18392.Zero.excludes least top dirty none
    change R.card = 0 at zero
    change 2 * U.card ≤ 2 * Z.card + J.card at enough
    change 2 * U.card ≤ 2 * Z.card + J.card + R.card
    omega
  · have noFour : NoFourCycle G := by
      dsimp only [G]
      decide +kernel
    have noCentreless : centreless G C = ∅ := Finset.card_eq_zero.mp allRegular
    exact PEqualNP.Outside.L_meta_18392.Mix.oneMixingPays (h₄ := noFour) least top many noCentreless one
