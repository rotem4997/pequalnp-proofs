import Mathlib
import PEqualNP.Defs

/- The rectangle bound and its auxiliary declarations below are adapted from
   lean/PEqualNP/Outside/L_meta_8197.lean at commit b2070cb63206b2409ff4b63813e94fa446e5edaa in open-goat/pequalnp-proofs
   (Apache-2.0). The final specialization proves the distinct desk statement 8393. -/

namespace PEqualNP.Outside.L_meta_8393

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

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

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
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
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

open PEqualNP.TopForm in
lemma junk_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (hk : k ∈ junk G C) : k < C.gates.length ∧ (gateAt C k).op = GateOp.and := by
  have hjm := hk
  unfold junk gatesWhere at hjm
  obtain ⟨hlen0, hdirty⟩ := Finset.mem_filter.mp hjm
  exact ⟨Finset.mem_range.mp hlen0, hdirty.1⟩

open PEqualNP.TopForm in
lemma and_val2 {n : ℕ} (C : Circuit) (hAO2 : IsAO2 n C) (h : ℕ) (hlen : h < C.gates.length)
    (hand : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C h x = true ↔
      (val C (List.ofFn x) (opnd C h 0) = true ∧ val C (List.ofFn x) (opnd C h 1) = true) := by
  obtain ⟨_, hRB, h2⟩ := hAO2
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hlen))
  have e0 : opnd C h 0 = p := by simp [opnd, hin]
  have e1 : opnd C h 1 = q := by simp [opnd, hin]
  have hpin : p ∈ (gateAt C h).inputs := by rw [hin]; simp
  have hqin : q ∈ (gateAt C h).inputs := by rw [hin]; simp
  have hp : p < n + h := hRB h hlen p hpin
  have hq : q < n + h := hRB h hlen q hqin
  rw [gateVal_eq_val, val_and (n := n) (by simp) hlen hand, hin, e0, e1]
  constructor
  · intro hall
    exact ⟨(hall p (by simp)).2, (hall q (by simp)).2⟩
  · rintro ⟨h1, h2'⟩ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, h1⟩
    · exact ⟨hq, h2'⟩

open PEqualNP.TopForm in
lemma junk_rect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (h : ℕ) (hj : h ∈ junk G C) (x : Fin n → Bool)
    (hx : (∃ a ∈ side (n := n) C h 0, x a = true) ∧ (∃ b ∈ side (n := n) C h 1, x b = true)) :
    gateVal n C h x = true := by
  obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := hx
  obtain ⟨hlen, hand⟩ := junk_lt G C h hj
  exact (and_val2 C hAO2 h hlen hand x).mpr
    ⟨reach_var_val x _ a (mem_orIn_reach a ha) hax, reach_var_val x _ b (mem_orIn_reach b hb) hbx⟩

open PEqualNP.TopForm in
lemma top_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (t : ℕ) (ht : t ∈ tops G C) (x : Fin n → Bool)
    (h0 : val C (List.ofFn x) (opnd C t 0) = true)
    (h1 : val C (List.ofFn x) (opnd C t 1) = true) : graphFun G ∅ x = true := by
  obtain ⟨_, hRB, h2⟩ := hAO2
  have htm := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htm
  obtain ⟨hlen, hand, hbel⟩ := htm
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hlen))
  have e0 : opnd C t 0 = p := by simp [opnd, hin]
  have e1 : opnd C t 1 = q := by simp [opnd, hin]
  rw [e0] at h0
  rw [e1] at h1
  apply hbel x
  show val C (List.ofFn x) (n + t) = true
  rw [val_and (n := n) (by simp) hlen hand, hin]
  intro i hi
  have hlt : i < n + t := hRB t hlen i (by rw [hin]; exact hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hlt, h0⟩
  · exact ⟨hlt, h1⟩

open PEqualNP.TopForm in
lemma side_leaf {n : ℕ} (C : Circuit) (t : ℕ) (i : Fin 2) (s : Fin n)
    (hs : s ∈ side (n := n) C t i) (x : Fin n → Bool) (hx : x s = true) :
    val C (List.ofFn x) (opnd C t i) = true :=
  reach_var_val x _ s (mem_orIn_reach s hs) hx

lemma junk_leaf {n : ℕ} (C : Circuit) (w k : ℕ) (hr : OrReaches n C w k) (x : Fin n → Bool)
    (hv : gateVal n C k x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach k w hr).1 hv

lemma fin2_sub (i : Fin 2) :
    (i = 0 ∧ (1 : Fin 2) - i = 1) ∨ (i = 1 ∧ (1 : Fin 2) - i = 0) := by
  revert i; decide

lemma common_unique {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (z z' x y : Fin n) (h1 : G.Adj z x) (h2 : G.Adj z y) (h3 : G.Adj z' x) (h5 : G.Adj z' y)
    (hxy : x ≠ y) : z = z' := by
  by_contra hzz
  exact h4 z x z' y hzz hxy ⟨h1, h3.symm, h5, h2.symm⟩

lemma fibre_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (Pset Q : Finset (Fin n)) (k : ℕ) (Z : Finset (Fin n × Fin n))
    (hZ : ∀ zv ∈ Z, G.Adj zv.1 zv.2 ∧ zv.2 ∈ Pset ∧ zv.2 ∈ Q ∧
      (∀ v' ∈ Pset, G.Adj zv.1 v' → v' = zv.2) ∧
      (∃ b ∈ Q, b ≠ zv.2 ∧ G.Adj zv.1 b) ∧ (Q.filter (fun x => ¬ G.Adj zv.1 x)).card ≤ k) :
    Z.card ≤ (2 * k + 1) ^ 2 := by
  classical
  by_cases hsame : ∀ zv ∈ Z, ∀ zv' ∈ Z, zv.1 = zv'.1
  · have h1 : Z.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro zv hzv zv' hzv'
      have e1 := hsame zv hzv zv' hzv'
      obtain ⟨_, _, _, hu, _, _⟩ := hZ zv hzv
      obtain ⟨hadj', hmem', _, _, _, _⟩ := hZ zv' hzv'
      have e2 : zv'.2 = zv.2 := hu zv'.2 hmem' (by rw [e1]; exact hadj')
      exact Prod.ext e1 e2.symm
    exact h1.trans (Nat.one_le_pow _ _ (by omega))
  · obtain ⟨z1, hA⟩ := not_forall.mp hsame
    obtain ⟨hz1, hB⟩ := Classical.not_imp.mp hA
    obtain ⟨z2, hD⟩ := not_forall.mp hB
    obtain ⟨hz2, hne⟩ := Classical.not_imp.mp hD
    obtain ⟨_, _, _, _, _, hd1⟩ := hZ z1 hz1
    obtain ⟨_, _, _, _, _, hd2⟩ := hZ z2 hz2
    have hcn : (Q.filter (fun x => G.Adj z1.1 x ∧ G.Adj z2.1 x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter] at hx hy
      by_contra hxy
      exact hne (common_unique G h4 z1.1 z2.1 x y hx.2.1 hy.2.1 hx.2.2 hy.2.2 hxy)
    have hsub : Q ⊆ (Q.filter (fun x => ¬ G.Adj z1.1 x)) ∪ (Q.filter (fun x => ¬ G.Adj z2.1 x)) ∪
        (Q.filter (fun x => G.Adj z1.1 x ∧ G.Adj z2.1 x)) := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases a1 : G.Adj z1.1 x
      · by_cases a2 : G.Adj z2.1 x
        · exact Or.inr ⟨hx, a1, a2⟩
        · exact Or.inl (Or.inr ⟨hx, a2⟩)
      · exact Or.inl (Or.inl ⟨hx, a1⟩)
    have hQ : Q.card ≤ 2 * k + 1 := by
      have u0 := Finset.card_le_card hsub
      have u1 := Finset.card_union_le
        ((Q.filter (fun x => ¬ G.Adj z1.1 x)) ∪ (Q.filter (fun x => ¬ G.Adj z2.1 x)))
        (Q.filter (fun x => G.Adj z1.1 x ∧ G.Adj z2.1 x))
      have u2 := Finset.card_union_le (Q.filter (fun x => ¬ G.Adj z1.1 x))
        (Q.filter (fun x => ¬ G.Adj z2.1 x))
      omega
    have hw : ∀ zv : Fin n × Fin n, ∃ b : Fin n, zv ∈ Z →
        (b ∈ Q ∧ b ≠ zv.2 ∧ G.Adj zv.1 b) := by
      intro zv
      by_cases hz : zv ∈ Z
      · obtain ⟨_, _, _, _, ⟨b, hb⟩, _⟩ := hZ zv hz
        exact ⟨b, fun _ => hb⟩
      · exact ⟨zv.1, fun h => absurd h hz⟩
    choose bw hbw using hw
    have hinj : Z.card ≤ (Q ×ˢ Q).card := by
      apply Finset.card_le_card_of_injOn (fun zv => (zv.2, bw zv))
      · intro zv hzv
        have hzv' := Finset.mem_coe.mp hzv
        obtain ⟨_, _, hm, _, _, _⟩ := hZ zv hzv'
        exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hm, (hbw zv hzv').1⟩)
      · intro zv hzv zv' hzv' heq
        have hzvm := Finset.mem_coe.mp hzv
        have hzvm' := Finset.mem_coe.mp hzv'
        have e2 : zv.2 = zv'.2 := congrArg Prod.fst heq
        have e3 : bw zv = bw zv' := congrArg Prod.snd heq
        obtain ⟨ha, _, _, _, _, _⟩ := hZ zv hzvm
        obtain ⟨ha', _, _, _, _, _⟩ := hZ zv' hzvm'
        obtain ⟨_, hb2, hb3⟩ := hbw zv hzvm
        obtain ⟨_, _, hb3'⟩ := hbw zv' hzvm'
        have e1 : zv.1 = zv'.1 :=
          common_unique G h4 zv.1 zv'.1 zv.2 (bw zv) ha hb3 (by rw [e2]; exact ha')
            (by rw [e3]; exact hb3') (Ne.symm hb2)
        exact Prod.ext e1 e2
    rw [Finset.card_product] at hinj
    calc Z.card ≤ Q.card * Q.card := hinj
      _ ≤ (2 * k + 1) * (2 * k + 1) := Nat.mul_le_mul hQ hQ
      _ = (2 * k + 1) ^ 2 := by ring

lemma orIn_input {n : ℕ} (C : Circuit) (v b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C v.val) : b = v := by
  have hr := mem_orIn_reach b hb
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hstep, _⟩
  · exact Fin.ext h.symm
  · obtain ⟨k, _, hk, _, _, _⟩ := hstep
    have := v.isLt
    omega

lemma orIn_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    PEqualNP.TopForm.orIn n C w' ⊆ PEqualNP.TopForm.orIn n C w := by
  intro u hu
  exact reach_mem_orIn u (h.trans (mem_orIn_reach u hu))

lemma chain_split {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (z v : Fin n) :
    ∀ w : ℕ, v ∈ PEqualNP.TopForm.orIn n C w →
      (∃ b ∈ PEqualNP.TopForm.orIn n C w, b ≠ v ∧ G.Adj z b) →
      ∃ g c : ℕ, g < C.gates.length ∧ c ∈ (gateAt C g).inputs ∧
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧
        v ∈ PEqualNP.TopForm.orIn n C c ∧ v ∈ PEqualNP.TopForm.orIn n C (n + g) ∧
        (∀ v' ∈ PEqualNP.TopForm.orIn n C c, G.Adj z v' → v' = v) ∧
        (∃ b ∈ PEqualNP.TopForm.orIn n C (n + g), b ≠ v ∧ G.Adj z b) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hb
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with h | ⟨c, hstep, hrest⟩
    · exfalso
      obtain ⟨b, hbm, hbne, _⟩ := hb
      rw [h] at hbm
      exact hbne (orIn_input C v b hbm)
    · obtain ⟨g, hg, hwg, hop, hin, hlt⟩ := hstep
      have hvc : v ∈ PEqualNP.TopForm.orIn n C c := reach_mem_orIn v hrest
      by_cases huniq : ∀ v' ∈ PEqualNP.TopForm.orIn n C c, G.Adj z v' → v' = v
      · subst hwg
        exact ⟨g, c, hg, hin, Relation.ReflTransGen.refl, hvc, hv, huniq, hb⟩
      · obtain ⟨v', h1⟩ := not_forall.mp huniq
        obtain ⟨hv'm, h2⟩ := Classical.not_imp.mp h1
        obtain ⟨hadj, hne⟩ := Classical.not_imp.mp h2
        obtain ⟨g', c', hg', hin', hr', hvc', hvg', hu', hb'⟩ :=
          ih c (by omega) hvc ⟨v', hv'm, hne, hadj⟩
        exact ⟨g', c', hg', hin',
          Relation.ReflTransGen.head ⟨g, hg, hwg, hop, hin, hlt⟩ hr', hvc', hvg', hu', hb'⟩

def slots (C : Circuit) : Finset (ℕ × ℕ) :=
  (Finset.range C.gates.length).biUnion fun g =>
    (gateAt C g).inputs.toFinset.image fun c => (g, c)

lemma slots_card (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (slots C).card ≤ 2 * C.gates.length := by
  unfold slots
  calc ((Finset.range C.gates.length).biUnion fun g =>
        (gateAt C g).inputs.toFinset.image fun c => (g, c)).card
      ≤ ∑ g ∈ Finset.range C.gates.length,
          ((gateAt C g).inputs.toFinset.image fun c => (g, c)).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ Finset.range C.gates.length, 2 := Finset.sum_le_sum (fun g hg => by
        have hlt := Finset.mem_range.mp hg
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (h2 _ (gateAt_mem hlt))))
    _ = 2 * C.gates.length := by simp [mul_comm]

lemma charge_dirt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (k : ℕ)
    (P : Finset (Fin n × Fin n))
    (hP : ∀ zv ∈ P, G.Adj zv.1 zv.2 ∧ ∃ w : ℕ, zv.2 ∈ PEqualNP.TopForm.orIn n C w ∧
      (∃ b ∈ PEqualNP.TopForm.orIn n C w, b ≠ zv.2 ∧ G.Adj zv.1 b) ∧
      ((PEqualNP.TopForm.orIn n C w).filter (fun x => ¬ G.Adj zv.1 x)).card ≤ k) :
    P.card ≤ (2 * k + 1) ^ 2 * (2 * C.gates.length) := by
  classical
  have hslot : ∀ zv : Fin n × Fin n, ∃ gc : ℕ × ℕ, zv ∈ P →
      (gc ∈ slots C ∧ zv.2 ∈ PEqualNP.TopForm.orIn n C gc.2 ∧
        zv.2 ∈ PEqualNP.TopForm.orIn n C (n + gc.1) ∧
        (∀ v' ∈ PEqualNP.TopForm.orIn n C gc.2, G.Adj zv.1 v' → v' = zv.2) ∧
        (∃ b ∈ PEqualNP.TopForm.orIn n C (n + gc.1), b ≠ zv.2 ∧ G.Adj zv.1 b) ∧
        ((PEqualNP.TopForm.orIn n C (n + gc.1)).filter (fun x => ¬ G.Adj zv.1 x)).card ≤ k) := by
    intro zv
    by_cases hz : zv ∈ P
    · obtain ⟨_, w, hv, hb, hk⟩ := hP zv hz
      obtain ⟨g, c, hg, hin, hr, hvc, hvg, hu, hb'⟩ := chain_split G C zv.1 zv.2 w hv hb
      refine ⟨(g, c), fun _ => ⟨?_, hvc, hvg, hu, hb', ?_⟩⟩
      · unfold slots
        exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_range.mpr hg,
          Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hin, rfl⟩⟩
      · exact (Finset.card_le_card (Finset.filter_subset_filter _ (orIn_mono hr))).trans hk
    · exact ⟨(0, 0), fun h => absurd h hz⟩
  choose f hf using hslot
  refine (Finset.card_le_mul_card_image_of_maps_to (f := f) (t := slots C)
    (fun zv hzv => (hf zv hzv).1) ((2 * k + 1) ^ 2) ?_).trans
    (Nat.mul_le_mul_left _ (slots_card C h2))
  intro gc _
  apply fibre_bound G h4 (PEqualNP.TopForm.orIn n C gc.2)
    (PEqualNP.TopForm.orIn n C (n + gc.1)) k
  intro zv hzv
  rw [Finset.mem_filter] at hzv
  obtain ⟨hzP, hfz⟩ := hzv
  obtain ⟨_, h1, h1', h3, h5, h6⟩ := hf zv hzP
  rw [hfz] at h1 h1' h3 h5 h6
  exact ⟨(hP zv hzP).1, h1, h1', h3, h5, h6⟩

def Fires (n : ℕ) (C : Circuit) (w : ℕ) (u : Fin n) : Prop :=
  ∀ X : Fin n → Bool, X u = true → val C (List.ofFn X) w = true

open PEqualNP.TopForm in
lemma fires_side {n : ℕ} (C : Circuit) (t : ℕ) (i : Fin 2) (u : Fin n)
    (hu : u ∈ side (n := n) C t i) : Fires n C (opnd C t i) u :=
  fun X hX => side_leaf C t i u hu X hX

open PEqualNP.TopForm in
lemma clean_rect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u : Fin n) (hu : Fires n C (opnd C t i) u)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (b c : Fin n) (hb : b ∈ side (n := n) C k 0) (hc : c ∈ side (n := n) C k 1)
    (hub : ¬ G.Adj u b) (huc : ¬ G.Adj u c) : G.Adj b c := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ w : Fin n, X w = true ↔ (w = u ∨ w = b ∨ w = c) :=
    ⟨fun w => decide (w = u ∨ w = b ∨ w = c), fun w => by simp⟩
  have hkv : gateVal n C k X = true :=
    (junk_rect G C hAO2 k hk X)
      ⟨⟨b, hb, (hx b).mpr (Or.inr (Or.inl rfl))⟩, ⟨c, hc, (hx c).mpr (Or.inr (Or.inr rfl))⟩⟩
  have hsv := hu X ((hx u).mpr (Or.inl rfl))
  have hjv := junk_leaf C _ k hor X hkv
  have hF : graphFun G ∅ X = true := by
    rcases fin2_sub i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · rw [hi] at hsv; rw [hi'] at hjv
      exact top_sound G C hAO2 t ht X hsv hjv
    · rw [hi] at hsv; rw [hi'] at hjv
      exact top_sound G C hAO2 t ht X hjv hsv
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  rcases (hx y).mp hy with e1 | e1 | e1 <;> rcases (hx z).mp hz with e2 | e2 | e2 <;>
    rw [e1, e2] at hyz
  · exact (G.irrefl hyz).elim
  · exact absurd hyz hub
  · exact absurd hyz huc
  · exact absurd hyz.symm hub
  · exact (G.irrefl hyz).elim
  · exact hyz
  · exact absurd hyz.symm huc
  · exact hyz.symm
  · exact (G.irrefl hyz).elim

lemma dirt_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (u : Fin n) (S T : Finset (Fin n))
    (h : ∀ b ∈ S, ∀ c ∈ T, ¬ G.Adj u b → ¬ G.Adj u c → G.Adj b c) :
    (S.filter (fun y => ¬ G.Adj u y)).card ≤ 1 ∨ (T.filter (fun y => ¬ G.Adj u y)).card ≤ 1 :=
  biclique_star G h4 _ _ (fun a ha b hb => by
    rw [Finset.mem_filter] at ha hb
    exact h a ha.1 b hb.1 ha.2 hb.2)

def O1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (X : Finset (Fin n)) : Prop :=
  v ∈ X ∧ (∃ b ∈ X, b ≠ v ∧ G.Adj u b) ∧ (X.filter (fun y => ¬ G.Adj u y)).card ≤ 1

def O2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : ℕ) (u v : Fin n)
    (X Y : Finset (Fin n)) : Prop :=
  Y = {v} ∧ u ∈ X ∧ (∃ b ∈ X, b ≠ u ∧ G.Adj v b) ∧ (X.filter (fun y => ¬ G.Adj v y)).card ≤ K

def O3 {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (X Y : Finset (Fin n)) : Prop :=
  Y = {v} ∧ u ∈ X ∧ ∀ y ∈ X, G.Adj v y → y = u

def O4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : ℕ) (u v : Fin n)
    (X Y : Finset (Fin n)) : Prop :=
  Y = {v} ∧ u ∈ X ∧ v ∉ X ∧ (∃ b ∈ X, b ≠ u ∧ G.Adj v b) ∧
    K < (X.filter (fun y => ¬ G.Adj v y)).card

def O5 {n : ℕ} (v : Fin n) (S T : Finset (Fin n)) : Prop :=
  v ∈ S ∧ v ∈ T ∧ ∀ y ∈ S, y ∈ T → y = v

lemma classD_case2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : ℕ)
    (u v : Fin n) (S T : Finset (Fin n))
    (hclean : ∀ b ∈ S, ∀ c ∈ T, ¬ G.Adj u b → ¬ G.Adj u c → G.Adj b c)
    (huS : u ∈ S) (hvT : v ∈ T) (hvS : v ∉ S) :
    O1 G u v T ∨ O2 G K u v S T ∨ O3 G u v S T ∨ O4 G K u v S T := by
  classical
  have hTN : ∀ c ∈ T, G.Adj u c := by
    intro c hc
    by_contra hnc
    exact hnc (hclean u huS c hc G.irrefl hnc)
  by_cases h2 : ∃ b ∈ T, b ≠ v
  · obtain ⟨b, hb, hbv⟩ := h2
    left
    refine ⟨hvT, ⟨b, hb, hbv, hTN b hb⟩, ?_⟩
    have he : T.filter (fun y => ¬ G.Adj u y) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun y hy => not_not.mpr (hTN y hy))
    rw [he]; simp
  · have hT1 : T = {v} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        by_contra hyv
        exact h2 ⟨y, hy, hyv⟩
      · intro hy
        rw [hy]; exact hvT
    right
    by_cases h3 : ∃ b ∈ S, b ≠ u ∧ G.Adj v b
    · by_cases h5 : (S.filter (fun y => ¬ G.Adj v y)).card ≤ K
      · exact Or.inl ⟨hT1, huS, h3, h5⟩
      · exact Or.inr (Or.inr ⟨hT1, huS, hvS, h3, by omega⟩)
    · refine Or.inr (Or.inl ⟨hT1, huS, ?_⟩)
      intro y hy hadj
      by_contra hyu
      exact h3 ⟨y, hy, hyu, hadj⟩

lemma classD_abs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (K : ℕ) (u v : Fin n) (S T : Finset (Fin n))
    (hclean : ∀ b ∈ S, ∀ c ∈ T, ¬ G.Adj u b → ¬ G.Adj u c → G.Adj b c)
    (hS : u ∈ S ∨ v ∈ S) (hT : u ∈ T ∨ v ∈ T) :
    (O1 G u v S ∨ O1 G u v T) ∨ (O2 G K u v S T ∨ O2 G K u v T S) ∨
      (O3 G u v S T ∨ O3 G u v T S) ∨ (O4 G K u v S T ∨ O4 G K u v T S) ∨ O5 v S T := by
  classical
  have hclean' : ∀ b ∈ T, ∀ c ∈ S, ¬ G.Adj u b → ¬ G.Adj u c → G.Adj b c :=
    fun b hb c hc h1 h2 => (hclean c hc b hb h2 h1).symm
  have hnot : ¬ (u ∈ S ∧ u ∈ T) :=
    fun h => G.irrefl (hclean u h.1 u h.2 G.irrefl G.irrefl)
  by_cases hv : v ∈ S ∧ v ∈ T
  · by_cases h1 : ∀ y ∈ S, y ∈ T → y = v
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hv.1, hv.2, h1⟩)))
    · obtain ⟨y, hy1⟩ := not_forall.mp h1
      obtain ⟨hyS, hy2⟩ := Classical.not_imp.mp hy1
      obtain ⟨hyT, hyv⟩ := Classical.not_imp.mp hy2
      have hadj : G.Adj u y := by
        by_contra hn
        exact G.irrefl (hclean y hyS y hyT hn hn)
      left
      rcases dirt_star G h4 u S T hclean with hd | hd
      · exact Or.inl ⟨hv.1, ⟨y, hyS, hyv, hadj⟩, hd⟩
      · exact Or.inr ⟨hv.2, ⟨y, hyT, hyv, hadj⟩, hd⟩
  · rcases hS with huS | hvS
    · rcases hT with huT | hvT
      · exact absurd ⟨huS, huT⟩ hnot
      · have hvS : v ∉ S := fun h => hv ⟨h, hvT⟩
        rcases classD_case2 G K u v S T hclean huS hvT hvS with h | h | h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
    · rcases hT with huT | hvT
      · have hvT : v ∉ T := fun h => hv ⟨hvS, h⟩
        rcases classD_case2 G K u v T S hclean' huT hvS hvT with h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
      · exact absurd ⟨hvS, hvT⟩ hv

open PEqualNP.TopForm in
lemma classD_cases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u : Fin n) (hu : Fires n C (opnd C t i) u)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (v : Fin n) (hr0 : u ∈ side (n := n) C k 0 ∨ v ∈ side (n := n) C k 0)
    (hr1 : u ∈ side (n := n) C k 1 ∨ v ∈ side (n := n) C k 1) :
    (O1 G u v (side (n := n) C k 0) ∨ O1 G u v (side (n := n) C k 1)) ∨
      (O2 G K u v (side (n := n) C k 0) (side (n := n) C k 1) ∨
        O2 G K u v (side (n := n) C k 1) (side (n := n) C k 0)) ∨
      (O3 G u v (side (n := n) C k 0) (side (n := n) C k 1) ∨
        O3 G u v (side (n := n) C k 1) (side (n := n) C k 0)) ∨
      (O4 G K u v (side (n := n) C k 0) (side (n := n) C k 1) ∨
        O4 G K u v (side (n := n) C k 1) (side (n := n) C k 0)) ∨
      O5 v (side (n := n) C k 0) (side (n := n) C k 1) :=
  classD_abs G h4 K u v _ _
    (fun b hb c hc => clean_rect G C hAO2 t ht i u hu k hk hor b c hb hc) hr0 hr1

def CD {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (z x : Fin n) : Prop :=
  G.Adj z x ∧ ∃ w : ℕ, x ∈ PEqualNP.TopForm.orIn n C w ∧
    (∃ b ∈ PEqualNP.TopForm.orIn n C w, b ≠ x ∧ G.Adj z b) ∧
    ((PEqualNP.TopForm.orIn n C w).filter (fun y => ¬ G.Adj z y)).card ≤ K

lemma cd_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {K K' : ℕ} (hK : K ≤ K') {z x : Fin n} (h : CD G C K z x) : CD G C K' z x := by
  obtain ⟨h1, w, h2, h3, h5⟩ := h
  exact ⟨h1, w, h2, h3, h5.trans hK⟩

open PEqualNP.TopForm in
lemma cd_of_O1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (k : ℕ) (j : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (h : O1 G u v (side (n := n) C k j)) : CD G C 1 u v :=
  ⟨huv, opnd C k j, h.1, h.2.1, h.2.2⟩

open PEqualNP.TopForm in
lemma cd_of_O2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (k : ℕ) (j : Fin 2) (Y : Finset (Fin n)) (u v : Fin n) (huv : G.Adj u v)
    (h : O2 G K u v (side (n := n) C k j) Y) : CD G C K v u :=
  ⟨huv.symm, opnd C k j, h.2.1, h.2.2.1, h.2.2.2⟩

lemma cd_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ)
    (P : Finset (Fin n × Fin n)) (hP : ∀ zv ∈ P, CD G C K zv.1 zv.2) :
    P.card ≤ (2 * K + 1) ^ 2 * (2 * C.gates.length) :=
  charge_dirt G h4 C h2 K P hP

def Bnd {n : ℕ} (R : Fin n → Fin n → Prop) (c : ℕ) : Prop :=
  ∀ P : Finset (Fin n × Fin n), (∀ zv ∈ P, R zv.1 zv.2) → P.card ≤ c

lemma bnd_le {n : ℕ} {R : Fin n → Fin n → Prop} {c c' : ℕ} (hc : c ≤ c') (hb : Bnd R c) :
    Bnd R c' :=
  fun P hP => (hb P hP).trans hc

lemma bnd_or {n : ℕ} {R R' : Fin n → Fin n → Prop} {a b : ℕ} (ha : Bnd R a) (hb : Bnd R' b) :
    Bnd (fun x y => R x y ∨ R' x y) (a + b) := by
  classical
  intro P hP
  have h1 := ha (P.filter (fun zv => R zv.1 zv.2)) (fun zv hzv => (Finset.mem_filter.mp hzv).2)
  have h2 := hb (P.filter (fun zv => ¬ R zv.1 zv.2)) (fun zv hzv => by
    obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hzv
    rcases hP zv hm with h | h
    · exact absurd h hn
    · exact h)
  have h3 := Finset.card_filter_add_card_filter_not (s := P) (fun zv => R zv.1 zv.2)
  omega

lemma bnd_swap {n : ℕ} {R : Fin n → Fin n → Prop} {c : ℕ} (hb : Bnd R c) :
    Bnd (fun x y => R y x) c := by
  classical
  intro P hP
  have h := hb (P.image Prod.swap) (fun zv hzv => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzv
    exact hP w hw)
  rwa [Finset.card_image_of_injective _ Prod.swap_injective] at h

lemma obj_count {n : ℕ} {ι : Type} (O : Finset ι) (m : ℕ) (Rel : ι → Fin n → Fin n → Prop)
    (hfib : ∀ o ∈ O, Bnd (Rel o) m) : Bnd (fun x y => ∃ o ∈ O, Rel o x y) (m * O.card) := by
  classical
  intro P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨o0, _, _⟩ := hP zv0 hzv0
    have hch : ∀ zv : Fin n × Fin n, ∃ o : ι, zv ∈ P → (o ∈ O ∧ Rel o zv.1 zv.2) := by
      intro zv
      by_cases hz : zv ∈ P
      · obtain ⟨o, ho, hr⟩ := hP zv hz
        exact ⟨o, fun _ => ⟨ho, hr⟩⟩
      · exact ⟨o0, fun h => absurd h hz⟩
    choose f hf using hch
    refine Finset.card_le_mul_card_image_of_maps_to (f := f) (t := O)
      (fun zv hzv => (hf zv hzv).1) m ?_
    intro o ho
    apply hfib o ho
    intro zv hzv
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hzv
    have := (hf zv hm).2
    rwa [he] at this

lemma edges_bnd {n : ℕ} (R : Fin n → Fin n → Prop) (c : ℕ) (hb : Bnd R c)
    (F : Finset (Sym2 (Fin n))) (hF : ∀ e ∈ F, ∃ a b : Fin n, e = s(a, b) ∧ R a b) :
    F.card ≤ c := by
  classical
  have hch : ∀ e : Sym2 (Fin n), ∃ ab : Fin n × Fin n,
      e ∈ F → (e = s(ab.1, ab.2) ∧ R ab.1 ab.2) := by
    intro e
    by_cases he : e ∈ F
    · obtain ⟨a, b, h1, h2⟩ := hF e he
      exact ⟨(a, b), fun _ => ⟨h1, h2⟩⟩
    · induction e using Sym2.inductionOn with
      | hf a b => exact ⟨(a, b), fun h => absurd h he⟩
  choose f hf using hch
  have h1 : F.card ≤ (F.image f).card := by
    rw [Finset.card_image_of_injOn]
    intro e he e' he' heq
    have a1 := (hf e (Finset.mem_coe.mp he)).1
    have a2 := (hf e' (Finset.mem_coe.mp he')).1
    rw [a1, a2, heq]
  exact h1.trans (hb (F.image f) (fun zv hzv => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hzv
    exact (hf e he).2))

noncomputable def Lw (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => Fires n C w x)

lemma mem_Lw {n : ℕ} {C : Circuit} {w : ℕ} {x : Fin n} : x ∈ Lw n C w ↔ Fires n C w x := by
  classical
  simp [Lw]

lemma fires_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') {x : Fin n} (hx : Fires n C w' x) :
    Fires n C w x :=
  fun X hX => orStep_up (n := n) (by simp) h (hx X hX)

lemma Lw_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : Lw n C w' ⊆ Lw n C w :=
  fun _ hx => mem_Lw.mpr (fires_mono h (mem_Lw.mp hx))

lemma fires_input {n : ℕ} (C : Circuit) (u x : Fin n) : Fires n C u.val x ↔ x = u := by
  constructor
  · intro h
    have h1 := h (pairInput x x) (pairInput_left x x)
    rw [val_ofFn] at h1
    rcases (pairInput_true x x u).mp h1 with e | e
    · exact e.symm
    · exact e.symm
  · intro h X hX
    rw [val_ofFn, ← h]; exact hX

open PEqualNP.TopForm in
lemma fires_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (x y : Fin n)
    (hx : Fires n C (opnd C t i) x) (hy : Fires n C (opnd C t ((1 : Fin 2) - i)) y) :
    G.Adj x y := by
  have h1 := hx (pairInput x y) (pairInput_left x y)
  have h2 := hy (pairInput x y) (pairInput_right x y)
  have hF : graphFun G ∅ (pairInput x y) = true := by
    rcases fin2_sub i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · rw [hi] at h1; rw [hi'] at h2
      exact top_sound G C hAO2 t ht _ h1 h2
    · rw [hi] at h1; rw [hi'] at h2
      exact top_sound G C hAO2 t ht _ h2 h1
  exact (graphFun_pair G x y).mp hF

lemma path_split {n : ℕ} (C : Circuit) (Big : ℕ → Prop) (τ : ℕ) (hτ : ¬ Big τ) :
    ∀ w : ℕ, Relation.ReflTransGen (OrStep n C) w τ → Big w →
      ∃ g c : ℕ, g < C.gates.length ∧ c ∈ (gateAt C g).inputs ∧
        Relation.ReflTransGen (OrStep n C) w (n + g) ∧
        Relation.ReflTransGen (OrStep n C) (n + g) c ∧
        Relation.ReflTransGen (OrStep n C) c τ ∧ Big (n + g) ∧ ¬ Big c := by
  intro w h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro hb; exact absurd hb hτ
  | @head a c hstep hrest ih =>
    intro hb
    by_cases hc : Big c
    · obtain ⟨g', c', hg', hin', hr1, hr2, hr3, hb1, hb2⟩ := ih hc
      exact ⟨g', c', hg', hin', Relation.ReflTransGen.head hstep hr1, hr2, hr3, hb1, hb2⟩
    · obtain ⟨g, hg, hag, hop, hin, hlt⟩ := hstep
      subst hag
      exact ⟨g, c, hg, hin, Relation.ReflTransGen.refl,
        Relation.ReflTransGen.single ⟨g, hg, rfl, hop, hin, hlt⟩, hrest, hb, hc⟩

def CDL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (z x : Fin n) : Prop :=
  ∃ gc ∈ slots C, G.Adj z x ∧ x ∈ Lw n C gc.2 ∧ x ∈ Lw n C (n + gc.1) ∧
    (∀ y ∈ Lw n C gc.2, G.Adj z y → y = x) ∧
    (∃ b ∈ Lw n C (n + gc.1), b ≠ x ∧ G.Adj z b) ∧
    ((Lw n C (n + gc.1)).filter (fun y => ¬ G.Adj z y)).card ≤ K

lemma cdl_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) :
    Bnd (CDL G C K) ((2 * K + 1) ^ 2 * (2 * C.gates.length)) := by
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  unfold CDL
  apply obj_count (slots C) ((2 * K + 1) ^ 2)
  intro gc _ P hP
  exact fibre_bound G h4 (Lw n C gc.2) (Lw n C (n + gc.1)) K P
    (fun zv hzv => by
      obtain ⟨a1, a2, a3, a5, a6, a7⟩ := hP zv hzv
      exact ⟨a1, a2, a3, a5, a6, a7⟩)

lemma cdl_of_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (z x : Fin n) (hzx : G.Adj z x) (p τ : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) p τ) (hxτ : x ∈ Lw n C τ)
    (hτ : ∀ y ∈ Lw n C τ, G.Adj z y → y = x)
    (hsec : ∃ b ∈ Lw n C p, b ≠ x ∧ G.Adj z b)
    (hdirt : ((Lw n C p).filter (fun y => ¬ G.Adj z y)).card ≤ K) : CDL G C K z x := by
  have hnb : ¬ (∃ b ∈ Lw n C τ, b ≠ x ∧ G.Adj z b) := by
    rintro ⟨b, hb, hbx, hzb⟩
    exact hbx (hτ b hb hzb)
  obtain ⟨g, c, hg, hin, hr1, hr2, hr3, hb1, hb2⟩ :=
    path_split C (fun w => ∃ b ∈ Lw n C w, b ≠ x ∧ G.Adj z b) τ hnb p hr hsec
  refine ⟨(g, c), ?_, hzx, Lw_mono hr3 hxτ, Lw_mono (hr2.trans hr3) hxτ, ?_, hb1, ?_⟩
  · unfold slots
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_range.mpr hg,
      Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hin, rfl⟩⟩
  · intro y hy hzy
    by_contra hyx
    exact hb2 ⟨y, hy, hyx, hzy⟩
  · exact (Finset.card_le_card (Finset.filter_subset_filter _ (Lw_mono hr1))).trans hdirt

lemma fin2_ss (i : Fin 2) : (1 : Fin 2) - ((1 : Fin 2) - i) = i := by
  revert i; decide

def TopDet (n : ℕ) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ ti ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    u ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ti.2) ∧
    v ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) ∧
    (∀ y ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ti.2), y = u) ∧
    (∀ y ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)), y = v)

lemma prod_card (m : ℕ) :
    (Finset.range m ×ˢ (Finset.univ : Finset (Fin 2))).card = 2 * m := by
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin, mul_comm]

lemma topdet_bnd (n : ℕ) (C : Circuit) : Bnd (TopDet n C) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold TopDet
  refine bnd_le (by rw [hc]; omega) (obj_count _ 1 _ ?_)
  intro ti _ P hP
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  obtain ⟨_, _, a3, a4⟩ := hP zv hzv
  obtain ⟨b1, b2, _, _⟩ := hP zv' hzv'
  exact Prod.ext (a3 zv'.1 b1).symm (a4 zv'.2 b2).symm

def LineDet {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ O3 G u v (PEqualNP.TopForm.side (n := n) C kj.1 kj.2)
      (PEqualNP.TopForm.side (n := n) C kj.1 ((1 : Fin 2) - kj.2))

lemma linedet_bnd {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    Bnd (LineDet G C) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold LineDet
  refine bnd_le (by rw [hc]; omega) (obj_count _ 1 _ ?_)
  intro kj _ P hP
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  obtain ⟨_, a1, _, a3⟩ := hP zv hzv
  obtain ⟨badj, b1, b2, _⟩ := hP zv' hzv'
  have e2 : zv.2 = zv'.2 := by
    have := a1.symm.trans b1
    exact Finset.singleton_injective this
  have e1 : zv'.1 = zv.1 := a3 zv'.1 b2 (by rw [e2]; exact badj.symm)
  exact Prod.ext e1.symm e2

open PEqualNP.TopForm in
lemma lstar_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (τu τv : ℕ)
    (hru : Relation.ReflTransGen (OrStep n C) (opnd C t i) τu) (huτ : u ∈ Lw n C τu)
    {Q : Prop} (hτu : (∀ y ∈ Lw n C τu, y = u) ∨ Q)
    (hrv : Relation.ReflTransGen (OrStep n C) (opnd C t ((1 : Fin 2) - i)) τv)
    (hvτ : v ∈ Lw n C τv) (hτv : ∀ y ∈ Lw n C τv, y = v) :
    CDL G C 0 u v ∨ CDL G C 0 v u ∨ TopDet n C u v ∨ Q := by
  classical
  have hup : u ∈ Lw n C (opnd C t i) := Lw_mono hru huτ
  have hvq : v ∈ Lw n C (opnd C t ((1 : Fin 2) - i)) := Lw_mono hrv hvτ
  have hadj : ∀ x ∈ Lw n C (opnd C t i), ∀ y ∈ Lw n C (opnd C t ((1 : Fin 2) - i)),
      G.Adj x y :=
    fun x hx y hy => fires_adj G C hAO2 t ht i x y (mem_Lw.mp hx) (mem_Lw.mp hy)
  have huv : G.Adj u v := hadj u hup v hvq
  have htm := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htm
  by_cases hq : ∃ y ∈ Lw n C (opnd C t ((1 : Fin 2) - i)), y ≠ v
  · left
    obtain ⟨y, hy, hyv⟩ := hq
    refine cdl_of_path G C 0 u v huv _ τv hrv hvτ (fun y' hy' _ => hτv y' hy')
      ⟨y, hy, hyv, hadj u hup y hy⟩ ?_
    have he : (Lw n C (opnd C t ((1 : Fin 2) - i))).filter (fun y => ¬ G.Adj u y) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun y hy => not_not.mpr (hadj u hup y hy))
    rw [he]; simp
  · by_cases hp : ∃ y ∈ Lw n C (opnd C t i), y ≠ u
    · rcases hτu with hτu | hcd
      · right; left
        obtain ⟨y, hy, hyu⟩ := hp
        refine cdl_of_path G C 0 v u huv.symm _ τu hru huτ (fun y' hy' _ => hτu y' hy')
          ⟨y, hy, hyu, (hadj y hy v hvq).symm⟩ ?_
        have he : (Lw n C (opnd C t i)).filter (fun y => ¬ G.Adj v y) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun y hy => not_not.mpr (hadj y hy v hvq).symm)
        rw [he]; simp
      · exact Or.inr (Or.inr (Or.inr hcd))
    · right; right; left
      refine ⟨(t, i), Finset.mem_product.mpr ⟨Finset.mem_range.mpr htm.1, Finset.mem_univ _⟩,
        hup, hvq, ?_, ?_⟩
      · intro y hy
        by_contra hne
        exact hp ⟨y, hy, hne⟩
      · intro y hy
        by_contra hne
        exact hq ⟨y, hy, hne⟩

lemma slot_mem (C : Circuit) {g c : ℕ} (hg : g < C.gates.length)
    (hin : c ∈ (gateAt C g).inputs) : (g, c) ∈ slots C := by
  unfold slots
  exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_range.mpr hg,
    Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hin, rfl⟩⟩

lemma fin2_ne : ∀ j j' : Fin 2, j' ≠ j → j = (1 : Fin 2) - j' := by decide

open PEqualNP.TopForm in
lemma junk_reach_self {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (k : ℕ) (hk : k ∈ junk G C) (w : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) (n + k) w) : w = n + k := by
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hstep, _⟩
  · exact h.symm
  · obtain ⟨g, _, hkg, hop, _, _⟩ := hstep
    have e : g = k := by omega
    rw [e, (junk_lt G C k hk).2] at hop
    exact GateOp.noConfusion hop

def Cl {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : Fin n)
    (r : ℕ) : Prop :=
  ∀ X : Fin n → Bool, X w = true → val C (List.ofFn X) r = true → graphFun G ∅ X = true

lemma cl_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {w : Fin n} {r r' : ℕ} (h : Cl G C w r)
    (hr : Relation.ReflTransGen (OrStep n C) r r') : Cl G C w r' :=
  fun X hw hv => h X hw (orStep_up (n := n) (by simp) hr hv)

open PEqualNP.TopForm in
lemma cl_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (w : Fin n)
    (hf : Fires n C (opnd C t i) w) : Cl G C w (opnd C t ((1 : Fin 2) - i)) := by
  intro X hw hv
  have hsv := hf X hw
  rcases fin2_sub i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
  · rw [hi] at hsv; rw [hi'] at hv
    exact top_sound G C hAO2 t ht X hsv hv
  · rw [hi] at hsv; rw [hi'] at hv
    exact top_sound G C hAO2 t ht X hv hsv

def HL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) (k : ℕ)
    (v : Fin n) : Prop :=
  k ∈ PEqualNP.TopForm.junk G C ∧ ∃ j : Fin 2,
    (PEqualNP.TopForm.side (n := n) C k ((1 : Fin 2) - j) = {v} ∨
      Lw n C (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) = {v}) ∧
    K < ((PEqualNP.TopForm.side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card

def HcP {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) (r : ℕ)
    (v : Fin n) : Prop :=
  ∃ k : ℕ, Relation.ReflTransGen (OrStep n C) r (n + k) ∧ HL G C K k v

open PEqualNP.TopForm in
lemma thin_fires {n : ℕ} (C : Circuit) (k : ℕ) (j : Fin 2) (v : Fin n)
    (hY : side (n := n) C k j = {v} ∨ Lw n C (opnd C k j) = {v}) :
    Fires n C (opnd C k j) v := by
  rcases hY with h | h
  · exact fires_side C k j v (by rw [h]; exact Finset.mem_singleton_self v)
  · exact mem_Lw.mp (by rw [h]; exact Finset.mem_singleton_self v)

open PEqualNP.TopForm in
lemma thin_side_sub {n : ℕ} (C : Circuit) (k : ℕ) (j : Fin 2) (v : Fin n)
    (hY : side (n := n) C k j = {v} ∨ Lw n C (opnd C k j) = {v}) :
    ∀ x ∈ side (n := n) C k j, x = v := by
  intro x hx
  rcases hY with h | h
  · rw [h] at hx; exact Finset.mem_singleton.mp hx
  · have hx' : x ∈ Lw n C (opnd C k j) := mem_Lw.mpr (fires_side C k j x hx)
    rw [h] at hx'; exact Finset.mem_singleton.mp hx'

open PEqualNP.TopForm in
lemma hl_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (K : ℕ) (hK : 1 ≤ K) (k : ℕ) (j j' : Fin 2) (v v' : Fin n)
    (hY : side (n := n) C k ((1 : Fin 2) - j) = {v} ∨
      Lw n C (opnd C k ((1 : Fin 2) - j)) = {v})
    (hD : K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card)
    (hY' : side (n := n) C k ((1 : Fin 2) - j') = {v'} ∨
      Lw n C (opnd C k ((1 : Fin 2) - j')) = {v'}) : v' = v := by
  classical
  by_cases hjj : j' = j
  · rw [hjj] at hY'
    rcases hY' with h' | h'
    · rcases hY with h | h
      · exact (Finset.singleton_injective (h.symm.trans h')).symm
      · have hv' : v' ∈ Lw n C (opnd C k ((1 : Fin 2) - j)) :=
          mem_Lw.mpr (thin_fires C k _ v' (Or.inl h'))
        rw [h] at hv'; exact Finset.mem_singleton.mp hv'
    · have hv : v ∈ Lw n C (opnd C k ((1 : Fin 2) - j)) :=
        mem_Lw.mpr (thin_fires C k _ v hY)
      rw [h'] at hv; exact (Finset.mem_singleton.mp hv).symm
  · have e := fin2_ne j j' hjj
    rw [← e] at hY'
    have hsub : (side (n := n) C k j).filter (fun y => ¬ G.Adj v y) ⊆ {v'} := by
      intro x hx
      exact Finset.mem_singleton.mpr
        (thin_side_sub C k j v' hY' x (Finset.mem_filter.mp hx).1)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hc
    omega

open PEqualNP.TopForm in
lemma cl_rectF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (w : Fin n) (r : ℕ) (hcl : Cl G C w r) (k : ℕ) (hk : k ∈ junk G C)
    (hr : Relation.ReflTransGen (OrStep n C) r (n + k))
    (j : Fin 2) (b c : Fin n) (hb : b ∈ side (n := n) C k j)
    (hc : Fires n C (opnd C k ((1 : Fin 2) - j)) c)
    (hwb : ¬ G.Adj w b) (hwc : ¬ G.Adj w c) : G.Adj b c := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ z : Fin n, X z = true ↔ (z = w ∨ z = b ∨ z = c) :=
    ⟨fun z => decide (z = w ∨ z = b ∨ z = c), fun z => by simp⟩
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  have hkv : gateVal n C k X = true := by
    apply (and_val2 C hAO2 k hlen hand X).mpr
    have a1 := side_leaf C k j b hb X ((hx b).mpr (Or.inr (Or.inl rfl)))
    have a2 := hc X ((hx c).mpr (Or.inr (Or.inr rfl)))
    rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
  have hF : graphFun G ∅ X = true :=
    hcl X ((hx w).mpr (Or.inl rfl)) (orStep_up (n := n) (by simp) hr hkv)
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  rcases (hx y).mp hy with e1 | e1 | e1 <;> rcases (hx z).mp hz with e2 | e2 | e2 <;>
    rw [e1, e2] at hyz
  · exact (G.irrefl hyz).elim
  · exact absurd hyz hwb
  · exact absurd hyz hwc
  · exact absurd hyz.symm hwb
  · exact (G.irrefl hyz).elim
  · exact hyz
  · exact absurd hyz.symm hwc
  · exact hyz.symm
  · exact (G.irrefl hyz).elim

open PEqualNP.TopForm in
lemma hl_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (w : Fin n) (r : ℕ) (hcl : Cl G C w r) (k : ℕ) (v : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) r (n + k)) (hk : k ∈ junk G C)
    (j : Fin 2) (hY : side (n := n) C k ((1 : Fin 2) - j) = {v} ∨
      Lw n C (opnd C k ((1 : Fin 2) - j)) = {v}) :
    G.Adj w v ∨ ∀ d ∈ (side (n := n) C k j).filter (fun y => ¬ G.Adj v y), G.Adj w d := by
  by_cases hwv : G.Adj w v
  · exact Or.inl hwv
  · right
    intro d hd
    rw [Finset.mem_filter] at hd
    by_contra hwd
    exact hd.2 (cl_rectF G C hAO2 w r hcl k hk hr j d v hd.1
      (thin_fires C k _ v hY) hwd hwv).symm

lemma cn_pair_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v v' : Fin n) (hne : v ≠ v') :
    (Finset.univ.filter (fun x => G.Adj x v ∧ G.Adj x v')).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact common_unique G h4 x y v v' hx.1 hx.2 hy.1 hy.2 hne

lemma cn_set_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (D : Finset (Fin n)) (hD : 2 ≤ D.card) :
    (Finset.univ.filter (fun x => ∀ d ∈ D, G.Adj x d)).card ≤ 1 := by
  obtain ⟨d1, hd1, d2, hd2, hne⟩ := Finset.one_lt_card.mp hD
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact common_unique G h4 x y d1 d2 (hx d1 hd1) (hx d2 hd2) (hy d1 hd1) (hy d2 hd2) hne

lemma card_two_centres {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (z z' : Fin n) (hne : z ≠ z') (Q : Finset (Fin n)) (k k' : ℕ)
    (h1 : (Q.filter (fun x => ¬ G.Adj z x)).card ≤ k)
    (h2 : (Q.filter (fun x => ¬ G.Adj z' x)).card ≤ k') : Q.card ≤ k + k' + 1 := by
  classical
  have hcn : (Q.filter (fun x => G.Adj z x ∧ G.Adj z' x)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    by_contra hxy
    exact hne (common_unique G h4 z z' x y hx.2.1 hy.2.1 hx.2.2 hy.2.2 hxy)
  have hsub : Q ⊆ (Q.filter (fun x => ¬ G.Adj z x)) ∪ (Q.filter (fun x => ¬ G.Adj z' x)) ∪
      (Q.filter (fun x => G.Adj z x ∧ G.Adj z' x)) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases a1 : G.Adj z x
    · by_cases a2 : G.Adj z' x
      · exact Or.inr ⟨hx, a1, a2⟩
      · exact Or.inl (Or.inr ⟨hx, a2⟩)
    · exact Or.inl (Or.inl ⟨hx, a1⟩)
  have u0 := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    ((Q.filter (fun x => ¬ G.Adj z x)) ∪ (Q.filter (fun x => ¬ G.Adj z' x)))
    (Q.filter (fun x => G.Adj z x ∧ G.Adj z' x))
  have u2 := Finset.card_union_le (Q.filter (fun x => ¬ G.Adj z x))
    (Q.filter (fun x => ¬ G.Adj z' x))
  omega

lemma g43 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (D1 D2 D3 : Finset (Fin n))
    (htri : ∀ a ∈ D1, ∀ x ∈ D2, ∀ y ∈ D3, G.Adj a x ∨ G.Adj a y ∨ G.Adj x y)
    (h2 : 4 ≤ D2.card) (h3 : 4 ≤ D3.card) : D1.card ≤ 2 := by
  classical
  have hkind : ∀ a ∈ D1, (D2.filter (fun x => ¬ G.Adj a x)).card ≤ 1 ∨
      (D3.filter (fun y => ¬ G.Adj a y)).card ≤ 1 := by
    intro a ha
    apply biclique_star G h4
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    rcases htri a ha x hx.1 y hy.1 with h | h | h
    · exact absurd h hx.2
    · exact absurd h hy.2
    · exact h
  have hsub : D1 ⊆ (D1.filter (fun a => (D2.filter (fun x => ¬ G.Adj a x)).card ≤ 1)) ∪
      (D1.filter (fun a => (D3.filter (fun y => ¬ G.Adj a y)).card ≤ 1)) := by
    intro a ha
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hkind a ha with h | h
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, h⟩
  have c2 : (D1.filter (fun a => (D2.filter (fun x => ¬ G.Adj a x)).card ≤ 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha a' ha'
    rw [Finset.mem_filter] at ha ha'
    by_contra hne
    have := card_two_centres G h4 a a' hne D2 1 1 ha.2 ha'.2
    omega
  have c3 : (D1.filter (fun a => (D3.filter (fun y => ¬ G.Adj a y)).card ≤ 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha a' ha'
    rw [Finset.mem_filter] at ha ha'
    by_contra hne
    have := card_two_centres G h4 a a' hne D3 1 1 ha.2 ha'.2
    omega
  have u0 := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    (D1.filter (fun a => (D2.filter (fun x => ¬ G.Adj a x)).card ≤ 1))
    (D1.filter (fun a => (D3.filter (fun y => ¬ G.Adj a y)).card ≤ 1))
  omega

open PEqualNP.TopForm in
lemma valid4i {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (h : ℕ) (hh : h ∈ junk G C) (k : ℕ)
    (hk : k ∈ junk G C) (hor0 : OrReaches n C (opnd C t i) h)
    (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k) (jh jk : Fin 2)
    (a1 b1 a2 b2 : Fin n) (ha1 : a1 ∈ side (n := n) C h jh)
    (hb1 : b1 ∈ side (n := n) C h ((1 : Fin 2) - jh)) (ha2 : a2 ∈ side (n := n) C k jk)
    (hb2 : b2 ∈ side (n := n) C k ((1 : Fin 2) - jk)) :
    ∃ y z : Fin n, G.Adj y z ∧ (y = a1 ∨ y = b1 ∨ y = a2 ∨ y = b2) ∧
      (z = a1 ∨ z = b1 ∨ z = a2 ∨ z = b2) := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
      ∀ w : Fin n, X w = true ↔ (w = a1 ∨ w = b1 ∨ w = a2 ∨ w = b2) :=
    ⟨fun w => decide (w = a1 ∨ w = b1 ∨ w = a2 ∨ w = b2), fun w => by simp⟩
  have hhv : gateVal n C h X = true := by
    apply (junk_rect G C hAO2 h hh X)
    rcases fin2_sub jh with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at ha1; rw [e'] at hb1
      exact ⟨⟨a1, ha1, (hx a1).mpr (Or.inl rfl)⟩, ⟨b1, hb1, (hx b1).mpr (Or.inr (Or.inl rfl))⟩⟩
    · rw [e] at ha1; rw [e'] at hb1
      exact ⟨⟨b1, hb1, (hx b1).mpr (Or.inr (Or.inl rfl))⟩, ⟨a1, ha1, (hx a1).mpr (Or.inl rfl)⟩⟩
  have hkv : gateVal n C k X = true := by
    apply (junk_rect G C hAO2 k hk X)
    rcases fin2_sub jk with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at ha2; rw [e'] at hb2
      exact ⟨⟨a2, ha2, (hx a2).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩,
        ⟨b2, hb2, (hx b2).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩⟩
    · rw [e] at ha2; rw [e'] at hb2
      exact ⟨⟨b2, hb2, (hx b2).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩,
        ⟨a2, ha2, (hx a2).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
  have h0 := junk_leaf C _ h hor0 X hhv
  have h1 := junk_leaf C _ k hor1 X hkv
  have hF : graphFun G ∅ X = true := by
    rcases fin2_sub i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · rw [hi] at h0; rw [hi'] at h1
      exact top_sound G C hAO2 t ht X h0 h1
    · rw [hi] at h0; rw [hi'] at h1
      exact top_sound G C hAO2 t ht X h1 h0
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  exact ⟨y, z, hyz, (hx y).mp hy, (hx z).mp hz⟩

lemma tri_of_four {n : ℕ} (G : SimpleGraph (Fin n)) (a x d v y z : Fin n) (hyz : G.Adj y z)
    (hy : y = a ∨ y = x ∨ y = d ∨ y = v) (hz : z = a ∨ z = x ∨ z = d ∨ z = v)
    (ha : ¬ G.Adj v a) (hx : ¬ G.Adj v x) (hd : ¬ G.Adj v d) :
    G.Adj a x ∨ G.Adj a d ∨ G.Adj x d := by
  rcases hy with e | e | e | e <;> rcases hz with e' | e' | e' | e' <;> rw [e, e'] at hyz
  all_goals first
    | exact (G.irrefl hyz).elim
    | exact Or.inl hyz
    | exact Or.inl hyz.symm
    | exact Or.inr (Or.inl hyz)
    | exact Or.inr (Or.inl hyz.symm)
    | exact Or.inr (Or.inr hyz)
    | exact Or.inr (Or.inr hyz.symm)
    | exact absurd hyz ha
    | exact absurd hyz.symm ha
    | exact absurd hyz hx
    | exact absurd hyz.symm hx
    | exact absurd hyz hd
    | exact absurd hyz.symm hd

open PEqualNP.TopForm in
lemma fires_both {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (k : ℕ) (hk : k ∈ junk G C) (x : Fin n)
    (h0 : x ∈ side (n := n) C k 0) (h1 : x ∈ side (n := n) C k 1) : Fires n C (n + k) x := by
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  intro X hX
  exact (and_val2 C hAO2 k hlen hand X).mpr
    ⟨side_leaf C k 0 x h0 X hX, side_leaf C k 1 x h1 X hX⟩

open PEqualNP.TopForm in
lemma fires_opnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (k : ℕ) (hk : k ∈ junk G C) (j : Fin 2) (y : Fin n)
    (hy : Fires n C (n + k) y) : Fires n C (opnd C k j) y := by
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  intro X hX
  have h := (and_val2 C hAO2 k hlen hand X).mp (hy X hX)
  rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]; exact h.1
  · rw [e]; exact h.2

open PEqualNP.TopForm in
lemma clean_rectL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u : Fin n) (hu : Fires n C (opnd C t i) u)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (b c : Fin n) (hb : b ∈ Lw n C (opnd C k 0)) (hc : c ∈ Lw n C (opnd C k 1))
    (hub : ¬ G.Adj u b) (huc : ¬ G.Adj u c) : G.Adj b c := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ w : Fin n, X w = true ↔ (w = u ∨ w = b ∨ w = c) :=
    ⟨fun w => decide (w = u ∨ w = b ∨ w = c), fun w => by simp⟩
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  have hkv : gateVal n C k X = true :=
    (and_val2 C hAO2 k hlen hand X).mpr
      ⟨mem_Lw.mp hb X ((hx b).mpr (Or.inr (Or.inl rfl))),
        mem_Lw.mp hc X ((hx c).mpr (Or.inr (Or.inr rfl)))⟩
  have hsv := hu X ((hx u).mpr (Or.inl rfl))
  have hjv := junk_leaf C _ k hor X hkv
  have hF : graphFun G ∅ X = true := by
    rcases fin2_sub i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · rw [hi] at hsv; rw [hi'] at hjv
      exact top_sound G C hAO2 t ht X hsv hjv
    · rw [hi] at hsv; rw [hi'] at hjv
      exact top_sound G C hAO2 t ht X hjv hsv
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  rcases (hx y).mp hy with e1 | e1 | e1 <;> rcases (hx z).mp hz with e2 | e2 | e2 <;>
    rw [e1, e2] at hyz
  · exact (G.irrefl hyz).elim
  · exact absurd hyz hub
  · exact absurd hyz huc
  · exact absurd hyz.symm hub
  · exact (G.irrefl hyz).elim
  · exact hyz
  · exact absurd hyz.symm huc
  · exact hyz.symm
  · exact (G.irrefl hyz).elim

open PEqualNP.TopForm in
lemma lleaf_cdl {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (z : Fin n) (hz : Fires n C (opnd C t i) z)
    (h : ℕ) (hh : h ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) h)
    (x y : Fin n) (hx0 : x ∈ side (n := n) C h 0) (hx1 : x ∈ side (n := n) C h 1)
    (hy : y ∈ Lw n C (n + h)) (hxy : y ≠ x) : CDL G C 1 z x := by
  classical
  have hrh := (orReaches_reach h _ hor).1
  have hxf : Fires n C (n + h) x := fires_both G C hAO2 h hh x hx0 hx1
  have hzx : G.Adj z x := fires_adj G C hAO2 t ht i z x hz (fires_mono hrh hxf)
  have hzy : G.Adj z y := fires_adj G C hAO2 t ht i z y hz (fires_mono hrh (mem_Lw.mp hy))
  have hclean := fun b hb c hc => clean_rectL G C hAO2 t ht i z hz h hh hor b c hb hc
  have hxx : x ∈ Lw n C x.val := mem_Lw.mpr ((fires_input C x x).mpr rfl)
  have hux : ∀ y' ∈ Lw n C x.val, G.Adj z y' → y' = x :=
    fun y' hy' _ => (fires_input C x y').mp (mem_Lw.mp hy')
  rcases dirt_star G h4 z _ _ hclean with hd | hd
  · exact cdl_of_path G C 1 z x hzx (opnd C h 0) x.val (mem_orIn_reach x hx0) hxx hux
      ⟨y, mem_Lw.mpr (fires_opnd G C hAO2 h hh 0 y (mem_Lw.mp hy)), hxy, hzy⟩ hd
  · exact cdl_of_path G C 1 z x hzx (opnd C h 1) x.val (mem_orIn_reach x hx1) hxx hux
      ⟨y, mem_Lw.mpr (fires_opnd G C hAO2 h hh 1 y (mem_Lw.mp hy)), hxy, hzy⟩ hd

open PEqualNP.TopForm in
lemma valid4L {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (h : ℕ) (hh : h ∈ junk G C) (k : ℕ)
    (hk : k ∈ junk G C) (hor0 : OrReaches n C (opnd C t i) h)
    (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k) (jk : Fin 2)
    (a1 b1 a2 b2 : Fin n) (ha1 : a1 ∈ Lw n C (opnd C h 0))
    (hb1 : b1 ∈ Lw n C (opnd C h 1)) (ha2 : a2 ∈ side (n := n) C k jk)
    (hb2 : b2 ∈ side (n := n) C k ((1 : Fin 2) - jk)) :
    ∃ y z : Fin n, G.Adj y z ∧ (y = a1 ∨ y = b1 ∨ y = a2 ∨ y = b2) ∧
      (z = a1 ∨ z = b1 ∨ z = a2 ∨ z = b2) := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
      ∀ w : Fin n, X w = true ↔ (w = a1 ∨ w = b1 ∨ w = a2 ∨ w = b2) :=
    ⟨fun w => decide (w = a1 ∨ w = b1 ∨ w = a2 ∨ w = b2), fun w => by simp⟩
  obtain ⟨hlen, hand⟩ := junk_lt G C h hh
  have hhv : gateVal n C h X = true :=
    (and_val2 C hAO2 h hlen hand X).mpr
      ⟨mem_Lw.mp ha1 X ((hx a1).mpr (Or.inl rfl)),
        mem_Lw.mp hb1 X ((hx b1).mpr (Or.inr (Or.inl rfl)))⟩
  have hkv : gateVal n C k X = true := by
    apply (junk_rect G C hAO2 k hk X)
    rcases fin2_sub jk with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at ha2; rw [e'] at hb2
      exact ⟨⟨a2, ha2, (hx a2).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩,
        ⟨b2, hb2, (hx b2).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩⟩
    · rw [e] at ha2; rw [e'] at hb2
      exact ⟨⟨b2, hb2, (hx b2).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩,
        ⟨a2, ha2, (hx a2).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
  have h0 := junk_leaf C _ h hor0 X hhv
  have h1 := junk_leaf C _ k hor1 X hkv
  have hF : graphFun G ∅ X = true := by
    rcases fin2_sub i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · rw [hi] at h0; rw [hi'] at h1
      exact top_sound G C hAO2 t ht X h0 h1
    · rw [hi] at h0; rw [hi'] at h1
      exact top_sound G C hAO2 t ht X h1 h0
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  exact ⟨y, z, hyz, (hx y).mp hy, (hx z).mp hz⟩

open PEqualNP.TopForm in
lemma heavy_leafL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (h : ℕ) (hh : h ∈ junk G C)
    (horh : OrReaches n C (opnd C t i) h) (k : ℕ) (hk : k ∈ junk G C)
    (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k) (v : Fin n) (j : Fin 2)
    (hY : side (n := n) C k ((1 : Fin 2) - j) = {v})
    (hD : K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card)
    (u y : Fin n) (hu0 : u ∈ side (n := n) C h 0) (hu1 : u ∈ side (n := n) C h 1)
    (hy : y ∈ Lw n C (n + h)) (hyu : y ≠ u)
    (hvu : G.Adj v u) (hvy : G.Adj v y) : CDL G C 3 v u := by
  classical
  have hv1 : v ∈ side (n := n) C k ((1 : Fin 2) - j) := by
    rw [hY]; exact Finset.mem_singleton_self v
  have htri : ∀ a ∈ (Lw n C (opnd C h 0)).filter (fun x => ¬ G.Adj v x),
      ∀ x ∈ (Lw n C (opnd C h 1)).filter (fun x => ¬ G.Adj v x),
      ∀ d ∈ (side (n := n) C k j).filter (fun x => ¬ G.Adj v x),
      G.Adj a x ∨ G.Adj a d ∨ G.Adj x d := by
    intro a ha x hx d hd
    rw [Finset.mem_filter] at ha hx hd
    obtain ⟨y', z', hyz, hy', hz'⟩ := valid4L G C hAO2 t ht i h hh k hk horh hor j
      a x d v ha.1 hx.1 hd.1 hv1
    exact tri_of_four G a x d v y' z' hyz hy' hz' ha.2 hx.2 hd.2
  have hD4 : 4 ≤ ((side (n := n) C k j).filter (fun x => ¬ G.Adj v x)).card := by omega
  have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
  have huq : ∀ y' ∈ Lw n C u.val, G.Adj v y' → y' = u :=
    fun y' hy' _ => (fires_input C u y').mp (mem_Lw.mp hy')
  by_cases h1 : 4 ≤ ((Lw n C (opnd C h 1)).filter (fun x => ¬ G.Adj v x)).card
  · have h0 := g43 G h4 _ _ _ htri h1 hD4
    exact cdl_of_path G C 3 v u hvu (opnd C h 0) u.val (mem_orIn_reach u hu0) huu huq
      ⟨y, mem_Lw.mpr (fires_opnd G C hAO2 h hh 0 y (mem_Lw.mp hy)), hyu, hvy⟩
      (le_trans h0 (by norm_num))
  · exact cdl_of_path G C 3 v u hvu (opnd C h 1) u.val (mem_orIn_reach u hu1) huu huq
      ⟨y, mem_Lw.mpr (fires_opnd G C hAO2 h hh 1 y (mem_Lw.mp hy)), hyu, hvy⟩
      (Nat.lt_succ_iff.mp (not_le.mp h1))

def HcSlot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ gc ∈ slots C, G.Adj u v ∧ HcP G C K gc.2 v ∧ (∀ y, HcP G C K gc.2 y → y = v) ∧
    (∃ v', HcP G C K (n + gc.1) v' ∧ v' ≠ v) ∧ Cl G C u (n + gc.1)

open PEqualNP.TopForm in
lemma hcslot_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) (hK : 1 ≤ K) :
    Bnd (HcSlot G C K) (2 * (2 * C.gates.length)) := by
  classical
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  unfold HcSlot
  apply obj_count (slots C) 2
  intro gc _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, _, huniq, ⟨v', hv', hne⟩, _⟩ := hP zv0 hzv0
    obtain ⟨k', hr', hk', j', hY', hD'⟩ := hv'
    have hsub : P ⊆ ((Finset.univ.filter (fun x => G.Adj x zv0.2 ∧ G.Adj x v')) ∪
        (Finset.univ.filter (fun x => ∀ d ∈ (side (n := n) C k' j').filter
          (fun y => ¬ G.Adj v' y), G.Adj x d))) ×ˢ {zv0.2} := by
      intro zv hzv
      obtain ⟨hadj, hv, _, _, hcl⟩ := hP zv hzv
      have e2 : zv.2 = zv0.2 := huniq zv.2 hv
      rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_union]
      refine ⟨?_, e2⟩
      rcases hl_clean G C hAO2 zv.1 (n + gc.1) hcl k' v' hr' hk' j' hY' with h | h
      · left
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by rw [← e2]; exact hadj, h⟩
      · right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hA := cn_pair_card G h4 zv0.2 v' (Ne.symm hne)
    have hB := cn_set_card G h4 ((side (n := n) C k' j').filter (fun y => ¬ G.Adj v' y))
      (by omega)
    have hU := Finset.card_union_le
      (Finset.univ.filter (fun x => G.Adj x zv0.2 ∧ G.Adj x v'))
      (Finset.univ.filter (fun x => ∀ d ∈ (side (n := n) C k' j').filter
        (fun y => ¬ G.Adj v' y), G.Adj x d))
    have hc := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_singleton] at hc
    omega

def TopHL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ ti ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ u ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ti.2) ∧
    (∀ y ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ti.2), G.Adj v y → y = u) ∧
    HcP G C K (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) v ∧
    ∀ y, HcP G C K (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) y → y = v

lemma tophl_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) :
    Bnd (TopHL G C K) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold TopHL
  refine bnd_le (by rw [hc]; omega) (obj_count _ 1 _ ?_)
  intro ti _ P hP
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  obtain ⟨_, _, a3, _, a5⟩ := hP zv hzv
  obtain ⟨badj, b2, _, b4, _⟩ := hP zv' hzv'
  have e2 : zv'.2 = zv.2 := a5 zv'.2 b4
  have e1 : zv'.1 = zv.1 := a3 zv'.1 b2 (by rw [← e2]; exact badj.symm)
  exact Prod.ext e1.symm e2.symm

open PEqualNP.TopForm in
lemma heavy_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v) (τu : ℕ)
    (hru : Relation.ReflTransGen (OrStep n C) (opnd C t i) τu) (huτ : u ∈ Lw n C τu)
    {Q : Prop} (hτu : (∀ y ∈ Lw n C τu, G.Adj v y → y = u) ∨ Q)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hY : side (n := n) C k ((1 : Fin 2) - j) = {v} ∨
      Lw n C (opnd C k ((1 : Fin 2) - j)) = {v})
    (hD : K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card) :
    HcSlot G C K u v ∨ Q ∨ CDL G C 1 v u ∨ TopHL G C K u v := by
  classical
  have hup : u ∈ Lw n C (opnd C t i) := Lw_mono hru huτ
  have hfu : Fires n C (opnd C t i) u := mem_Lw.mp hup
  have hrk : Relation.ReflTransGen (OrStep n C) (opnd C t ((1 : Fin 2) - i)) (n + k) :=
    (orReaches_reach k _ hor).1
  have hHLk : HL G C K k v := ⟨hk, j, hY, hD⟩
  have hvq : HcP G C K (opnd C t ((1 : Fin 2) - i)) v := ⟨k, hrk, hHLk⟩
  have htm := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htm
  by_cases hbig : ∃ v', HcP G C K (opnd C t ((1 : Fin 2) - i)) v' ∧ v' ≠ v
  · left
    have hterm : ¬ ∃ v', HcP G C K (n + k) v' ∧ v' ≠ v := by
      rintro ⟨v', ⟨k', hr', hhl'⟩, hne⟩
      have hkk : k' = k := by
        have := junk_reach_self G C k hk _ hr'
        omega
      rw [hkk] at hhl'
      obtain ⟨_, j', hY', _⟩ := hhl'
      exact hne (hl_unique G C K (by omega) k j j' v v' hY hD hY')
    obtain ⟨g, c, hg, hin, hr1, hr2, hr3, hb1, hb2⟩ :=
      path_split C (fun r => ∃ v', HcP G C K r v' ∧ v' ≠ v) (n + k) hterm _ hrk hbig
    refine ⟨(g, c), slot_mem C hg hin, huv, ⟨k, hr3, hHLk⟩, ?_, hb1, cl_mono G C (cl_top G C hAO2 t ht i u hfu) hr1⟩
    intro y hy
    by_contra hne
    exact hb2 ⟨y, hy, hne⟩
  · have huniq : ∀ y, HcP G C K (opnd C t ((1 : Fin 2) - i)) y → y = v := by
      intro y hy
      by_contra hne
      exact hbig ⟨y, hy, hne⟩
    rcases hτu with hτu | hcd
    · by_cases hsec : ∃ b ∈ Lw n C (opnd C t i), b ≠ u ∧ G.Adj v b
      · right; right; left
        refine cdl_of_path G C 1 v u huv.symm _ τu hru huτ hτu hsec ?_
        have hsubB : (Lw n C (opnd C t i)).filter (fun y => ¬ G.Adj v y) ⊆
            Finset.univ.filter (fun x => ∀ d ∈ (side (n := n) C k j).filter
              (fun y => ¬ G.Adj v y), G.Adj x d) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hclx : Cl G C x (opnd C t ((1 : Fin 2) - i)) :=
            cl_top G C hAO2 t ht i x (mem_Lw.mp hx.1)
          rcases hl_clean G C hAO2 x _ hclx k v hrk hk j hY with h | h
          · exact absurd h.symm hx.2
          · exact h
        exact (Finset.card_le_card hsubB).trans (cn_set_card G h4 _ (by omega))
      · right; right; right
        refine ⟨(t, i), Finset.mem_product.mpr ⟨Finset.mem_range.mpr htm.1, Finset.mem_univ _⟩,
          huv, hup, ?_, hvq, huniq⟩
        intro y hy hvy
        by_contra hne
        exact hsec ⟨y, hy, hne, hvy⟩
    · exact Or.inr (Or.inl hcd)

lemma cdl_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {K K' : ℕ} (hK : K ≤ K') {z x : Fin n} (h : CDL G C K z x) : CDL G C K' z x := by
  obtain ⟨gc, hgc, a1, a2, a3, a5, a6, a7⟩ := h
  exact ⟨gc, hgc, a1, a2, a3, a5, a6, a7.trans hK⟩

lemma cd_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) :
    Bnd (CD G C K) ((2 * K + 1) ^ 2 * (2 * C.gates.length)) :=
  fun P hP => cd_count G h4 C h2 K P hP

def PayD {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  CD G C K u v ∨ CD G C K v u ∨ LineDet G C u v ∨ CDL G C K u v ∨ CDL G C K v u ∨
    TopDet n C u v ∨ HcSlot G C K u v ∨ TopHL G C K u v

open PEqualNP.TopForm in
lemma payd_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) (hK : 1 ≤ K) :
    Bnd (PayD G C K)
      ((2 * K + 1) ^ 2 * (2 * C.gates.length) + ((2 * K + 1) ^ 2 * (2 * C.gates.length) +
        (2 * C.gates.length + ((2 * K + 1) ^ 2 * (2 * C.gates.length) +
          ((2 * K + 1) ^ 2 * (2 * C.gates.length) + (2 * C.gates.length +
            (2 * (2 * C.gates.length) + 2 * C.gates.length))))))) := by
  unfold PayD
  exact bnd_or (cd_bnd G h4 C h2 K) (bnd_or (bnd_swap (cd_bnd G h4 C h2 K))
    (bnd_or (linedet_bnd G C) (bnd_or (cdl_bnd G h4 C h2 K)
      (bnd_or (bnd_swap (cdl_bnd G h4 C h2 K)) (bnd_or (topdet_bnd n C)
        (bnd_or (hcslot_bnd G C h4 hAO2 h2 K hK) (tophl_bnd G C K)))))))

open PEqualNP.TopForm in
lemma classD_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v) (τu : ℕ)
    (hru : Relation.ReflTransGen (OrStep n C) (opnd C t i) τu)
    (hterm : τu = u.val ∨ ∃ h ∈ junk G C, τu = n + h ∧ u ∈ side (n := n) C h 0 ∧
      u ∈ side (n := n) C h 1)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (hr0 : u ∈ side (n := n) C k 0 ∨ v ∈ side (n := n) C k 0)
    (hr1 : u ∈ side (n := n) C k 1 ∨ v ∈ side (n := n) C k 1) : PayD G C K u v := by
  classical
  have e10 : ((1 : Fin 2) - 0) = 1 := by decide
  have e11 : ((1 : Fin 2) - 1) = 0 := by decide
  have huτ : u ∈ Lw n C τu := by
    rcases hterm with e | ⟨h, hh, e, h0, h1⟩
    · rw [e]; exact mem_Lw.mpr ((fires_input C u u).mpr rfl)
    · rw [e]; exact mem_Lw.mpr (fires_both G C hAO2 h hh u h0 h1)
  have hfu : Fires n C (opnd C t i) u := fires_mono hru (mem_Lw.mp huτ)
  have hrk : Relation.ReflTransGen (OrStep n C) (opnd C t ((1 : Fin 2) - i)) (n + k) :=
    (orReaches_reach k _ hor).1
  have htm := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htm
  have hklen := (junk_lt G C k hk).1
  have hτheavy : ∀ j : Fin 2, side (n := n) C k ((1 : Fin 2) - j) = {v} →
      K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card →
      ((∀ y ∈ Lw n C τu, G.Adj v y → y = u) ∨ CDL G C 3 v u) := by
    intro j hY hD
    rcases hterm with e | ⟨h, hh, e, h0, h1⟩
    · left
      intro y hy _
      rw [e] at hy
      exact (fires_input C u y).mp (mem_Lw.mp hy)
    · by_cases hex : ∃ y, y ∈ Lw n C (n + h) ∧ y ≠ u ∧ G.Adj v y
      · right
        obtain ⟨y, hy, hyu, hvy⟩ := hex
        have horh : OrReaches n C (opnd C t i) h := by
          rw [e] at hru
          exact reach_orReaches hru h rfl (junk_lt G C h hh).1
        exact heavy_leafL G C h4 hAO2 K hK t ht i h hh horh k hk hor v j hY hD
          u y h0 h1 hy hyu huv.symm hvy
      · left
        intro y hy hvy
        by_contra hne
        rw [e] at hy
        exact hex ⟨y, hy, hne, hvy⟩
  have hheavy : ∀ j : Fin 2, side (n := n) C k ((1 : Fin 2) - j) = {v} →
      K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card → PayD G C K u v := by
    intro j hY hD
    rcases heavy_pay G C h4 hAO2 K hK t ht i u v huv τu hru huτ (hτheavy j hY hD)
      k hk hor j (Or.inl hY) hD with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  rcases classD_cases G C h4 hAO2 K t ht i u hfu k hk hor v hr0 hr1 with
    (h | h) | (h | h) | (h | h) | (h | h) | h
  · exact Or.inl (cd_mono G C (by omega) (cd_of_O1 G C k 0 u v huv h))
  · exact Or.inl (cd_mono G C (by omega) (cd_of_O1 G C k 1 u v huv h))
  · exact Or.inr (Or.inl (cd_of_O2 G C K k 0 _ u v huv h))
  · exact Or.inr (Or.inl (cd_of_O2 G C K k 1 _ u v huv h))
  · refine Or.inr (Or.inr (Or.inl ⟨(k, 0),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hklen, Finset.mem_univ _⟩, huv, ?_⟩))
    rw [e10]; exact h
  · refine Or.inr (Or.inr (Or.inl ⟨(k, 1),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hklen, Finset.mem_univ _⟩, huv, ?_⟩))
    rw [e11]; exact h
  · exact hheavy 0 (by rw [e10]; exact h.1) h.2.2.2.2
  · exact hheavy 1 (by rw [e11]; exact h.1) h.2.2.2.2
  · obtain ⟨hv0, hv1, _⟩ := h
    have hvτ : v ∈ Lw n C (n + k) := mem_Lw.mpr (fires_both G C hAO2 k hk v hv0 hv1)
    have hfv : Fires n C (opnd C t ((1 : Fin 2) - i)) v := fires_mono hrk (mem_Lw.mp hvτ)
    by_cases hτv : ∀ y ∈ Lw n C (n + k), y = v
    · have hτu : (∀ y ∈ Lw n C τu, y = u) ∨ CDL G C 1 v u := by
        rcases hterm with e | ⟨h, hh, e, h0, h1⟩
        · left
          intro y hy
          rw [e] at hy
          exact (fires_input C u y).mp (mem_Lw.mp hy)
        · by_cases hex : ∃ y, y ∈ Lw n C (n + h) ∧ y ≠ u
          · right
            obtain ⟨y, hy, hyu⟩ := hex
            have horh : OrReaches n C (opnd C t ((1 : Fin 2) - ((1 : Fin 2) - i))) h := by
              rw [fin2_ss]
              rw [e] at hru
              exact reach_orReaches hru h rfl (junk_lt G C h hh).1
            exact lleaf_cdl G C h4 hAO2 t ht ((1 : Fin 2) - i) v hfv h hh horh
              u y h0 h1 hy hyu
          · left
            intro y hy
            by_contra hne
            rw [e] at hy
            exact hex ⟨y, hy, hne⟩
      rcases lstar_pay G C hAO2 t ht i u v τu (n + k) hru huτ hτu hrk hvτ hτv with
        h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h)))))
    · obtain ⟨y, hy1⟩ := not_forall.mp hτv
      obtain ⟨hy, hyv⟩ := Classical.not_imp.mp hy1
      exact Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega)
        (lleaf_cdl G C h4 hAO2 t ht i u hfu k hk hor v y hv0 hv1 hy hyv)))))

lemma small_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (S : Finset (Fin n)) (hS : ∀ b ∈ S, G.Adj u b → b = v) :
    S.card ≤ 1 + (S.filter (fun y => ¬ G.Adj u y)).card := by
  classical
  have hsub : S ⊆ {v} ∪ S.filter (fun y => ¬ G.Adj u y) := by
    intro b hb
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter]
    by_cases hub : G.Adj u b
    · exact Or.inl (hS b hb hub)
    · exact Or.inr ⟨hb, hub⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ({v} : Finset (Fin n)) (S.filter (fun y => ¬ G.Adj u y))
  rw [Finset.card_singleton] at h2
  omega

def PA {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : ℕ) (z x : Fin n)
    (S : Finset (Fin n)) : Prop :=
  x ∈ S ∧ (∃ b ∈ S, b ≠ x ∧ G.Adj z b) ∧ (S.filter (fun y => ¬ G.Adj z y)).card ≤ K

lemma not_pa_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : ℕ)
    (z x : Fin n) (S : Finset (Fin n)) (hx : x ∈ S) (h : ¬ PA G K z x S)
    (hd : (S.filter (fun y => ¬ G.Adj z y)).card ≤ K) :
    S.card ≤ 1 + (S.filter (fun y => ¬ G.Adj z y)).card := by
  apply small_side G z x S
  intro b hb hzb
  by_contra hne
  exact h ⟨hx, ⟨b, hb, hne, hzb⟩, hd⟩

lemma classX_half {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : ℕ) (hK : 1 ≤ K)
    (u v : Fin n) (Uh Vh Uk Vk : Finset (Fin n))
    (huh : u ∈ Uh) (hvh : v ∈ Vh) (huk : u ∈ Uk) (hvk : v ∈ Vk)
    (hdv : (Uh.filter (fun y => ¬ G.Adj v y)).card ≤ 1 ∨
      (Uk.filter (fun y => ¬ G.Adj v y)).card ≤ 1)
    (hn1 : ¬ PA G K u v Vh) (hn2 : ¬ PA G K u v Vk) (hn3 : ¬ PA G K v u Uh)
    (hn4 : ¬ PA G K v u Uk)
    (hd : (Vh.filter (fun y => ¬ G.Adj u y)).card ≤ 1) :
    (Uh.card ≤ K + 1 ∧ Vh.card ≤ K + 1) ∨ (Uk.card ≤ K + 1 ∧ Vk.card ≤ K + 1) ∨
      (Vh.card ≤ 2 ∧ K < (Uh.filter (fun y => ¬ G.Adj v y)).card ∧ Uk.card ≤ 2 ∧
        K < (Vk.filter (fun y => ¬ G.Adj u y)).card) := by
  have hVh : Vh.card ≤ 2 := by
    have := not_pa_small G K u v Vh hvh hn1 (by omega)
    omega
  by_cases hUh : Uh.card ≤ K + 1
  · exact Or.inl ⟨hUh, by omega⟩
  · have hDv : K < (Uh.filter (fun y => ¬ G.Adj v y)).card := by
      by_contra hle
      have := not_pa_small G K v u Uh huh hn3 (by omega)
      omega
    have hdk : (Uk.filter (fun y => ¬ G.Adj v y)).card ≤ 1 := by
      rcases hdv with h | h
      · omega
      · exact h
    have hUk : Uk.card ≤ 2 := by
      have := not_pa_small G K v u Uk huk hn4 (by omega)
      omega
    by_cases hVk : Vk.card ≤ K + 1
    · exact Or.inr (Or.inl ⟨by omega, hVk⟩)
    · have hDu : K < (Vk.filter (fun y => ¬ G.Adj u y)).card := by
        by_contra hle
        have := not_pa_small G K u v Vk hvk hn2 (by omega)
        omega
      exact Or.inr (Or.inr ⟨hVh, hDv, hUk, hDu⟩)

lemma classX_abs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (K : ℕ) (hK : 1 ≤ K) (u v : Fin n) (Uh Vh Uk Vk : Finset (Fin n))
    (huh : u ∈ Uh) (hvh : v ∈ Vh) (huk : u ∈ Uk) (hvk : v ∈ Vk)
    (hXu : ∀ d ∈ Vh, ∀ d' ∈ Vk, ¬ G.Adj u d → ¬ G.Adj u d' → G.Adj d d')
    (hXv : ∀ d ∈ Uh, ∀ d' ∈ Uk, ¬ G.Adj v d → ¬ G.Adj v d' → G.Adj d d') :
    (PA G K u v Vh ∨ PA G K u v Vk) ∨ (PA G K v u Uh ∨ PA G K v u Uk) ∨
      ((Uh.card ≤ K + 1 ∧ Vh.card ≤ K + 1) ∨ (Uk.card ≤ K + 1 ∧ Vk.card ≤ K + 1)) ∨
      (Vh.card ≤ 2 ∧ K < (Uh.filter (fun y => ¬ G.Adj v y)).card ∧ Uk.card ≤ 2 ∧
        K < (Vk.filter (fun y => ¬ G.Adj u y)).card) ∨
      (Vk.card ≤ 2 ∧ K < (Uk.filter (fun y => ¬ G.Adj v y)).card ∧ Uh.card ≤ 2 ∧
        K < (Vh.filter (fun y => ¬ G.Adj u y)).card) := by
  classical
  by_cases hn1 : PA G K u v Vh
  · exact Or.inl (Or.inl hn1)
  by_cases hn2 : PA G K u v Vk
  · exact Or.inl (Or.inr hn2)
  by_cases hn3 : PA G K v u Uh
  · exact Or.inr (Or.inl (Or.inl hn3))
  by_cases hn4 : PA G K v u Uk
  · exact Or.inr (Or.inl (Or.inr hn4))
  have hdu := dirt_star G h4 u Vh Vk hXu
  have hdv := dirt_star G h4 v Uh Uk hXv
  right; right
  rcases hdu with hd | hd
  · rcases classX_half G K hK u v Uh Vh Uk Vk huh hvh huk hvk hdv hn1 hn2 hn3 hn4 hd with
      h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rcases classX_half G K hK u v Uk Vk Uh Vh huk hvk huh hvh hdv.symm hn2 hn1 hn4 hn3 hd with
      h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)

def SmallGate {n : ℕ} (C : Circuit) (M : ℕ) (u v : Fin n) : Prop :=
  ∃ g ∈ Finset.range C.gates.length,
    (PEqualNP.TopForm.side (n := n) C g 0).card ≤ M ∧
    (PEqualNP.TopForm.side (n := n) C g 1).card ≤ M ∧
    u ∈ PEqualNP.TopForm.side (n := n) C g 0 ∪ PEqualNP.TopForm.side (n := n) C g 1 ∧
    v ∈ PEqualNP.TopForm.side (n := n) C g 0 ∪ PEqualNP.TopForm.side (n := n) C g 1

lemma smallgate_bnd {n : ℕ} (C : Circuit) (M : ℕ) :
    Bnd (SmallGate (n := n) C M) ((2 * M) * (2 * M) * C.gates.length) := by
  classical
  have h := obj_count (n := n) (Finset.range C.gates.length) ((2 * M) * (2 * M))
    (fun g u v => (PEqualNP.TopForm.side (n := n) C g 0).card ≤ M ∧
      (PEqualNP.TopForm.side (n := n) C g 1).card ≤ M ∧
      u ∈ PEqualNP.TopForm.side (n := n) C g 0 ∪ PEqualNP.TopForm.side (n := n) C g 1 ∧
      v ∈ PEqualNP.TopForm.side (n := n) C g 0 ∪ PEqualNP.TopForm.side (n := n) C g 1) ?_
  · rw [Finset.card_range] at h
    exact h
  · intro g _ P hP
    rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
    · rw [h0]; simp
    · obtain ⟨c0, c1, _, _⟩ := hP zv0 hzv0
      have hsub : P ⊆ (PEqualNP.TopForm.side (n := n) C g 0 ∪
          PEqualNP.TopForm.side (n := n) C g 1) ×ˢ
          (PEqualNP.TopForm.side (n := n) C g 0 ∪ PEqualNP.TopForm.side (n := n) C g 1) := by
        intro zv hzv
        obtain ⟨_, _, a3, a4⟩ := hP zv hzv
        exact Finset.mem_product.mpr ⟨a3, a4⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_product] at hc
      have hu := Finset.card_union_le (PEqualNP.TopForm.side (n := n) C g 0)
        (PEqualNP.TopForm.side (n := n) C g 1)
      calc P.card ≤ _ := hc
        _ ≤ (2 * M) * (2 * M) := Nat.mul_le_mul (by omega) (by omega)

lemma two_level_count {n : ℕ} (m : ℕ) (A : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (P : Finset (Fin n × Fin n))
    (hP : ∀ zv ∈ P, zv.1 ∈ A ∧ zv.2 ∈ L zv.1 ∧ (L zv.1).card ≤ m) : P.card ≤ m * A.card := by
  classical
  have hsub : P ⊆ A.biUnion (fun c => if (L c).card ≤ m then (L c).image (fun x => (c, x))
      else ∅) := by
    intro zv hzv
    obtain ⟨h1, h2, h3⟩ := hP zv hzv
    refine Finset.mem_biUnion.mpr ⟨zv.1, h1, ?_⟩
    rw [if_pos h3]
    exact Finset.mem_image.mpr ⟨zv.2, h2, rfl⟩
  calc P.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ A, (if (L c).card ≤ m then (L c).image (fun x => (c, x)) else ∅).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ A, m := Finset.sum_le_sum (fun c _ => by
        split_ifs with hc
        · exact Finset.card_image_le.trans hc
        · simp)
    _ = m * A.card := by simp [mul_comm]

def HC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) (g : ℕ)
    (jg : Fin 2) (c : Fin n) : Prop :=
  g ∈ PEqualNP.TopForm.junk G C ∧ c ∈ PEqualNP.TopForm.side (n := n) C g jg ∧
    (PEqualNP.TopForm.side (n := n) C g jg).card ≤ 2 ∧
    c ∉ PEqualNP.TopForm.side (n := n) C g ((1 : Fin 2) - jg) ∧
    K < ((PEqualNP.TopForm.side (n := n) C g ((1 : Fin 2) - jg)).filter
      (fun y => ¬ G.Adj c y)).card

def Sp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (jg : Fin 2) (c s : Fin n) : Prop :=
  s ≠ c ∧ (((PEqualNP.TopForm.side (n := n) C g ((1 : Fin 2) - jg)).filter
    (fun y => ¬ G.Adj c y)).filter (fun y => ¬ G.Adj s y)).card ≤ 2

lemma da_of_four {n : ℕ} (G : SimpleGraph (Fin n)) (c d c' a y z : Fin n) (hyz : G.Adj y z)
    (hy : y = c ∨ y = d ∨ y = c' ∨ y = a) (hz : z = c ∨ z = d ∨ z = c' ∨ z = a)
    (h1 : ¬ G.Adj c d) (h2 : ¬ G.Adj c c') (h3 : ¬ G.Adj c a) (h5 : ¬ G.Adj c' d)
    (h6 : ¬ G.Adj c' a) : G.Adj d a := by
  rcases hy with e | e | e | e <;> rcases hz with e' | e' | e' | e' <;> rw [e, e'] at hyz
  all_goals first
    | exact (G.irrefl hyz).elim
    | exact hyz
    | exact hyz.symm
    | exact absurd hyz h1
    | exact absurd hyz.symm h1
    | exact absurd hyz h2
    | exact absurd hyz.symm h2
    | exact absurd hyz h3
    | exact absurd hyz.symm h3
    | exact absurd hyz h5
    | exact absurd hyz.symm h5
    | exact absurd hyz h6
    | exact absurd hyz.symm h6

open PEqualNP.TopForm in
lemma x1_lemma {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (g : ℕ) (jg : Fin 2) (c : Fin n) (g' : ℕ)
    (jg' : Fin 2) (c' : Fin n) (hor : OrReaches n C (opnd C t i) g)
    (hor' : OrReaches n C (opnd C t ((1 : Fin 2) - i)) g')
    (hc : HC G C K g jg c) (hc' : HC G C K g' jg' c') :
    c ≠ c' ∧ (G.Adj c c' ∨ Sp G C g jg c c' ∨ Sp G C g' jg' c' c) := by
  classical
  obtain ⟨hg, hcτ, _, _, hD⟩ := hc
  obtain ⟨hg', hcτ', _, _, hD'⟩ := hc'
  have key : ∀ d ∈ side (n := n) C g ((1 : Fin 2) - jg),
      ∀ a ∈ side (n := n) C g' ((1 : Fin 2) - jg'),
      ¬ G.Adj c d → ¬ G.Adj c c' → ¬ G.Adj c a → ¬ G.Adj c' d → ¬ G.Adj c' a → G.Adj d a := by
    intro d hd a ha h1 h2 h3 h5 h6
    obtain ⟨y, z, hyz, hy, hz⟩ := valid4i G C hAO2 t ht i g hg g' hg' hor hor' jg jg'
      c d c' a hcτ hd hcτ' ha
    exact da_of_four G c d c' a y z hyz hy hz h1 h2 h3 h5 h6
  have hne : c ≠ c' := by
    intro heq
    have hb := biclique_star G h4
      ((side (n := n) C g ((1 : Fin 2) - jg)).filter (fun y => ¬ G.Adj c y))
      ((side (n := n) C g' ((1 : Fin 2) - jg')).filter (fun y => ¬ G.Adj c' y))
      (fun d hd a ha => by
        rw [Finset.mem_filter] at hd ha
        exact key d hd.1 a ha.1 hd.2 (by rw [← heq]; exact G.irrefl)
          (by rw [heq]; exact ha.2) (by rw [← heq]; exact hd.2) ha.2)
    omega
  refine ⟨hne, ?_⟩
  by_cases hadj : G.Adj c c'
  · exact Or.inl hadj
  · right
    have hb := biclique_star G h4
      (((side (n := n) C g ((1 : Fin 2) - jg)).filter (fun y => ¬ G.Adj c y)).filter
        (fun y => ¬ G.Adj c' y))
      (((side (n := n) C g' ((1 : Fin 2) - jg')).filter (fun y => ¬ G.Adj c' y)).filter
        (fun y => ¬ G.Adj c y))
      (fun d hd a ha => by
        rw [Finset.mem_filter, Finset.mem_filter] at hd ha
        exact key d hd.1.1 a ha.1.1 hd.1.2 hadj ha.2 hd.2 ha.1.2)
    rcases hb with h | h
    · exact Or.inl ⟨Ne.symm hne, by omega⟩
    · exact Or.inr ⟨hne, by omega⟩

def HCsmall {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (c1 c2 : Fin n) : Prop :=
  ∃ gj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    c1 ∈ PEqualNP.TopForm.side (n := n) C gj.1 gj.2 ∧
    (PEqualNP.TopForm.side (n := n) C gj.1 gj.2).card ≤ 2 ∧
    c2 ∈ (PEqualNP.TopForm.side (n := n) C gj.1 ((1 : Fin 2) - gj.2)).filter
      (fun y => G.Adj c1 y) ∧
    ((PEqualNP.TopForm.side (n := n) C gj.1 ((1 : Fin 2) - gj.2)).filter
      (fun y => G.Adj c1 y)).card ≤ 6

lemma hcsmall_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Bnd (HCsmall G C) (12 * (2 * C.gates.length)) := by
  have hc := prod_card C.gates.length
  unfold HCsmall
  refine bnd_le (by rw [hc]) (obj_count _ 12 _ ?_)
  intro gj _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, hτ, _, _⟩ := hP zv0 hzv0
    have h := two_level_count 6 (PEqualNP.TopForm.side (n := n) C gj.1 gj.2)
      (fun c => (PEqualNP.TopForm.side (n := n) C gj.1 ((1 : Fin 2) - gj.2)).filter
        (fun y => G.Adj c y)) P
      (fun zv hzv => by
        obtain ⟨a1, _, a3, a4⟩ := hP zv hzv
        exact ⟨a1, a3, a4⟩)
    omega

lemma centre_eq_special {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (Q : Finset (Fin n)) (u1 s1 u : Fin n)
    (hE : ((Q.filter (fun y => ¬ G.Adj u1 y)).filter (fun y => ¬ G.Adj s1 y)).card ≤ 2)
    (hne : u ≠ u1) (h7 : 7 ≤ (Q.filter (fun y => G.Adj u y)).card) : u = s1 := by
  classical
  by_contra hus
  have hsub : Q.filter (fun y => G.Adj u y) ⊆
      ((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj u1 y)) ∪
      ((Q.filter (fun y => ¬ G.Adj u1 y)).filter (fun y => ¬ G.Adj s1 y)) ∪
      ((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj s1 y)) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases a1 : G.Adj u1 x
    · exact Or.inl (Or.inl ⟨hx', a1⟩)
    · by_cases a2 : G.Adj s1 x
      · exact Or.inr ⟨hx', a2⟩
      · exact Or.inl (Or.inr ⟨⟨hx'.1, a1⟩, a2⟩)
  have c1 : ((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj u1 y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_filter] at hx hy
    by_contra hxy
    exact hne (common_unique G h4 u u1 x y hx.1.2 hy.1.2 hx.2 hy.2 hxy)
  have c3 : ((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj s1 y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_filter] at hx hy
    by_contra hxy
    exact hus (common_unique G h4 u s1 x y hx.1.2 hy.1.2 hx.2 hy.2 hxy)
  have u0 := Finset.card_le_card hsub
  have u1' := Finset.card_union_le
    (((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj u1 y)) ∪
      ((Q.filter (fun y => ¬ G.Adj u1 y)).filter (fun y => ¬ G.Adj s1 y)))
    ((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj s1 y))
  have u2 := Finset.card_union_le
    ((Q.filter (fun y => G.Adj u y)).filter (fun y => G.Adj u1 y))
    ((Q.filter (fun y => ¬ G.Adj u1 y)).filter (fun y => ¬ G.Adj s1 y))
  omega

lemma two_centres2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (Q : Finset (Fin n)) :
    (Finset.univ.filter (fun u : Fin n => 7 ≤ (Q.filter (fun y => G.Adj u y)).card ∧
      ∃ s : Fin n, ((Q.filter (fun y => ¬ G.Adj u y)).filter
        (fun y => ¬ G.Adj s y)).card ≤ 2)).card ≤ 2 := by
  classical
  by_contra hcon
  rw [not_le, Finset.two_lt_card_iff] at hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  obtain ⟨_, s, hs⟩ := ha
  have e1 := centre_eq_special G h4 Q a s b hs (Ne.symm hab) hb.1
  have e2 := centre_eq_special G h4 Q a s c hs (Ne.symm hac) hc.1
  exact hbc (e1.trans e2.symm)

def TwoC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (c1 c2 : Fin n) : Prop :=
  ∃ gc ∈ slots C,
    c2 ∈ (PEqualNP.TopForm.orIn n C gc.2).filter (fun y => G.Adj c1 y) ∧
    ((PEqualNP.TopForm.orIn n C gc.2).filter (fun y => G.Adj c1 y)).card ≤ 6 ∧
    7 ≤ ((PEqualNP.TopForm.orIn n C (n + gc.1)).filter (fun y => G.Adj c1 y)).card ∧
    ∃ s : Fin n, (((PEqualNP.TopForm.orIn n C (n + gc.1)).filter
      (fun y => ¬ G.Adj c1 y)).filter (fun y => ¬ G.Adj s y)).card ≤ 2

lemma twoc_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (TwoC G C) (12 * (2 * C.gates.length)) := by
  classical
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  unfold TwoC
  apply obj_count (slots C) 12
  intro gc _ P hP
  have h := two_level_count 6
    (Finset.univ.filter (fun u : Fin n =>
      7 ≤ ((PEqualNP.TopForm.orIn n C (n + gc.1)).filter (fun y => G.Adj u y)).card ∧
      ∃ s : Fin n, (((PEqualNP.TopForm.orIn n C (n + gc.1)).filter
        (fun y => ¬ G.Adj u y)).filter (fun y => ¬ G.Adj s y)).card ≤ 2))
    (fun c => (PEqualNP.TopForm.orIn n C gc.2).filter (fun y => G.Adj c y)) P
    (fun zv hzv => by
      obtain ⟨a1, a2, a3, a4⟩ := hP zv hzv
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a3, a4⟩, a1, a2⟩)
  have h' := two_centres2 G h4 (PEqualNP.TopForm.orIn n C (n + gc.1))
  calc P.card ≤ 6 * _ := h
    _ ≤ 6 * 2 := Nat.mul_le_mul_left _ h'
    _ = 12 := by norm_num

open PEqualNP.TopForm in
lemma xc1_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (g1 : ℕ) (j1 : Fin 2) (c1 c2 s : Fin n) (hc : HC G C K g1 j1 c1)
    (hc2 : c2 ∈ side (n := n) C g1 ((1 : Fin 2) - j1)) (hadj : G.Adj c1 c2)
    (hs : Sp G C g1 j1 c1 s) : HCsmall G C c1 c2 ∨ TwoC G C c1 c2 := by
  classical
  obtain ⟨hg, hcτ, hτ, _, _⟩ := hc
  by_cases hsm : ((side (n := n) C g1 ((1 : Fin 2) - j1)).filter (fun y => G.Adj c1 y)).card ≤ 6
  · left
    exact ⟨(g1, j1), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (junk_lt G C g1 hg).1, Finset.mem_univ _⟩, hcτ, hτ,
      Finset.mem_filter.mpr ⟨hc2, hadj⟩, hsm⟩
  · right
    have hr := mem_orIn_reach c2 hc2
    have hterm : ¬ (7 ≤ ((orIn n C c2.val).filter (fun y => G.Adj c1 y)).card) := by
      have hsub : (orIn n C c2.val).filter (fun y => G.Adj c1 y) ⊆ {c2} := by
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_singleton.mpr (orIn_input C c2 x hx.1)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    obtain ⟨g, c, hg', hin, hr1, hr2, hr3, hb1, hb2⟩ :=
      path_split C (fun w => 7 ≤ ((orIn n C w).filter (fun y => G.Adj c1 y)).card) c2.val
        hterm _ hr (by
          have : ¬ ((side (n := n) C g1 ((1 : Fin 2) - j1)).filter
            (fun y => G.Adj c1 y)).card ≤ 6 := hsm
          exact Nat.lt_of_not_le this)
    refine ⟨(g, c), slot_mem C hg' hin,
      Finset.mem_filter.mpr ⟨reach_mem_orIn c2 hr3, hadj⟩, Nat.lt_succ_iff.mp (not_le.mp hb2),
      hb1, s, ?_⟩
    exact (Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.filter_subset_filter _ (orIn_mono hr1)))).trans hs.2

def GcP {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) (r : ℕ)
    (c : Fin n) : Prop :=
  ∃ (g : ℕ) (jg : Fin 2), Relation.ReflTransGen (OrStep n C) r (n + g) ∧ HC G C K g jg c ∧
    ∀ s : Fin n, ¬ Sp G C g jg c s

lemma gc_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    {r r' : ℕ} (hr : Relation.ReflTransGen (OrStep n C) r r') {c : Fin n}
    (h : GcP G C K r' c) : GcP G C K r c := by
  obtain ⟨g, jg, h1, h2, h3⟩ := h
  exact ⟨g, jg, hr.trans h1, h2, h3⟩

open PEqualNP.TopForm in
lemma gc_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (x y : Fin n)
    (hx : GcP G C K (opnd C t i) x) (hy : GcP G C K (opnd C t ((1 : Fin 2) - i)) y) :
    G.Adj x y := by
  obtain ⟨g, jg, hr, hc, hgen⟩ := hx
  obtain ⟨g', jg', hr', hc', hgen'⟩ := hy
  obtain ⟨_, h⟩ := x1_lemma G C h4 hAO2 K hK t ht i g jg x g' jg' y
    (reach_orReaches hr g rfl (junk_lt G C g hc.1).1)
    (reach_orReaches hr' g' rfl (junk_lt G C g' hc'.1).1) hc hc'
  rcases h with h | h | h
  · exact h
  · exact absurd h (hgen y)
  · exact absurd h (hgen' x)

def GateGc {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (c1 c2 : Fin n) : Prop :=
  ∃ gj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    c2 ∈ PEqualNP.TopForm.side (n := n) C gj.1 gj.2 ∧
    (PEqualNP.TopForm.side (n := n) C gj.1 gj.2).card ≤ 2 ∧
    ∃ x y : Fin n, x ≠ y ∧ x ∈ PEqualNP.TopForm.side (n := n) C gj.1 gj.2 ∧
      y ∈ PEqualNP.TopForm.side (n := n) C gj.1 gj.2 ∧ G.Adj c1 x ∧ G.Adj c1 y

lemma gategc_bnd {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) : Bnd (GateGc G C) (2 * (2 * C.gates.length)) := by
  classical
  have hc := prod_card C.gates.length
  unfold GateGc
  refine bnd_le (by rw [hc]) (obj_count _ 2 _ ?_)
  intro gj _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, hτ, x0, y0, hne0, hx0, hy0, hax0, hay0⟩ := hP zv0 hzv0
    have hpair : ({x0, y0} : Finset (Fin n)) = PEqualNP.TopForm.side (n := n) C gj.1 gj.2 := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with e | e
        · rw [e]; exact hx0
        · rw [e]; exact hy0
      · rw [Finset.card_pair hne0]; exact hτ
    have hsub : P ⊆ ({zv0.1} : Finset (Fin n)) ×ˢ PEqualNP.TopForm.side (n := n) C gj.1 gj.2 := by
      intro zv hzv
      obtain ⟨hm, _, x, y, hne, hx, hy, hax, hay⟩ := hP zv hzv
      rw [← hpair, Finset.mem_insert, Finset.mem_singleton] at hx hy
      have hboth : G.Adj zv.1 x0 ∧ G.Adj zv.1 y0 := by
        rcases hx with ex | ex <;> rcases hy with ey | ey
        · exact absurd (ex.trans ey.symm) hne
        · rw [ex] at hax; rw [ey] at hay; exact ⟨hax, hay⟩
        · rw [ex] at hax; rw [ey] at hay; exact ⟨hay, hax⟩
        · exact absurd (ex.trans ey.symm) hne
      have e1 : zv.1 = zv0.1 :=
        common_unique G h4 zv.1 zv0.1 x0 y0 hboth.1 hboth.2 hax0 hay0 hne0
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr e1, hm⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_singleton] at hcard
    omega

def GcSlot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (c1 c2 : Fin n) : Prop :=
  ∃ gc ∈ slots C, GcP G C K gc.2 c2 ∧ (∀ y, GcP G C K gc.2 y → y = c2) ∧
    (∃ x y : Fin n, x ≠ y ∧ GcP G C K (n + gc.1) x ∧ GcP G C K (n + gc.1) y) ∧
    (∀ x, GcP G C K (n + gc.1) x → G.Adj c1 x)

lemma gcslot_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) :
    Bnd (GcSlot G C K) (2 * C.gates.length) := by
  have h := obj_count (n := n) (slots C) 1
    (fun gc c1 c2 => GcP G C K gc.2 c2 ∧ (∀ y, GcP G C K gc.2 y → y = c2) ∧
      (∃ x y : Fin n, x ≠ y ∧ GcP G C K (n + gc.1) x ∧ GcP G C K (n + gc.1) y) ∧
      (∀ x, GcP G C K (n + gc.1) x → G.Adj c1 x)) ?_
  · refine bnd_le ?_ h
    have := slots_card C h2
    omega
  · intro gc _ P hP
    rw [Finset.card_le_one]
    intro zv hzv zv' hzv'
    obtain ⟨_, a2, ⟨x, y, hne, hx, hy⟩, a4⟩ := hP zv hzv
    obtain ⟨b1, _, _, b4⟩ := hP zv' hzv'
    have e2 : zv'.2 = zv.2 := a2 zv'.2 b1
    have e1 : zv.1 = zv'.1 :=
      common_unique G h4 zv.1 zv'.1 x y (a4 x hx) (a4 y hy) (b4 x hx) (b4 y hy) hne
    exact Prod.ext e1 e2.symm

def TopGc {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (c1 c2 : Fin n) : Prop :=
  ∃ ti ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    GcP G C K (PEqualNP.TopForm.opnd C ti.1 ti.2) c1 ∧
    GcP G C K (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) c2 ∧
    (∀ y, GcP G C K (PEqualNP.TopForm.opnd C ti.1 ti.2) y → y = c1) ∧
    (∀ y, GcP G C K (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) y → y = c2)

lemma topgc_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) :
    Bnd (TopGc G C K) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold TopGc
  refine bnd_le (by rw [hc]; omega) (obj_count _ 1 _ ?_)
  intro ti _ P hP
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  obtain ⟨_, _, a3, a4⟩ := hP zv hzv
  obtain ⟨b1, b2, _, _⟩ := hP zv' hzv'
  exact Prod.ext (a3 zv'.1 b1).symm (a4 zv'.2 b2).symm

open PEqualNP.TopForm in
lemma xc2_half {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 2 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (c1 : Fin n) (h1 : GcP G C K (opnd C t i) c1)
    (g2 : ℕ) (j2 : Fin 2) (c2 : Fin n)
    (hr2 : Relation.ReflTransGen (OrStep n C) (opnd C t ((1 : Fin 2) - i)) (n + g2))
    (hc2 : HC G C K g2 j2 c2) (hgen2 : ∀ s : Fin n, ¬ Sp G C g2 j2 c2 s)
    (hA : ∃ c', GcP G C K (opnd C t ((1 : Fin 2) - i)) c' ∧ c' ≠ c2) :
    GateGc G C c1 c2 ∨ GcSlot G C K c1 c2 := by
  classical
  have hadj : ∀ x, GcP G C K (opnd C t ((1 : Fin 2) - i)) x → G.Adj c1 x :=
    fun x hx => gc_adj G C h4 hAO2 K (by omega) t ht i c1 x h1 hx
  have hG2 : GcP G C K (n + g2) c2 := ⟨g2, j2, Relation.ReflTransGen.refl, hc2, hgen2⟩
  by_cases hbig : ∃ x y : Fin n, x ≠ y ∧ GcP G C K (n + g2) x ∧ GcP G C K (n + g2) y
  · left
    obtain ⟨x, y, hne, hx, hy⟩ := hbig
    have hside : ∀ z, GcP G C K (n + g2) z → z ∈ side (n := n) C g2 j2 := by
      intro z hz
      obtain ⟨g, jg, hr, hc, _⟩ := hz
      have hgg : g = g2 := by
        have := junk_reach_self G C g2 hc2.1 _ hr
        omega
      rw [hgg] at hc
      by_cases hjj : jg = j2
      · rw [hjj] at hc; exact hc.2.1
      · exfalso
        have e := fin2_ne j2 jg hjj
        have e' : (1 : Fin 2) - j2 = jg := by rw [e, fin2_ss]
        have hsmall := hc.2.2.1
        have hbigd := hc2.2.2.2.2
        rw [e'] at hbigd
        have := Finset.card_le_card (Finset.filter_subset (fun y => ¬ G.Adj c2 y)
          (side (n := n) C g2 jg))
        omega
    refine ⟨(g2, j2), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (junk_lt G C g2 hc2.1).1, Finset.mem_univ _⟩, hc2.2.1, hc2.2.2.1,
      x, y, hne, hside x hx, hside y hy, hadj x (gc_mono G C K hr2 hx),
      hadj y (gc_mono G C K hr2 hy)⟩
  · right
    obtain ⟨c', hc', hne'⟩ := hA
    obtain ⟨g, c, hg, hin, hr1, hr2', hr3, hb1, hb2⟩ :=
      path_split C (fun r => ∃ x y : Fin n, x ≠ y ∧ GcP G C K r x ∧ GcP G C K r y) (n + g2)
        hbig _ hr2 ⟨c', c2, hne', hc', gc_mono G C K hr2 hG2⟩
    have hc2c : GcP G C K c c2 := gc_mono G C K hr3 hG2
    refine ⟨(g, c), slot_mem C hg hin, hc2c, ?_, hb1, ?_⟩
    · intro y hy
      by_contra hne
      exact hb2 ⟨y, c2, hne, hy, hc2c⟩
    · intro x hx
      exact hadj x (gc_mono G C K hr1 hx)

def PayX {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  HCsmall G C u v ∨ HCsmall G C v u ∨ TwoC G C u v ∨ TwoC G C v u ∨ GateGc G C u v ∨
    GateGc G C v u ∨ GcSlot G C K u v ∨ GcSlot G C K v u ∨ TopGc G C K u v ∨ TopGc G C K v u

lemma payx_symm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    {u v : Fin n} (h : PayX G C K u v) : PayX G C K v u := by
  unfold PayX at h ⊢
  tauto

lemma payx_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) :
    Bnd (PayX G C K)
      (12 * (2 * C.gates.length) + (12 * (2 * C.gates.length) + (12 * (2 * C.gates.length) +
        (12 * (2 * C.gates.length) + (2 * (2 * C.gates.length) + (2 * (2 * C.gates.length) +
          (2 * C.gates.length + (2 * C.gates.length + (2 * C.gates.length +
            2 * C.gates.length))))))))) := by
  unfold PayX
  exact bnd_or (hcsmall_bnd G C) (bnd_or (bnd_swap (hcsmall_bnd G C))
    (bnd_or (twoc_bnd G h4 C h2) (bnd_or (bnd_swap (twoc_bnd G h4 C h2))
      (bnd_or (gategc_bnd G h4 C) (bnd_or (bnd_swap (gategc_bnd G h4 C))
        (bnd_or (gcslot_bnd G h4 C h2 K) (bnd_or (bnd_swap (gcslot_bnd G h4 C h2 K))
          (bnd_or (topgc_bnd G C K) (bnd_swap (topgc_bnd G C K))))))))))

open PEqualNP.TopForm in
lemma xc_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 2 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (g1 : ℕ) (j1 : Fin 2) (c1 : Fin n) (g2 : ℕ)
    (j2 : Fin 2) (c2 : Fin n) (hor1 : OrReaches n C (opnd C t i) g1)
    (hor2 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) g2)
    (hc1 : HC G C K g1 j1 c1) (hc2 : HC G C K g2 j2 c2)
    (h21 : c2 ∈ side (n := n) C g1 ((1 : Fin 2) - j1))
    (h12 : c1 ∈ side (n := n) C g2 ((1 : Fin 2) - j2)) (hadj : G.Adj c1 c2) :
    PayX G C K c1 c2 := by
  classical
  have htm := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htm
  by_cases hs1 : ∃ s, Sp G C g1 j1 c1 s
  · obtain ⟨s, hs⟩ := hs1
    rcases xc1_pay G C K g1 j1 c1 c2 s hc1 h21 hadj hs with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  by_cases hs2 : ∃ s, Sp G C g2 j2 c2 s
  · obtain ⟨s, hs⟩ := hs2
    rcases xc1_pay G C K g2 j2 c2 c1 s hc2 h12 hadj.symm hs with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have gen1 : ∀ s : Fin n, ¬ Sp G C g1 j1 c1 s := fun s hs => hs1 ⟨s, hs⟩
  have gen2 : ∀ s : Fin n, ¬ Sp G C g2 j2 c2 s := fun s hs => hs2 ⟨s, hs⟩
  have hr1 := (orReaches_reach g1 _ hor1).1
  have hr2 := (orReaches_reach g2 _ hor2).1
  have hG1 : GcP G C K (opnd C t i) c1 := ⟨g1, j1, hr1, hc1, gen1⟩
  have hG2 : GcP G C K (opnd C t ((1 : Fin 2) - i)) c2 := ⟨g2, j2, hr2, hc2, gen2⟩
  by_cases hA : ∃ c', GcP G C K (opnd C t ((1 : Fin 2) - i)) c' ∧ c' ≠ c2
  · rcases xc2_half G C h4 hAO2 K hK t ht i c1 hG1 g2 j2 c2 hr2 hc2 gen2 hA with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  by_cases hB : ∃ c', GcP G C K (opnd C t i) c' ∧ c' ≠ c1
  · have hr1' : Relation.ReflTransGen (OrStep n C)
        (opnd C t ((1 : Fin 2) - ((1 : Fin 2) - i))) (n + g1) := by
      rw [fin2_ss]; exact hr1
    have hB' : ∃ c', GcP G C K (opnd C t ((1 : Fin 2) - ((1 : Fin 2) - i))) c' ∧ c' ≠ c1 := by
      rw [fin2_ss]; exact hB
    rcases xc2_half G C h4 hAO2 K hK t ht ((1 : Fin 2) - i) c2 hG2 g1 j1 c1 hr1' hc1
      gen1 hB' with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(t, i), Finset.mem_product.mpr ⟨Finset.mem_range.mpr htm.1, Finset.mem_univ _⟩,
        hG1, hG2, ?_, ?_⟩))))))))
    · intro y hy
      by_contra hne
      exact hB ⟨y, hy, hne⟩
    · intro y hy
      by_contra hne
      exact hA ⟨y, hy, hne⟩

open PEqualNP.TopForm in
lemma smallgate_of {n : ℕ} (C : Circuit) (M : ℕ) (g : ℕ) (hg : g < C.gates.length)
    (j : Fin 2) (u v : Fin n) (hU : (side (n := n) C g j).card ≤ M)
    (hV : (side (n := n) C g ((1 : Fin 2) - j)).card ≤ M) (hu : u ∈ side (n := n) C g j)
    (hv : v ∈ side (n := n) C g ((1 : Fin 2) - j)) : SmallGate C M u v := by
  rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
  · rw [e] at hU hu; rw [e'] at hV hv
    exact ⟨g, Finset.mem_range.mpr hg, hU, hV, Finset.mem_union_left _ hu,
      Finset.mem_union_right _ hv⟩
  · rw [e] at hU hu; rw [e'] at hV hv
    exact ⟨g, Finset.mem_range.mpr hg, hV, hU, Finset.mem_union_right _ hu,
      Finset.mem_union_left _ hv⟩

open PEqualNP.TopForm in
lemma classX_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 2 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (h : ℕ) (hh : h ∈ junk G C) (k : ℕ) (hk : k ∈ junk G C)
    (hor0 : OrReaches n C (opnd C t 0) h) (hor1 : OrReaches n C (opnd C t 1) k)
    (u v : Fin n) (huv : G.Adj u v) (jh jk : Fin 2)
    (huh : u ∈ side (n := n) C h jh) (hvh : v ∈ side (n := n) C h ((1 : Fin 2) - jh))
    (hunh : u ∉ side (n := n) C h ((1 : Fin 2) - jh)) (hvnh : v ∉ side (n := n) C h jh)
    (huk : u ∈ side (n := n) C k jk) (hvk : v ∈ side (n := n) C k ((1 : Fin 2) - jk))
    (hunk : u ∉ side (n := n) C k ((1 : Fin 2) - jk)) (hvnk : v ∉ side (n := n) C k jk) :
    CD G C K u v ∨ CD G C K v u ∨ SmallGate C (K + 1) u v ∨ PayX G C K u v := by
  classical
  have e10 : ((1 : Fin 2) - 0) = 1 := by decide
  have hor1' : OrReaches n C (opnd C t ((1 : Fin 2) - 0)) k := by rw [e10]; exact hor1
  have hXu : ∀ d ∈ side (n := n) C h ((1 : Fin 2) - jh),
      ∀ d' ∈ side (n := n) C k ((1 : Fin 2) - jk), ¬ G.Adj u d → ¬ G.Adj u d' → G.Adj d d' := by
    intro d hd d' hd' h1 h2
    obtain ⟨y, z, hyz, hy, hz⟩ := valid4i G C hAO2 t ht 0 h hh k hk hor0 hor1' jh jk
      u d u d' huh hd huk hd'
    exact da_of_four G u d u d' y z hyz hy hz h1 G.irrefl h2 h1 h2
  have hXv : ∀ d ∈ side (n := n) C h jh, ∀ d' ∈ side (n := n) C k jk,
      ¬ G.Adj v d → ¬ G.Adj v d' → G.Adj d d' := by
    intro d hd d' hd' h1 h2
    obtain ⟨y, z, hyz, hy, hz⟩ := valid4i G C hAO2 t ht 0 h hh k hk hor0 hor1' jh jk
      d v d' v hd hvh hd' hvk
    exact da_of_four G v d v d' y z hyz (by tauto) (by tauto) h1 G.irrefl h2 h1 h2
  rcases classX_abs G h4 K (by omega) u v _ _ _ _ huh hvh huk hvk hXu hXv with
    (hp | hp) | (hp | hp) | (hs | hs) | hc | hc
  · exact Or.inl ⟨huv, opnd C h ((1 : Fin 2) - jh), hp.1, hp.2.1, hp.2.2⟩
  · exact Or.inl ⟨huv, opnd C k ((1 : Fin 2) - jk), hp.1, hp.2.1, hp.2.2⟩
  · exact Or.inr (Or.inl ⟨huv.symm, opnd C h jh, hp.1, hp.2.1, hp.2.2⟩)
  · exact Or.inr (Or.inl ⟨huv.symm, opnd C k jk, hp.1, hp.2.1, hp.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl (smallgate_of C (K + 1) h (junk_lt G C h hh).1 jh u v
      hs.1 hs.2 huh hvh)))
  · exact Or.inr (Or.inr (Or.inl (smallgate_of C (K + 1) k (junk_lt G C k hk).1 jk u v
      hs.1 hs.2 huk hvk)))
  · obtain ⟨c1, c2, c3, c5⟩ := hc
    have hHCh : HC G C K h ((1 : Fin 2) - jh) v := by
      refine ⟨hh, hvh, c1, ?_, ?_⟩
      · rw [fin2_ss]; exact hvnh
      · rw [fin2_ss]; exact c2
    have hHCk : HC G C K k jk u := ⟨hk, huk, c3, hunk, c5⟩
    have h21 : u ∈ side (n := n) C h ((1 : Fin 2) - ((1 : Fin 2) - jh)) := by
      rw [fin2_ss]; exact huh
    exact Or.inr (Or.inr (Or.inr (payx_symm G C K
      (xc_pay G C h4 hAO2 K hK t ht 0 h ((1 : Fin 2) - jh) v k jk u hor0 hor1'
        hHCh hHCk h21 hvk huv.symm))))
  · obtain ⟨c1, c2, c3, c5⟩ := hc
    have hHCk : HC G C K k ((1 : Fin 2) - jk) v := by
      refine ⟨hk, hvk, c1, ?_, ?_⟩
      · rw [fin2_ss]; exact hvnk
      · rw [fin2_ss]; exact c2
    have hHCh : HC G C K h jh u := ⟨hh, huh, c3, hunh, c5⟩
    have h12 : u ∈ side (n := n) C k ((1 : Fin 2) - ((1 : Fin 2) - jk)) := by
      rw [fin2_ss]; exact huk
    exact Or.inr (Or.inr (Or.inr
      (xc_pay G C h4 hAO2 K hK t ht 0 h jh u k ((1 : Fin 2) - jk) v hor0 hor1'
        hHCh hHCk hvh h12 huv)))

lemma orient {n : ℕ} (S0 S1 : Finset (Fin n)) (a b : Fin n)
    (r0 : a ∈ S0 ∨ b ∈ S0) (r1 : a ∈ S1 ∨ b ∈ S1)
    (ha : ¬ (a ∈ S0 ∧ a ∈ S1)) (hb : ¬ (b ∈ S0 ∧ b ∈ S1)) :
    (a ∈ S0 ∧ b ∈ S1 ∧ a ∉ S1 ∧ b ∉ S0) ∨ (a ∈ S1 ∧ b ∈ S0 ∧ a ∉ S0 ∧ b ∉ S1) := by
  tauto

open PEqualNP.TopForm in
lemma orient_j {n : ℕ} (C : Circuit) (g : ℕ) (a b : Fin n)
    (r0 : a ∈ side (n := n) C g 0 ∨ b ∈ side (n := n) C g 0)
    (r1 : a ∈ side (n := n) C g 1 ∨ b ∈ side (n := n) C g 1)
    (ha : ¬ (a ∈ side (n := n) C g 0 ∧ a ∈ side (n := n) C g 1))
    (hb : ¬ (b ∈ side (n := n) C g 0 ∧ b ∈ side (n := n) C g 1)) :
    ∃ j : Fin 2, a ∈ side (n := n) C g j ∧ b ∈ side (n := n) C g ((1 : Fin 2) - j) ∧
      a ∉ side (n := n) C g ((1 : Fin 2) - j) ∧ b ∉ side (n := n) C g j := by
  have e10 : ((1 : Fin 2) - 0) = 1 := by decide
  have e11 : ((1 : Fin 2) - 1) = 0 := by decide
  rcases orient _ _ a b r0 r1 ha hb with ⟨h1, h2, h3, h5⟩ | ⟨h1, h2, h3, h5⟩
  · exact ⟨0, h1, by rw [e10]; exact h2, by rw [e10]; exact h3, h5⟩
  · exact ⟨1, h1, by rw [e11]; exact h2, by rw [e11]; exact h3, h5⟩

def Pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  PayD G C K a b ∨ PayD G C K b a ∨ SmallGate C (K + 1) a b ∨ PayX G C K a b

def RWit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (a b : Fin n) : Prop :=
  ∃ t ∈ PEqualNP.TopForm.tops G C,
    (∃ i : Fin 2, ∃ k ∈ PEqualNP.TopForm.junk G C,
      a ∈ PEqualNP.TopForm.side (n := n) C t i ∧
      OrReaches n C (PEqualNP.TopForm.opnd C t ((1 : Fin 2) - i)) k ∧
      (a ∈ PEqualNP.TopForm.side (n := n) C k 0 ∨ b ∈ PEqualNP.TopForm.side (n := n) C k 0) ∧
      (a ∈ PEqualNP.TopForm.side (n := n) C k 1 ∨ b ∈ PEqualNP.TopForm.side (n := n) C k 1)) ∨
    (∃ h ∈ PEqualNP.TopForm.junk G C, ∃ k ∈ PEqualNP.TopForm.junk G C,
      OrReaches n C (PEqualNP.TopForm.opnd C t 0) h ∧
      OrReaches n C (PEqualNP.TopForm.opnd C t 1) k ∧
      (a ∈ PEqualNP.TopForm.side (n := n) C h 0 ∨ b ∈ PEqualNP.TopForm.side (n := n) C h 0) ∧
      (a ∈ PEqualNP.TopForm.side (n := n) C h 1 ∨ b ∈ PEqualNP.TopForm.side (n := n) C h 1) ∧
      (a ∈ PEqualNP.TopForm.side (n := n) C k 0 ∨ b ∈ PEqualNP.TopForm.side (n := n) C k 0) ∧
      (a ∈ PEqualNP.TopForm.side (n := n) C k 1 ∨ b ∈ PEqualNP.TopForm.side (n := n) C k 1))

open PEqualNP.TopForm in
lemma rwit_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 3 ≤ K)
    (a b : Fin n) (hab' : G.Adj a b) (hw : RWit G C a b) : Pay G C K a b := by
  classical
  have e10 : ((1 : Fin 2) - 0) = 1 := by decide
  have e11 : ((1 : Fin 2) - 1) = 0 := by decide
  obtain ⟨t, ht, hw'⟩ := hw
  rcases hw' with ⟨i, k, hk, hside, hor, r0, r1⟩ |
    ⟨h, hh, k, hk, hor1, hor2, r0, r1, r2, r3⟩
  · exact Or.inl (classD_pay G C h4 hAO2 K hK t ht i a b hab' a.val
      (mem_orIn_reach a hside) (Or.inl rfl) k hk hor r0 r1)
  · have hor2' : OrReaches n C (opnd C t ((1 : Fin 2) - 0)) k := by rw [e10]; exact hor2
    have hor1' : OrReaches n C (opnd C t ((1 : Fin 2) - 1)) h := by rw [e11]; exact hor1
    by_cases c1 : a ∈ side (n := n) C h 0 ∧ a ∈ side (n := n) C h 1
    · exact Or.inl (classD_pay G C h4 hAO2 K hK t ht 0 a b hab' (n + h)
        (orReaches_reach h _ hor1).1 (Or.inr ⟨h, hh, rfl, c1.1, c1.2⟩) k hk hor2' r2 r3)
    by_cases c2 : b ∈ side (n := n) C h 0 ∧ b ∈ side (n := n) C h 1
    · exact Or.inr (Or.inl (classD_pay G C h4 hAO2 K hK t ht 0 b a hab'.symm (n + h)
        (orReaches_reach h _ hor1).1 (Or.inr ⟨h, hh, rfl, c2.1, c2.2⟩) k hk hor2'
        r2.symm r3.symm))
    by_cases c3 : a ∈ side (n := n) C k 0 ∧ a ∈ side (n := n) C k 1
    · exact Or.inl (classD_pay G C h4 hAO2 K hK t ht 1 a b hab' (n + k)
        (orReaches_reach k _ hor2).1 (Or.inr ⟨k, hk, rfl, c3.1, c3.2⟩) h hh hor1' r0 r1)
    by_cases c5 : b ∈ side (n := n) C k 0 ∧ b ∈ side (n := n) C k 1
    · exact Or.inr (Or.inl (classD_pay G C h4 hAO2 K hK t ht 1 b a hab'.symm (n + k)
        (orReaches_reach k _ hor2).1 (Or.inr ⟨k, hk, rfl, c5.1, c5.2⟩) h hh hor1'
        r0.symm r1.symm))
    obtain ⟨jh, x1, x2, x3, x5⟩ := orient_j C h a b r0 r1 c1 c2
    obtain ⟨jk, y1, y2, y3, y5⟩ := orient_j C k a b r2 r3 c3 c5
    rcases classX_pay G C h4 hAO2 K (by omega) t ht h hh k hk hor1 hor2 a b hab'
      jh jk x1 x2 x3 x5 y1 y2 y3 y5 with hx | hx | hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))

open PEqualNP.TopForm in
lemma pay_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay G C 5) (2212 * C.gates.length) := by
  have hb := bnd_or (payd_bnd G C h4 hAO2 h2 5 (by norm_num))
    (bnd_or (bnd_swap (payd_bnd G C h4 hAO2 h2 5 (by norm_num)))
      (bnd_or (smallgate_bnd (n := n) C (5 + 1)) (payx_bnd G h4 C h2 5)))
  unfold Pay
  refine bnd_le ?_ hb
  norm_num
  omega

open PEqualNP.TopForm in
lemma rect_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (C : Circuit)
    (hAO2 : IsAO2 n C)
    (F : Finset (Sym2 (Fin n)))
    (hF : ∀ e ∈ F, ∃ a b : Fin n, e = s(a, b) ∧ G.Adj a b ∧ RWit G C a b) :
    F.card ≤ 2212 * (C.size + 1) := by
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) :=
    fun a b c d hac hbd h => no4 G hg a b c d h.1 h.2.1 h.2.2.1 h.2.2.2 hac hbd
  have h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg' => le_of_eq (hAO2.2.2 g hg')
  have hcard := edges_bnd (Pay G C 5) _ (pay_bnd G C h4 hAO2 h2) F
    (fun e he => by
      obtain ⟨a, b, h1, hadj, hw⟩ := hF e he
      exact ⟨a, b, h1, rwit_pay G C h4 hAO2 5 (by norm_num) a b hadj hw⟩)
  have hs : C.size = C.gates.length := rfl
  rw [hs]
  omega

open PEqualNP.TopForm in
noncomputable def ijunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset ℕ := by
  classical
  exact (junk G C).filter (fun k => ∀ j ∈ junk G C, ¬ InCone n C j k)

open PEqualNP.TopForm in
lemma mem_ijunk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ ijunk G C ↔ k ∈ junk G C ∧ ∀ j ∈ junk G C, ¬ InCone n C j k := by
  classical
  simp [ijunk]

open PEqualNP.TopForm in
lemma cone_all_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : AndOrOnly C) (hT : PEqualNP.TopForm.TopForm G C)
    (h : ℕ) (hj : h ∈ ijunk G C) (h' : ℕ) (hh' : h' < C.gates.length)
    (hnor : (gateAt C h').op ≠ GateOp.or) : ¬ InCone n C h' h := by
  intro hcone
  obtain ⟨hjj, hin⟩ := mem_ijunk.mp hj
  have hjm := hjj
  unfold junk gatesWhere at hjm
  obtain ⟨hlen, hdirty⟩ := Finset.mem_filter.mp hjm
  have hlen' := Finset.mem_range.mp hlen
  have hand : (gateAt C h).op = GateOp.and := hdirty.1
  have hhand : (gateAt C h').op = GateOp.and := by
    rcases hAO _ (gateAt_mem hh') with h3 | h3
    · exact h3
    · exact (hnor h3).elim
  by_cases hb : BelowF G C h'
  · exact hT h' hh' h hlen' hhand hb hand hcone
  · have hd : IsDirtyAnd n G C h' := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh', ?_⟩
      by_contra hne
      apply hb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hj' : h' ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh', hd⟩
    exact hin h' hj' hcone

open PEqualNP.TopForm in
lemma junk_operand_val {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : AndOrOnly C) (hT : PEqualNP.TopForm.TopForm G C)
    (h : ℕ) (hj : h ∈ ijunk G C) (hlen : h < C.gates.length)
    (p : ℕ) (hpin : p ∈ (gateAt C h).inputs) (hp : p < n + h) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔ ∃ t ∈ orIn n C p, x t = true := by
  constructor
  · intro hv
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) p hv
    rcases hw' with hlt | ⟨h', hh', rfl, hop⟩
    · refine ⟨⟨w', hlt⟩, reach_mem_orIn ⟨w', hlt⟩ hr, ?_⟩
      have h1 := val_ofFn C x ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
      exact h1.symm
    · exact absurd (operand_cone hlen hpin hp hr) (cone_all_or G C hAO hT h hj h' hh' hop)
  · rintro ⟨t, ht, hx⟩
    exact reach_var_val x p t (mem_orIn_reach t ht) hx

open PEqualNP.TopForm in
lemma ijunk_rect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (h : ℕ) (hj : h ∈ ijunk G C) (x : Fin n → Bool) :
    gateVal n C h x = true ↔
      (∃ a ∈ side (n := n) C h 0, x a = true) ∧ (∃ b ∈ side (n := n) C h 1, x b = true) := by
  obtain ⟨hAO, hRB, h2⟩ := hAO2
  have hjm := (mem_ijunk.mp hj).1
  unfold junk gatesWhere at hjm
  obtain ⟨hlen0, hdirty⟩ := Finset.mem_filter.mp hjm
  have hlen := Finset.mem_range.mp hlen0
  have hand : (gateAt C h).op = GateOp.and := hdirty.1
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hlen))
  have e0 : opnd C h 0 = p := by simp [opnd, hin]
  have e1 : opnd C h 1 = q := by simp [opnd, hin]
  have hpin : p ∈ (gateAt C h).inputs := by rw [hin]; simp
  have hqin : q ∈ (gateAt C h).inputs := by rw [hin]; simp
  have hp : p < n + h := hRB h hlen p hpin
  have hq : q < n + h := hRB h hlen q hqin
  rw [gateVal_eq_val, val_and (n := n) (by simp) hlen hand, hin]
  simp only [side, e0, e1]
  rw [← junk_operand_val G C hAO hT h hj hlen p hpin hp x,
    ← junk_operand_val G C hAO hT h hj hlen q hqin hq x]
  constructor
  · intro hall
    exact ⟨(hall p (by simp)).2, (hall q (by simp)).2⟩
  · rintro ⟨h1, h2'⟩ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hp, h1⟩
    · exact ⟨hq, h2'⟩

open PEqualNP.TopForm in
lemma irect_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (k : ℕ) (hk : k ∈ ijunk G C) (a b : Fin n)
    (hv : gateVal n C k (pairInput a b) = true) :
    (a ∈ side (n := n) C k 0 ∨ b ∈ side (n := n) C k 0) ∧
      (a ∈ side (n := n) C k 1 ∨ b ∈ side (n := n) C k 1) := by
  obtain ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩ := (ijunk_rect G C hAO2 hT k hk _).mp hv
  rw [pairInput_true] at hsx htx
  constructor
  · rcases hsx with rfl | rfl
    · exact Or.inl hs
    · exact Or.inr hs
  · rcases htx with rfl | rfl
    · exact Or.inl ht
    · exact Or.inr ht

def Wit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (a b : Fin n) : Prop :=
  ∃ t ∈ PEqualNP.TopForm.tops G C,
    (∃ i : Fin 2, ∃ k ∈ ijunk G C, a ∈ PEqualNP.TopForm.side (n := n) C t i ∧
      OrReaches n C (PEqualNP.TopForm.opnd C t ((1 : Fin 2) - i)) k ∧
      gateVal n C k (pairInput a b) = true) ∨
    (∃ h ∈ ijunk G C, ∃ k ∈ ijunk G C,
      OrReaches n C (PEqualNP.TopForm.opnd C t 0) h ∧
      OrReaches n C (PEqualNP.TopForm.opnd C t 1) k ∧
      gateVal n C h (pairInput a b) = true ∧ gateVal n C k (pairInput a b) = true)

open PEqualNP.TopForm in
lemma wit_rwit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C) (a b : Fin n)
    (hw : Wit G C a b) : RWit G C a b := by
  obtain ⟨t, ht, hw'⟩ := hw
  rcases hw' with ⟨i, k, hk, hside, hor, hv⟩ | ⟨h, hh, k, hk, hor1, hor2, hv1, hv2⟩
  · obtain ⟨r0, r1⟩ := irect_pair G C hAO2 hT k hk a b hv
    exact ⟨t, ht, Or.inl ⟨i, k, (mem_ijunk.mp hk).1, hside, hor, r0, r1⟩⟩
  · obtain ⟨r0, r1⟩ := irect_pair G C hAO2 hT h hh a b hv1
    obtain ⟨r2, r3⟩ := irect_pair G C hAO2 hT k hk a b hv2
    exact ⟨t, ht, Or.inr ⟨h, (mem_ijunk.mp hh).1, k, (mem_ijunk.mp hk).1, hor1, hor2,
      r0, r1, r2, r3⟩⟩

open PEqualNP.TopForm in
lemma local_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (C : Circuit)
    (hAO2 : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (F : Finset (Sym2 (Fin n)))
    (hF : ∀ e ∈ F, ∃ a b : Fin n, e = s(a, b) ∧ G.Adj a b ∧ Wit G C a b) :
    F.card ≤ 2212 * (C.size + 1) :=
  rect_bound G hg C hAO2 F (fun e he => by
    obtain ⟨a, b, h1, hadj, hw⟩ := hF e he
    exact ⟨a, b, h1, hadj, wit_rwit G C hAO2 hT a b hw⟩)

end PEqualNP.Outside.L_meta_8393

theorem PEqualNP.Outside.L_meta_8393 :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ (x9 : Finset (Sym2 (Fin x2))), (∀ x10 ∈ x9, x10 ∈ PEqualNP.TopForm.Ustar x3 x5 ∧ ∃ (x12 : Fin x2) (x13 : Fin x2), x10 = s(x12, x13) ∧ ∃ x14 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x15 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x16 ∈ PEqualNP.TopForm.junk x3 x5, x15 ≠ x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x14 (0 : Fin (2 : ℕ))) x15 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x14 (1 : Fin (2 : ℕ))) x16 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x16 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ (∀ x17 ∈ PEqualNP.TopForm.junk x3 x5, ¬PEqualNP.EdgeOwnership.InCone x2 x5 x17 x15) ∧ ∀ x17 ∈ PEqualNP.TopForm.junk x3 x5, ¬PEqualNP.EdgeOwnership.InCone x2 x5 x17 x16) → x9.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  refine ⟨2212, ?_⟩
  intro n G _ C hg hleast htop F hF
  apply PEqualNP.Outside.L_meta_8393.local_bound G hg C hleast.1 htop F
  intro e he
  rcases hF e he with ⟨hU, a, b, hab, t, ht, j, hj, k, hk, _, hrj, hrk, hvj, hvk, hnj, hnk⟩
  subst e
  have hedge : G.Adj a b := by
    simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] at hU
    exact hU.1
  exact ⟨a, b, rfl, hedge, t, ht, Or.inr ⟨j,
    PEqualNP.Outside.L_meta_8393.mem_ijunk.mpr ⟨hj, hnj⟩, k,
    PEqualNP.Outside.L_meta_8393.mem_ijunk.mpr ⟨hk, hnk⟩, hrj, hrk, hvj, hvk⟩⟩
