import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1878

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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
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

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp only [pairInput]
  exact decide_eq_decide.mpr or_comm

open PEqualNP.TopForm in
lemma caseA {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (u v : Fin n)
    (a : ℕ) (hatop : a ∈ tops G C) (i : Fin 2) (h : ℕ) (hjunk : h ∈ junk G C) (t1 : Fin n)
    (ht1 : t1 = u ∨ t1 = v) (hside : t1 ∈ side (n := n) C a i)
    (hor : OrReaches n C (opnd C a ((1 : Fin 2) - i)) h)
    (hv : gateVal n C h (pairInput u v) = true) :
    ∃ (x9 : Fin n) (x10 : Fin n), s(u, v) = s(x9, x10) ∧ ∃ x11 ∈ tops G C, ∃ (x12 : Fin 2),
      ∃ x13 ∈ junk G C, x9 ∈ side C x11 x12 ∧
        OrReaches n C (opnd C x11 ((1 : Fin 2) - x12)) x13 ∧
        gateVal n C x13 (pairInput x9 x10) = true := by
  rcases ht1 with h1 | h1
  · rw [h1] at hside
    exact ⟨u, v, rfl, a, hatop, i, h, hjunk, hside, hor, hv⟩
  · rw [h1] at hside
    exact ⟨v, u, Sym2.eq_swap, a, hatop, i, h, hjunk, hside, hor, by
      rw [pairInput_comm]; exact hv⟩

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    (∃ (x9 : Fin n) (x10 : Fin n), s(u, v) = s(x9, x10) ∧ ∃ x11 ∈ tops G C, ∃ (x12 : Fin 2),
      ∃ x13 ∈ junk G C, x9 ∈ side C x11 x12 ∧
        OrReaches n C (opnd C x11 ((1 : Fin 2) - x12)) x13 ∧
        gateVal n C x13 (pairInput x9 x10) = true) ∨
    ∃ (x9 : Fin n) (x10 : Fin n), s(u, v) = s(x9, x10) ∧ ∃ x11 ∈ tops G C,
      ∃ x12 ∈ junk G C, ∃ x13 ∈ junk G C, x12 ≠ x13 ∧
        OrReaches n C (opnd C x11 (0 : Fin 2)) x12 ∧
        OrReaches n C (opnd C x11 (1 : Fin 2)) x13 ∧
        gateVal n C x12 (pairInput x9 x10) = true ∧
        gateVal n C x13 (pairInput x9 x10) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have d0 : opnd C a ((1 : Fin 2) - 0) = q := by
    rw [show ((1 : Fin 2) - 0) = 1 from by decide]; exact e1
  have d1 : opnd C a ((1 : Fin 2) - 1) = p := by
    rw [show ((1 : Fin 2) - 1) = 0 from by decide]; exact e0
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hpin : p ∈ (gateAt C a).inputs := by rw [hin]; simp
  have hqin : q ∈ (gateAt C a).inputs := by rw [hin]; simp
  have hp := hpq p hpin
  have hq := hpq q hqin
  have junk_of : ∀ (w : ℕ), w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      h ∈ junk G C ∧ OrReaches n C w h ∧ ¬ BelowF G C h := by
    intro w hwin hwlt h hh hhor hr
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    exact ⟨hjunk, reach_orReaches hr h rfl hh, hnb⟩
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · obtain ⟨hjunk, hor, _⟩ := junk_of q hqin hq.1 h hh hhor hr
      left
      refine caseA G C u v a hatop 0 h hjunk t1 ht1 ?_ ?_ hv
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · rw [d0]; exact hor
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨k, hk, hkor, hrk, hvk⟩
    · obtain ⟨hjunk, hor, _⟩ := junk_of p hpin hp.1 h hh hhor hr
      left
      refine caseA G C u v a hatop 1 h hjunk t2 ht2 ?_ ?_ hv
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
      · rw [d1]; exact hor
    · obtain ⟨hjunk, hor, hnb⟩ := junk_of p hpin hp.1 h hh hhor hr
      obtain ⟨hjunkk, hork, _⟩ := junk_of q hqin hq.1 k hk hkor hrk
      right
      refine ⟨u, v, rfl, a, hatop, h, hjunk, k, hjunkk, ?_, ?_, ?_, hv, hvk⟩
      · intro heq
        subst heq
        apply hnb
        intro x hx
        apply hbel x
        show val C (List.ofFn x) (n + a) = true
        rw [val_and (n := n) (by simp) halen hop, hin]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hp.1, orStep_up (n := n) (by simp) hr hx⟩
        · exact ⟨hq.1, orStep_up (n := n) (by simp) hrk hx⟩
      · rw [e0]; exact hor
      · rw [e1]; exact hork

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

def rd (n : ℕ) (C : Circuit) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ k < C.gates.length, (i : ℕ) ∈ (gateAt C k).inputs

lemma rd_card (n : ℕ) (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (rd n C).card ≤ 2 * C.gates.length := by
  have hsub : (rd n C).image (fun i => i.val) ⊆
      (Finset.range C.gates.length ×ˢ Finset.range 2).image
        (fun p => (gateAt C p.1).inputs.getD p.2 0) := by
    intro w hw
    simp only [rd, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨i, ⟨k, hk, hin⟩, rfl⟩ := hw
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
    rw [hab] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    refine Finset.mem_image.mpr ?_
    rcases hin with h | h
    · exact ⟨(k, 0), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hk, Finset.mem_range.mpr (by norm_num)⟩, by
          show (gateAt C k).inputs.getD 0 0 = i.val
          rw [hab, h]; rfl⟩
    · exact ⟨(k, 1), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hk, Finset.mem_range.mpr (by norm_num)⟩, by
          show (gateAt C k).inputs.getD 1 0 = i.val
          rw [hab, h]; rfl⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h1
  have h3 := Finset.card_image_le (s := Finset.range C.gates.length ×ˢ Finset.range 2)
    (f := fun p => (gateAt C p.1).inputs.getD p.2 0)
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at h3
  omega

lemma orIn_sub_rd {n : ℕ} {C : Circuit} {k w : ℕ} (hk : k < C.gates.length)
    (hw : w ∈ (gateAt C k).inputs) : PEqualNP.TopForm.orIn n C w ⊆ rd n C := by
  intro u hu
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  simp only [rd, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hu with h | ⟨k2, hk2, _, _, hin⟩
  · exact ⟨k, hk, by rw [h]; exact hw⟩
  · exact ⟨k2, hk2, hin⟩

lemma biclique_card {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (P Q : Finset (Fin n)) (hab : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b) :
    ((P ×ˢ Q).image (fun p => s(p.1, p.2))).card ≤ P.card + Q.card := by
  have h1 := Finset.card_image_le (s := P ×ˢ Q) (f := fun p => s(p.1, p.2))
  rw [Finset.card_product] at h1
  rcases biclique_star G h4 P Q hab with h | h
  · have h3 : P.card * Q.card ≤ 1 * Q.card := Nat.mul_le_mul_right _ h
    omega
  · have h3 : P.card * Q.card ≤ P.card * 1 := Nat.mul_le_mul_left _ h
    omega

open PEqualNP.TopForm in
lemma main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hg5 : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (g : ℕ) (hj : junk G C = {g}) :
    (Ustar G C).card ≤ 12 * (C.size + 1) := by
  have hL2 := hL
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) :=
    fun a b c d hac hbd h => no4 G hg5 a b c d h.1 h.2.1 h.2.2.1 h.2.2.2 hac hbd
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hgj : g ∈ junk G C := by rw [hj]; exact Finset.mem_singleton_self g
  unfold junk gatesWhere at hgj
  have hgd : IsDirtyAnd n G C g := (Finset.mem_filter.mp hgj).2
  have hglen : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hgj).1
  have hgand : (gateAt C g).op = GateOp.and := hgd.1
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hglen))
  have hpin : p ∈ (gateAt C g).inputs := by rw [hin]; simp
  have hqin : q ∈ (gateAt C g).inputs := by rw [hin]; simp
  have hplt : p < n + g := hRB g hglen p hpin
  have hqlt : q < n + g := hRB g hglen q hqin
  have g_up : ∀ (x : Fin n → Bool) (α β : Fin n), α ∈ orIn n C p → β ∈ orIn n C q →
      x α = true → x β = true → gateVal n C g x = true := by
    intro x α β hα hβ hxα hxβ
    show val C (List.ofFn x) (n + g) = true
    rw [val_and (n := n) (by simp) hglen hgand]
    intro i hi
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · rw [hi]; exact ⟨hplt, reach_var_val x _ α (mem_orIn_reach α hα) hxα⟩
    · rw [hi]; exact ⟨hqlt, reach_var_val x _ β (mem_orIn_reach β hβ) hxβ⟩
  have g_down : ∀ (u v : Fin n) (w : ℕ), w ∈ (gateAt C g).inputs → w < n + g →
      val C (List.ofFn (pairInput u v)) w = true → ∃ t ∈ orIn n C w, t = u ∨ t = v := by
    intro u v w hwin hwlt hv
    rcases operand_trace (C := C) u v w hv with ⟨t, ht, hr⟩ | ⟨h, hh, hhor, hr, hvh⟩
    · exact ⟨t, reach_mem_orIn t hr, ht⟩
    · exfalso
      have hhand : (gateAt C h).op = GateOp.and := by
        rcases hAO _ (gateAt_mem hh) with h3 | h3
        · exact h3
        · exact (hhor h3).elim
      have hcone : InCone n C h g := operand_cone hglen hwin hwlt hr
      have hnb : ¬ BelowF G C h := fun hb2 => hT h hh g hglen hhand hb2 hgand hcone
      have hdirty : IsDirtyAnd n G C h := by
        unfold IsDirtyAnd IsDirty
        refine ⟨hhand, hh, ?_⟩
        by_contra hne
        apply hnb
        intro x hx
        by_contra hfx
        exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
      have hjunk : h ∈ junk G C := by
        unfold junk gatesWhere
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
      rw [hj, Finset.mem_singleton] at hjunk
      have hle := orStep_le hr
      omega
  have top_w : ∀ (t : ℕ) (i : Fin 2) (u : Fin n), t ∈ tops G C → u ∈ side (n := n) C t i →
      OrReaches n C (opnd C t ((1 : Fin 2) - i)) g → u ∈ wmax G C g ∧ u ∈ rd n C := by
    intro t i u ht hu hor
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htlen, htand, htbel⟩ := ht
    obtain ⟨p2, q2, hin2⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem htlen))
    have e0 : opnd C t 0 = p2 := by simp [opnd, hin2]
    have e1 : opnd C t 1 = q2 := by simp [opnd, hin2]
    have hp2in : p2 ∈ (gateAt C t).inputs := by rw [hin2]; simp
    have hq2in : q2 ∈ (gateAt C t).inputs := by rw [hin2]; simp
    refine ⟨?_, ?_⟩
    · simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hgx hxu
      apply htbel
      have key : ∀ b : Fin 2, val C (List.ofFn x) (opnd C t b) = true := by
        intro b
        rcases fin2_cases i b with hb | hb
        · rw [hb]; exact reach_var_val x _ u (mem_orIn_reach u hu) hxu
        · rw [hb]; exact orStep_up (n := n) (by simp) (orReaches_reach g _ hor).1 hgx
      show val C (List.ofFn x) (n + t) = true
      rw [val_and (n := n) (by simp) htlen htand]
      intro w hw
      have hwlt := hRB t htlen w hw
      rw [hin2] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      refine ⟨hwlt, ?_⟩
      rcases hw with hw | hw
      · rw [hw, ← e0]; exact key 0
      · rw [hw, ← e1]; exact key 1
    · have hmem : opnd C t i ∈ (gateAt C t).inputs := by
        rcases fin2_cases 0 i with hb | hb
        · rw [hb, e0]; exact hp2in
        · rw [hb, show ((1 : Fin 2) - 0) = 1 from by decide, e1]; exact hq2in
      exact orIn_sub_rd htlen hmem hu
  have wadj : ∀ (a b α β : Fin n), a ∈ wmax G C g → α ∈ orIn n C p → β ∈ orIn n C q →
      (α = a ∨ α = b) → (β = a ∨ β = b) → G.Adj a b := by
    intro a b α β ha hα hβ hα2 hβ2
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    apply hF
    exact ha _ (g_up _ α β hα hβ ((pairInput_true a b α).mpr hα2) ((pairInput_true a b β).mpr hβ2))
      (pairInput_left a b)
  have mk : ∀ (P Q : Finset (Fin n)) (a b : Fin n), a ∈ P → b ∈ Q →
      s(a, b) ∈ (P ×ˢ Q).image (fun p => s(p.1, p.2)) :=
    fun P Q a b ha hb => Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  have hsub : Ustar G C ⊆
      (((wmax G C g ∩ rd n C) ×ˢ (orIn n C p ∩ orIn n C q)).image (fun p => s(p.1, p.2)) ∪
        ((wmax G C g ∩ orIn n C p) ×ˢ orIn n C q).image (fun p => s(p.1, p.2))) ∪
        ((wmax G C g ∩ orIn n C q) ×ˢ orIn n C p).image (fun p => s(p.1, p.2)) := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro huv
      rcases off_star G C hL2 hT u v huv with
        ⟨x9, x10, hs, t, ht, i, h, hh, hside, hor, hval⟩ |
        ⟨x9, x10, hs, t, ht, h1, hh1, h3, hh3, hne, _⟩
      · rw [hj, Finset.mem_singleton] at hh
        rw [hh] at hor hval
        obtain ⟨hw, hR⟩ := top_w t i x9 ht hside hor
        have hval2 : val C (List.ofFn (pairInput x9 x10)) (n + g) = true := hval
        have hpq := (val_and (n := n) (by simp) hglen hgand).mp hval2
        obtain ⟨α, hα, hα2⟩ := g_down x9 x10 p hpin hplt (hpq p hpin).2
        obtain ⟨β, hβ, hβ2⟩ := g_down x9 x10 q hqin hqlt (hpq q hqin).2
        rw [hs]
        rcases hα2 with e1 | e1 <;> rcases hβ2 with e2 | e2
        · rw [e1] at hα; rw [e2] at hβ
          exact (G.irrefl (wadj x9 x9 x9 x9 hw hα hβ (Or.inl rfl) (Or.inl rfl))).elim
        · rw [e1] at hα; rw [e2] at hβ
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (mk _ _ x9 x10 (Finset.mem_inter.mpr ⟨hw, hα⟩) hβ))
        · rw [e1] at hα; rw [e2] at hβ
          exact Finset.mem_union_right _ (mk _ _ x9 x10 (Finset.mem_inter.mpr ⟨hw, hβ⟩) hα)
        · rw [e1] at hα; rw [e2] at hβ
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (mk _ _ x9 x10 (Finset.mem_inter.mpr ⟨hw, hR⟩) (Finset.mem_inter.mpr ⟨hα, hβ⟩)))
      · rw [hj, Finset.mem_singleton] at hh1 hh3
        exact (hne (hh1.trans hh3.symm)).elim
  have hA : orIn n C p ⊆ rd n C := orIn_sub_rd hglen hpin
  have hB : orIn n C q ⊆ rd n C := orIn_sub_rd hglen hqin
  have c1 := biclique_card G h4 (wmax G C g ∩ rd n C) (orIn n C p ∩ orIn n C q) (by
    intro a ha b hb
    rw [Finset.mem_inter] at ha hb
    exact wadj a b b b ha.1 hb.1 hb.2 (Or.inr rfl) (Or.inr rfl))
  have c2 := biclique_card G h4 (wmax G C g ∩ orIn n C p) (orIn n C q) (by
    intro a ha b hb
    rw [Finset.mem_inter] at ha
    exact wadj a b a b ha.1 ha.2 hb (Or.inl rfl) (Or.inr rfl))
  have c3 := biclique_card G h4 (wmax G C g ∩ orIn n C q) (orIn n C p) (by
    intro a ha b hb
    rw [Finset.mem_inter] at ha
    exact wadj a b b a ha.1 hb ha.2 (Or.inr rfl) (Or.inl rfl))
  have d1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := wmax G C g) (s₂ := rd n C))
  have d2 := Finset.card_le_card
    ((Finset.inter_subset_left (s₁ := orIn n C p) (s₂ := orIn n C q)).trans hA)
  have d3 := Finset.card_le_card
    ((Finset.inter_subset_right (s₁ := wmax G C g) (s₂ := orIn n C p)).trans hA)
  have d4 := Finset.card_le_card
    ((Finset.inter_subset_right (s₁ := wmax G C g) (s₂ := orIn n C q)).trans hB)
  have d5 := Finset.card_le_card hA
  have d6 := Finset.card_le_card hB
  have hr := rd_card n C h2
  have hu := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    (((wmax G C g ∩ rd n C) ×ˢ (orIn n C p ∩ orIn n C q)).image (fun p => s(p.1, p.2)) ∪
        ((wmax G C g ∩ orIn n C p) ×ˢ orIn n C q).image (fun p => s(p.1, p.2)))
    (((wmax G C g ∩ orIn n C q) ×ˢ orIn n C p).image (fun p => s(p.1, p.2)))
  have u2 := Finset.card_union_le
    (((wmax G C g ∩ rd n C) ×ˢ (orIn n C p ∩ orIn n C q)).image (fun p => s(p.1, p.2)))
    (((wmax G C g ∩ orIn n C p) ×ˢ orIn n C q).image (fun p => s(p.1, p.2)))
  have hsz : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_1878

theorem PEqualNP.Outside.L_meta_1878 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → PEqualNP.TopForm.junk x3 x7 = {x8} → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  exact ⟨12, fun n G _ hg5 _ C g hL hT hj =>
    PEqualNP.Outside.L_meta_1878.main G C hg5 hL hT g hj⟩
