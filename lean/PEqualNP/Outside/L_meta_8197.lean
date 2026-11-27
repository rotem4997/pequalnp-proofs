import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8197

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

open PEqualNP.TopForm in
lemma valid3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (s : Fin n) (hs : s ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (b c : Fin n) (hb : b ∈ side (n := n) C k 0) (hc : c ∈ side (n := n) C k 1) :
    ∃ y z : Fin n, G.Adj y z ∧ (y = s ∨ y = b ∨ y = c) ∧ (z = s ∨ z = b ∨ z = c) := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ w : Fin n, X w = true ↔ (w = s ∨ w = b ∨ w = c) :=
    ⟨fun w => decide (w = s ∨ w = b ∨ w = c), fun w => by simp⟩
  have hkv : gateVal n C k X = true :=
    (junk_rect G C hAO2 k hk X)
      ⟨⟨b, hb, (hx b).mpr (Or.inr (Or.inl rfl))⟩, ⟨c, hc, (hx c).mpr (Or.inr (Or.inr rfl))⟩⟩
  have hsv := side_leaf C t i s hs X ((hx s).mpr (Or.inl rfl))
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
  exact ⟨y, z, hyz, (hx y).mp hy, (hx z).mp hz⟩

open PEqualNP.TopForm in
lemma valid4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (h : ℕ) (hh : h ∈ junk G C) (k : ℕ) (hk : k ∈ junk G C)
    (hor0 : OrReaches n C (opnd C t 0) h) (hor1 : OrReaches n C (opnd C t 1) k)
    (a1 b1 a2 b2 : Fin n) (ha1 : a1 ∈ side (n := n) C h 0) (hb1 : b1 ∈ side (n := n) C h 1)
    (ha2 : a2 ∈ side (n := n) C k 0) (hb2 : b2 ∈ side (n := n) C k 1) :
    ∃ y z : Fin n, G.Adj y z ∧ (y = a1 ∨ y = b1 ∨ y = a2 ∨ y = b2) ∧
      (z = a1 ∨ z = b1 ∨ z = a2 ∨ z = b2) := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
      ∀ w : Fin n, X w = true ↔ (w = a1 ∨ w = b1 ∨ w = a2 ∨ w = b2) :=
    ⟨fun w => decide (w = a1 ∨ w = b1 ∨ w = a2 ∨ w = b2), fun w => by simp⟩
  have hhv : gateVal n C h X = true :=
    (junk_rect G C hAO2 h hh X)
      ⟨⟨a1, ha1, (hx a1).mpr (Or.inl rfl)⟩, ⟨b1, hb1, (hx b1).mpr (Or.inr (Or.inl rfl))⟩⟩
  have hkv : gateVal n C k X = true :=
    (junk_rect G C hAO2 k hk X)
      ⟨⟨a2, ha2, (hx a2).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩,
        ⟨b2, hb2, (hx b2).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩⟩
  have hF := top_sound G C hAO2 t ht X (junk_leaf C _ h hor0 X hhv) (junk_leaf C _ k hor1 X hkv)
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  exact ⟨y, z, hyz, (hx y).mp hy, (hx z).mp hz⟩

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
lemma fires_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (w k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C w k) (u : Fin n)
    (h0 : u ∈ side (n := n) C k 0) (h1 : u ∈ side (n := n) C k 1) : Fires n C w u :=
  fun X hX => junk_leaf C w k hr X
    ((junk_rect G C hAO2 k hk X) ⟨⟨u, h0, hX⟩, ⟨u, h1, hX⟩⟩)

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

lemma bnd_imp {n : ℕ} {R R' : Fin n → Fin n → Prop} {c : ℕ}
    (h : ∀ x y, R x y → R' x y) (hb : Bnd R' c) : Bnd R c :=
  fun P hP => hb P (fun zv hzv => h _ _ (hP zv hzv))

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
lemma cd1_two_common {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (z : Fin n) (hz : Fires n C (opnd C t i) z)
    (h : ℕ) (hh : h ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) h)
    (x y : Fin n) (hx0 : x ∈ side (n := n) C h 0) (hx1 : x ∈ side (n := n) C h 1)
    (hy0 : y ∈ side (n := n) C h 0) (hy1 : y ∈ side (n := n) C h 1) (hxy : y ≠ x) :
    CD G C 1 z x := by
  have hclean := fun b hb c hc => clean_rect G C hAO2 t ht i z hz h hh hor b c hb hc
  have hzx : G.Adj z x := by
    by_contra hn
    exact G.irrefl (hclean x hx0 x hx1 hn hn)
  have hzy : G.Adj z y := by
    by_contra hn
    exact G.irrefl (hclean y hy0 y hy1 hn hn)
  rcases dirt_star G h4 z _ _ hclean with hd | hd
  · exact cd_of_O1 G C h 0 z x hzx ⟨hx0, ⟨y, hy0, hxy, hzy⟩, hd⟩
  · exact cd_of_O1 G C h 1 z x hzx ⟨hx1, ⟨y, hy1, hxy, hzy⟩, hd⟩

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

open PEqualNP.TopForm in
lemma clean_rect_j {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u : Fin n) (hu : Fires n C (opnd C t i) u)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (b c : Fin n) (hb : b ∈ side (n := n) C k j)
    (hc : c ∈ side (n := n) C k ((1 : Fin 2) - j))
    (hub : ¬ G.Adj u b) (huc : ¬ G.Adj u c) : G.Adj b c := by
  rcases fin2_sub j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩
  · rw [hj] at hb; rw [hj'] at hc
    exact clean_rect G C hAO2 t ht i u hu k hk hor b c hb hc hub huc
  · rw [hj] at hb; rw [hj'] at hc
    exact (clean_rect G C hAO2 t ht i u hu k hk hor c b hc hb huc hub).symm

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

open PEqualNP.TopForm in
lemma cl_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (g : ℕ) (hlen : g < C.gates.length)
    (hand : (gateAt C g).op = GateOp.and) (j : Fin 2) (w : Fin n)
    (hcl : Cl G C w (n + g)) (hf : Fires n C (opnd C g j) w) :
    Cl G C w (opnd C g ((1 : Fin 2) - j)) := by
  intro X hw hv
  apply hcl X hw
  have h1 := hf X hw
  show gateVal n C g X = true
  apply (and_val2 C hAO2 g hlen hand X).mpr
  rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
  · rw [e] at h1; rw [e'] at hv; exact ⟨h1, hv⟩
  · rw [e] at h1; rw [e'] at hv; exact ⟨hv, h1⟩

open PEqualNP.TopForm in
lemma cl_rect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C)
    (w : Fin n) (r : ℕ) (hcl : Cl G C w r) (k : ℕ) (hk : k ∈ junk G C)
    (hr : Relation.ReflTransGen (OrStep n C) r (n + k))
    (j : Fin 2) (b c : Fin n) (hb : b ∈ side (n := n) C k j)
    (hc : c ∈ side (n := n) C k ((1 : Fin 2) - j))
    (hwb : ¬ G.Adj w b) (hwc : ¬ G.Adj w c) : G.Adj b c := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ z : Fin n, X z = true ↔ (z = w ∨ z = b ∨ z = c) :=
    ⟨fun z => decide (z = w ∨ z = b ∨ z = c), fun z => by simp⟩
  have hkv : gateVal n C k X = true := by
    apply junk_rect G C hAO2 k hk X
    rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at hb; rw [e'] at hc
      exact ⟨⟨b, hb, (hx b).mpr (Or.inr (Or.inl rfl))⟩,
        ⟨c, hc, (hx c).mpr (Or.inr (Or.inr rfl))⟩⟩
    · rw [e] at hb; rw [e'] at hc
      exact ⟨⟨c, hc, (hx c).mpr (Or.inr (Or.inr rfl))⟩,
        ⟨b, hb, (hx b).mpr (Or.inr (Or.inl rfl))⟩⟩
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
lemma heavy_junk_leaf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C)
    (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (h : ℕ) (hh : h ∈ junk G C)
    (horh : OrReaches n C (opnd C t i) h) (k : ℕ) (hk : k ∈ junk G C)
    (hor : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k) (v : Fin n) (j : Fin 2)
    (hY : side (n := n) C k ((1 : Fin 2) - j) = {v})
    (hD : K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card)
    (u y : Fin n) (hu0 : u ∈ side (n := n) C h 0) (hu1 : u ∈ side (n := n) C h 1)
    (hy0 : y ∈ side (n := n) C h 0) (hy1 : y ∈ side (n := n) C h 1) (hyu : y ≠ u)
    (hvu : G.Adj v u) (hvy : G.Adj v y) : CD G C 3 v u := by
  classical
  have hv1 : v ∈ side (n := n) C k ((1 : Fin 2) - j) := by
    rw [hY]; exact Finset.mem_singleton_self v
  have htri : ∀ a ∈ (side (n := n) C h 0).filter (fun x => ¬ G.Adj v x),
      ∀ x ∈ (side (n := n) C h 1).filter (fun x => ¬ G.Adj v x),
      ∀ d ∈ (side (n := n) C k j).filter (fun x => ¬ G.Adj v x),
      G.Adj a x ∨ G.Adj a d ∨ G.Adj x d := by
    intro a ha x hx d hd
    rw [Finset.mem_filter] at ha hx hd
    obtain ⟨y', z', hyz, hy', hz'⟩ := valid4i G C hAO2 t ht i h hh k hk horh hor 0 j
      a x d v ha.1 (by rw [show ((1 : Fin 2) - 0) = 1 from by decide]; exact hx.1) hd.1 hv1
    exact tri_of_four G a x d v y' z' hyz hy' hz' ha.2 hx.2 hd.2
  have hD4 : 4 ≤ ((side (n := n) C k j).filter (fun x => ¬ G.Adj v x)).card := by omega
  by_cases h1 : 4 ≤ ((side (n := n) C h 1).filter (fun x => ¬ G.Adj v x)).card
  · have h0 := g43 G h4 _ _ _ htri h1 hD4
    exact ⟨hvu, opnd C h 0, hu0, ⟨y, hy0, hyu, hvy⟩, le_trans h0 (by norm_num)⟩
  · exact ⟨hvu, opnd C h 1, hu1, ⟨y, hy1, hyu, hvy⟩, Nat.lt_succ_iff.mp (not_le.mp h1)⟩

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
lemma classD_sem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (u v : Fin n) (huv : G.Adj u v) (q : ℕ) (hcl : Cl G C u q)
    (k : ℕ) (hk : k ∈ junk G C) (hrk : Relation.ReflTransGen (OrStep n C) q (n + k))
    (hr0 : u ∈ side (n := n) C k 0 ∨ v ∈ side (n := n) C k 0)
    (hr1 : u ∈ side (n := n) C k 1 ∨ v ∈ side (n := n) C k 1) :
    CD G C K u v ∨ CD G C K v u ∨ LineDet G C u v ∨ HcSlot G C K u v ∨
      (HcP G C K q v ∧ ∀ y, HcP G C K q y → y = v) ∨
      (v ∈ side (n := n) C k 0 ∧ v ∈ side (n := n) C k 1) := by
  classical
  have e10 : ((1 : Fin 2) - 0) = 1 := by decide
  have e11 : ((1 : Fin 2) - 1) = 0 := by decide
  have hklen := (junk_lt G C k hk).1
  have hclean : ∀ b ∈ side (n := n) C k 0, ∀ c ∈ side (n := n) C k 1,
      ¬ G.Adj u b → ¬ G.Adj u c → G.Adj b c :=
    fun b hb c hc => cl_rect G C hAO2 u q hcl k hk hrk 0 b c hb (by rw [e10]; exact hc)
  have hheavy : ∀ j : Fin 2, side (n := n) C k ((1 : Fin 2) - j) = {v} →
      K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card →
      (HcSlot G C K u v ∨ (HcP G C K q v ∧ ∀ y, HcP G C K q y → y = v)) := by
    intro j hY hD
    have hHLk : HL G C K k v := ⟨hk, j, Or.inl hY, hD⟩
    have hvq : HcP G C K q v := ⟨k, hrk, hHLk⟩
    by_cases hbig : ∃ v', HcP G C K q v' ∧ v' ≠ v
    · left
      have hterm : ¬ ∃ v', HcP G C K (n + k) v' ∧ v' ≠ v := by
        rintro ⟨v', ⟨k', hr', hhl'⟩, hne⟩
        have hkk : k' = k := by
          have := junk_reach_self G C k hk _ hr'
          omega
        rw [hkk] at hhl'
        obtain ⟨_, j', hY', _⟩ := hhl'
        exact hne (hl_unique G C K hK k j j' v v' (Or.inl hY) hD hY')
      obtain ⟨g, c, hg, hin, hr1', _, hr3, hb1, hb2⟩ :=
        path_split C (fun r => ∃ v', HcP G C K r v' ∧ v' ≠ v) (n + k) hterm _ hrk hbig
      refine ⟨(g, c), slot_mem C hg hin, huv, ⟨k, hr3, hHLk⟩, ?_, hb1, cl_mono G C hcl hr1'⟩
      intro y hy
      by_contra hne
      exact hb2 ⟨y, hy, hne⟩
    · right
      refine ⟨hvq, ?_⟩
      intro y hy
      by_contra hne
      exact hbig ⟨y, hy, hne⟩
  rcases classD_abs G h4 K u v _ _ hclean hr0 hr1 with
    (h | h) | (h | h) | (h | h) | (h | h) | h
  · exact Or.inl (cd_mono G C hK (cd_of_O1 G C k 0 u v huv h))
  · exact Or.inl (cd_mono G C hK (cd_of_O1 G C k 1 u v huv h))
  · exact Or.inr (Or.inl (cd_of_O2 G C K k 0 _ u v huv h))
  · exact Or.inr (Or.inl (cd_of_O2 G C K k 1 _ u v huv h))
  · refine Or.inr (Or.inr (Or.inl ⟨(k, 0),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hklen, Finset.mem_univ _⟩, huv, ?_⟩))
    rw [e10]; exact h
  · refine Or.inr (Or.inr (Or.inl ⟨(k, 1),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hklen, Finset.mem_univ _⟩, huv, ?_⟩))
    rw [e11]; exact h
  · rcases hheavy 0 (by rw [e10]; exact h.1) h.2.2.2.2 with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  · rcases hheavy 1 (by rw [e11]; exact h.1) h.2.2.2.2 with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1⟩))))

open PEqualNP.TopForm in
lemma classD_nest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hfu : Fires n C (opnd C t i) u)
    (k1 : ℕ) (hk1 : k1 ∈ junk G C) (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k1)
    (j1 : Fin 2) (hfu1 : Fires n C (opnd C k1 j1) u)
    (k : ℕ) (hk : k ∈ junk G C) (hor : OrReaches n C (opnd C k1 ((1 : Fin 2) - j1)) k)
    (hr0 : u ∈ side (n := n) C k 0 ∨ v ∈ side (n := n) C k 0)
    (hr1 : u ∈ side (n := n) C k 1 ∨ v ∈ side (n := n) C k 1) :
    CD G C K u v ∨ CD G C K v u ∨ LineDet G C u v ∨ HcSlot G C K u v ∨
      (HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) v ∧
        ∀ y, HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) y → y = v) ∨
      (v ∈ side (n := n) C k 0 ∧ v ∈ side (n := n) C k 1) := by
  have hc0 : Cl G C u (opnd C t ((1 : Fin 2) - i)) := cl_top G C hAO2 t ht i u hfu
  have hc1 : Cl G C u (n + k1) := cl_mono G C hc0 (orReaches_reach k1 _ hor1).1
  have hc2 : Cl G C u (opnd C k1 ((1 : Fin 2) - j1)) :=
    cl_and G C hAO2 k1 (junk_lt G C k1 hk1).1 (junk_lt G C k1 hk1).2 j1 u hc1 hfu1
  exact classD_sem G C h4 hAO2 K hK u v huv _ hc2 k hk (orReaches_reach k _ hor).1 hr0 hr1

lemma cl_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (z x : Fin n) (r : ℕ) (hcl : Cl G C z r) (hx : Fires n C r x) : G.Adj z x :=
  (graphFun_pair G z x).mp (hcl (pairInput z x) (pairInput_left z x)
    (hx (pairInput z x) (pairInput_right z x)))

open PEqualNP.TopForm in
lemma clean_rectL_sem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (u : Fin n) (k : ℕ) (hk : k ∈ junk G C) (hcl : Cl G C u (n + k))
    (b c : Fin n) (hb : b ∈ Lw n C (opnd C k 0)) (hc : c ∈ Lw n C (opnd C k 1))
    (hub : ¬ G.Adj u b) (huc : ¬ G.Adj u c) : G.Adj b c := by
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ w : Fin n, X w = true ↔ (w = u ∨ w = b ∨ w = c) :=
    ⟨fun w => decide (w = u ∨ w = b ∨ w = c), fun w => by simp⟩
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  have hkv : gateVal n C k X = true :=
    (and_val2 C hAO2 k hlen hand X).mpr
      ⟨mem_Lw.mp hb X ((hx b).mpr (Or.inr (Or.inl rfl))),
        mem_Lw.mp hc X ((hx c).mpr (Or.inr (Or.inr rfl)))⟩
  have hF : graphFun G ∅ X = true := hcl X ((hx u).mpr (Or.inl rfl)) hkv
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
lemma lleaf_cdl_sem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (z : Fin n) (h : ℕ) (hh : h ∈ junk G C) (hcl : Cl G C z (n + h))
    (x y : Fin n) (hx0 : x ∈ side (n := n) C h 0) (hx1 : x ∈ side (n := n) C h 1)
    (hy : y ∈ Lw n C (n + h)) (hxy : y ≠ x) : CDL G C 1 z x := by
  classical
  have hxf : Fires n C (n + h) x := fires_both G C hAO2 h hh x hx0 hx1
  have hzx : G.Adj z x := cl_adj G C z x _ hcl hxf
  have hzy : G.Adj z y := cl_adj G C z y _ hcl (mem_Lw.mp hy)
  have hclean := fun b hb c hc => clean_rectL_sem G C hAO2 z h hh hcl b c hb hc
  have hxx : x ∈ Lw n C x.val := mem_Lw.mpr ((fires_input C x x).mpr rfl)
  have hux : ∀ y' ∈ Lw n C x.val, G.Adj z y' → y' = x :=
    fun y' hy' _ => (fires_input C x y').mp (mem_Lw.mp hy')
  rcases dirt_star G h4 z _ _ hclean with hd | hd
  · exact cdl_of_path G C 1 z x hzx (opnd C h 0) x.val (mem_orIn_reach x hx0) hxx hux
      ⟨y, mem_Lw.mpr (fires_opnd G C hAO2 h hh 0 y (mem_Lw.mp hy)), hxy, hzy⟩ hd
  · exact cdl_of_path G C 1 z x hzx (opnd C h 1) x.val (mem_orIn_reach x hx1) hxx hux
      ⟨y, mem_Lw.mpr (fires_opnd G C hAO2 h hh 1 y (mem_Lw.mp hy)), hxy, hzy⟩ hd

open PEqualNP.TopForm in
lemma shape31_R2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k1 : ℕ) (hk1 : k1 ∈ junk G C) (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k1)
    (j1 : Fin 2) (hu3 : u ∈ side (n := n) C k1 j1)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k1 ((1 : Fin 2) - j1)) h)
    (hv0 : v ∈ side (n := n) C h 0) (hv1 : v ∈ side (n := n) C h 1) :
    PayD G C K u v ∨
      ((∀ y ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)), y = v) ∧
        v ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)) ∧ v ∉ side (n := n) C k1 j1) := by
  classical
  obtain ⟨hlen1, hand1⟩ := junk_lt G C k1 hk1
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hrk1 := (orReaches_reach k1 _ hor1).1
  have hrh := (orReaches_reach h _ horh).1
  have hc0 : Cl G C u (opnd C t ((1 : Fin 2) - i)) := cl_top G C hAO2 t ht i u hfu
  have hc1 : Cl G C u (n + k1) := cl_mono G C hc0 hrk1
  have hcQ : Cl G C u (opnd C k1 ((1 : Fin 2) - j1)) :=
    cl_and G C hAO2 k1 hlen1 hand1 j1 u hc1 (fires_side C k1 j1 u hu3)
  have hch : Cl G C u (n + h) := cl_mono G C hcQ hrh
  have hvh : v ∈ Lw n C (n + h) := mem_Lw.mpr (fires_both G C hAO2 h hh v hv0 hv1)
  have hvQ : v ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)) := Lw_mono hrh hvh
  by_cases hQ1 : ∀ y ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)), y = v
  · by_cases hv3 : v ∈ side (n := n) C k1 j1
    · left
      have hvk1 : v ∈ Lw n C (n + k1) := by
        refine mem_Lw.mpr (fun X hX => ?_)
        apply (and_val2 C hAO2 k1 hlen1 hand1 X).mpr
        have a1 := side_leaf C k1 j1 v hv3 X hX
        have a2 := mem_Lw.mp hvQ X hX
        rcases fin2_sub j1 with ⟨e, e'⟩ | ⟨e, e'⟩
        · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
        · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
      have hτv : ∀ y ∈ Lw n C (n + k1), y = v := fun y hy =>
        hQ1 y (mem_Lw.mpr (fires_opnd G C hAO2 k1 hk1 _ y (mem_Lw.mp hy)))
      have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
      have hτu : (∀ y ∈ Lw n C u.val, y = u) ∨ False :=
        Or.inl (fun y hy => (fires_input C u y).mp (mem_Lw.mp hy))
      rcases lstar_pay G C hAO2 t ht i u v u.val (n + k1) (mem_orIn_reach u hside) huu hτu
        hrk1 hvk1 hτv with h' | h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
      · exact h'.elim
    · exact Or.inr ⟨hQ1, hvQ, hv3⟩
  · left
    obtain ⟨y, hy1⟩ := not_forall.mp hQ1
    obtain ⟨hy, hyv⟩ := Classical.not_imp.mp hy1
    have huy : G.Adj u y := cl_adj G C u y _ hcQ (mem_Lw.mp hy)
    by_cases hh1 : ∀ y' ∈ Lw n C (n + h), y' = v
    · have hdirt : ((Lw n C (opnd C k1 ((1 : Fin 2) - j1))).filter
          (fun y' => ¬ G.Adj u y')).card ≤ 0 := by
        have he : (Lw n C (opnd C k1 ((1 : Fin 2) - j1))).filter (fun y' => ¬ G.Adj u y') = ∅ :=
          Finset.filter_eq_empty_iff.mpr
            (fun y' hy' => not_not.mpr (cl_adj G C u y' _ hcQ (mem_Lw.mp hy')))
        rw [he]; simp
      exact Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega)
        (cdl_of_path G C 0 u v huv _ (n + h) hrh hvh (fun y' hy' _ => hh1 y' hy')
          ⟨y, hy, hyv, huy⟩ hdirt)))))
    · obtain ⟨y2, hy3⟩ := not_forall.mp hh1
      obtain ⟨hy2, hy2v⟩ := Classical.not_imp.mp hy3
      exact Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK
        (lleaf_cdl_sem G C h4 hAO2 u h hh hch v y2 hv0 hv1 hy2 hy2v)))))

open PEqualNP.TopForm in
lemma shape31_I {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k1 : ℕ) (hk1 : k1 ∈ junk G C) (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k1)
    (j1 : Fin 2) (hu3 : u ∈ side (n := n) C k1 j1)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k1 ((1 : Fin 2) - j1)) h)
    (hr0 : u ∈ side (n := n) C h 0 ∨ v ∈ side (n := n) C h 0)
    (hr1 : u ∈ side (n := n) C h 1 ∨ v ∈ side (n := n) C h 1) :
    PayD G C K u v ∨
      (HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) v ∧
        ∀ y, HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) y → y = v) ∨
      ((∀ y ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)), y = v) ∧
        v ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)) ∧ v ∉ side (n := n) C k1 j1) := by
  rcases classD_nest G C h4 hAO2 K hK t ht i u v huv (fires_side C t i u hside) k1 hk1 hor1
    j1 (fires_side C k1 j1 u hu3) h hh horh hr0 hr1 with h' | h' | h' | h' | h' | h'
  · exact Or.inl (Or.inl h')
  · exact Or.inl (Or.inr (Or.inl h'))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h')))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))))
  · exact Or.inr (Or.inl h')
  · rcases shape31_R2 G C h4 hAO2 K hK t ht i u v huv hside k1 hk1 hor1 j1 hu3 h hh horh
      h'.1 h'.2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inr h2)

open PEqualNP.TopForm in
lemma shape31_Ib {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k1 : ℕ) (hk1 : k1 ∈ junk G C) (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k1)
    (j1 : Fin 2) (hu3 : u ∈ side (n := n) C k1 j1)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k1 ((1 : Fin 2) - j1)) h)
    (hr0 : u ∈ side (n := n) C h 0 ∨ v ∈ side (n := n) C h 0)
    (hr1 : u ∈ side (n := n) C h 1 ∨ v ∈ side (n := n) C h 1) :
    PayD G C K u v ∨
      (((HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) v ∧
          ∀ y, HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) y → y = v) ∨
        ((∀ y ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)), y = v) ∧
          v ∈ Lw n C (opnd C k1 ((1 : Fin 2) - j1)) ∧ v ∉ side (n := n) C k1 j1)) ∧
        ((∀ y ∈ side (n := n) C k1 j1, G.Adj v y → y = u) ∨
          K < ((side (n := n) C k1 j1).filter (fun y => ¬ G.Adj v y)).card)) := by
  classical
  rcases shape31_I G C h4 hAO2 K hK t ht i u v huv hside k1 hk1 hor1 j1 hu3 h hh horh
    hr0 hr1 with h' | h'
  · exact Or.inl h'
  · by_cases hthin : ∀ y ∈ side (n := n) C k1 j1, G.Adj v y → y = u
    · exact Or.inr ⟨h', Or.inl hthin⟩
    · by_cases hd : K < ((side (n := n) C k1 j1).filter (fun y => ¬ G.Adj v y)).card
      · exact Or.inr ⟨h', Or.inr hd⟩
      · left
        obtain ⟨b, hb1⟩ := not_forall.mp hthin
        obtain ⟨hb, hb2⟩ := Classical.not_imp.mp hb1
        obtain ⟨hvb, hbu⟩ := Classical.not_imp.mp hb2
        exact Or.inr (Or.inl ⟨huv.symm, opnd C k1 j1, hu3, ⟨b, hb, hbu, hvb⟩, not_lt.mp hd⟩)

def LineDetL {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ O3 G u v (PEqualNP.TopForm.side (n := n) C kj.1 kj.2)
      (Lw n C (PEqualNP.TopForm.opnd C kj.1 ((1 : Fin 2) - kj.2)))

lemma linedetl_bnd {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    Bnd (LineDetL G C) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold LineDetL
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

def GateHL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ ti ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ u ∈ PEqualNP.TopForm.side (n := n) C ti.1 ti.2 ∧
    (∀ y ∈ PEqualNP.TopForm.side (n := n) C ti.1 ti.2, G.Adj v y → y = u) ∧
    HcP G C K (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) v ∧
    ∀ y, HcP G C K (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) y → y = v

lemma gatehl_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) :
    Bnd (GateHL G C K) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold GateHL
  refine bnd_le (by rw [hc]; omega) (obj_count _ 1 _ ?_)
  intro ti _ P hP
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  obtain ⟨_, _, a3, _, a5⟩ := hP zv hzv
  obtain ⟨badj, b2, _, b4, _⟩ := hP zv' hzv'
  have e2 : zv'.2 = zv.2 := a5 zv'.2 b4
  have e1 : zv'.1 = zv.1 := a3 zv'.1 b2 (by rw [← e2]; exact badj.symm)
  exact Prod.ext e1.symm e2.symm

def Pay2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay G C K a b ∨ LineDetL G C a b ∨ LineDetL G C b a ∨ GateHL G C K a b ∨ GateHL G C K b a

open PEqualNP.TopForm in
lemma pay2_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay2 G C 5) (2220 * C.gates.length) := by
  have hb := bnd_or (pay_bnd G C h4 hAO2 h2) (bnd_or (linedetl_bnd G C)
    (bnd_or (bnd_swap (linedetl_bnd G C)) (bnd_or (gatehl_bnd G C 5)
      (bnd_swap (gatehl_bnd G C 5)))))
  unfold Pay2
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma shape31_Ic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k1 : ℕ) (hk1 : k1 ∈ junk G C) (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k1)
    (j1 : Fin 2) (hu3 : u ∈ side (n := n) C k1 j1)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k1 ((1 : Fin 2) - j1)) h)
    (hr0 : u ∈ side (n := n) C h 0 ∨ v ∈ side (n := n) C h 0)
    (hr1 : u ∈ side (n := n) C h 1 ∨ v ∈ side (n := n) C h 1) :
    Pay2 G C K u v ∨
      ((HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) v ∧
          ∀ y, HcP G C K (opnd C k1 ((1 : Fin 2) - j1)) y → y = v) ∧
        K < ((side (n := n) C k1 j1).filter (fun y => ¬ G.Adj v y)).card) := by
  classical
  have hmem : (k1, j1) ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (junk_lt G C k1 hk1).1, Finset.mem_univ _⟩
  rcases shape31_Ib G C h4 hAO2 K (by omega) t ht i u v huv hside k1 hk1 hor1 j1 hu3 h hh
    horh hr0 hr1 with h' | ⟨hres, hsplit⟩
  · exact Or.inl (Or.inl (Or.inl h'))
  · rcases hres with hR1 | hR2
    · rcases hsplit with hthin | hdirty
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨(k1, j1), hmem, huv, hu3, hthin, hR1.1, hR1.2⟩))))
      · exact Or.inr ⟨hR1, hdirty⟩
    · have hLw : Lw n C (opnd C k1 ((1 : Fin 2) - j1)) = {v} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hR2.2.1, hR2.1⟩
      rcases hsplit with hthin | hdirty
      · exact Or.inl (Or.inr (Or.inl ⟨(k1, j1), hmem, huv, hLw, hu3, hthin⟩))
      · have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
        have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False :=
          Or.inl (fun y hy _ => (fires_input C u y).mp (mem_Lw.mp hy))
        rcases heavy_pay G C h4 hAO2 K hK t ht i u v huv u.val (mem_orIn_reach u hside) huu
          hτu k1 hk1 hor1 j1 (Or.inr hLw) hdirty with h2 | h2 | h2 | h2
        · exact Or.inl (Or.inl (Or.inl
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2)))))))))
        · exact h2.elim
        · exact Or.inl (Or.inl (Or.inl
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h2))))))))
        · exact Or.inl (Or.inl (Or.inl
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2)))))))))

lemma and_reach_self {n : ℕ} (C : Circuit) (k : ℕ)
    (hand : (gateAt C k).op = GateOp.and) (w : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) (n + k) w) : w = n + k := by
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hstep, _⟩
  · exact h.symm
  · obtain ⟨g, _, hkg, hop, _, _⟩ := hstep
    have e : g = k := by omega
    rw [e, hand] at hop
    exact GateOp.noConfusion hop

def CcP {n : ℕ} (C : Circuit) (Ct : ℕ → Fin n → Prop) (r : ℕ) (v : Fin n) : Prop :=
  ∃ k : ℕ, Relation.ReflTransGen (OrStep n C) r (n + k) ∧ Ct k v

def CtOK {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ)
    (Ct : ℕ → Fin n → Prop) : Prop :=
  (∀ k v v', Ct k v → Ct k v' → v' = v) ∧
    ∀ k v, Ct k v → (gateAt C k).op = GateOp.and ∧
      ∃ M : Finset (Fin n), M.card ≤ m ∧ ∀ w : Fin n, Cl G C w (n + k) → G.Adj w v ∨ w ∈ M

def CSlot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (Ct : ℕ → Fin n → Prop) (u v : Fin n) : Prop :=
  ∃ gc ∈ slots C, G.Adj u v ∧ CcP C Ct gc.2 v ∧ (∀ y, CcP C Ct gc.2 y → y = v) ∧
    (∃ v', CcP C Ct (n + gc.1) v' ∧ v' ≠ v) ∧ Cl G C u (n + gc.1)

lemma cslot_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (m : ℕ) (Ct : ℕ → Fin n → Prop)
    (hok : CtOK G C m Ct) :
    Bnd (CSlot G C Ct) ((1 + m) * (2 * C.gates.length)) := by
  classical
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  unfold CSlot
  apply obj_count (slots C) (1 + m)
  intro gc _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, _, huniq, ⟨v', ⟨k', hr', hct'⟩, hne⟩, _⟩ := hP zv0 hzv0
    obtain ⟨_, M, hM, hclM⟩ := hok.2 k' v' hct'
    have hsub : P ⊆ ((Finset.univ.filter (fun x => G.Adj x zv0.2 ∧ G.Adj x v')) ∪ M) ×ˢ
        {zv0.2} := by
      intro zv hzv
      obtain ⟨hadj, hv, _, _, hcl⟩ := hP zv hzv
      have e2 : zv.2 = zv0.2 := huniq zv.2 hv
      rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_union]
      refine ⟨?_, e2⟩
      rcases hclM zv.1 (cl_mono G C hcl hr') with h | h
      · left
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by rw [← e2]; exact hadj, h⟩
      · exact Or.inr h
    have hA := cn_pair_card G h4 zv0.2 v' (Ne.symm hne)
    have hU := Finset.card_union_le
      (Finset.univ.filter (fun x => G.Adj x zv0.2 ∧ G.Adj x v')) M
    have hc := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_singleton] at hc
    omega

def TopC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (Ct : ℕ → Fin n → Prop) (u v : Fin n) : Prop :=
  ∃ ti ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ u ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ti.2) ∧
    (∀ y ∈ Lw n C (PEqualNP.TopForm.opnd C ti.1 ti.2), G.Adj v y → y = u) ∧
    CcP C Ct (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) v ∧
    ∀ y, CcP C Ct (PEqualNP.TopForm.opnd C ti.1 ((1 : Fin 2) - ti.2)) y → y = v

lemma topc_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (Ct : ℕ → Fin n → Prop) : Bnd (TopC G C Ct) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold TopC
  refine bnd_le (by rw [hc]; omega) (obj_count _ 1 _ ?_)
  intro ti _ P hP
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  obtain ⟨_, _, a3, _, a5⟩ := hP zv hzv
  obtain ⟨badj, b2, _, b4, _⟩ := hP zv' hzv'
  have e2 : zv'.2 = zv.2 := a5 zv'.2 b4
  have e1 : zv'.1 = zv.1 := a3 zv'.1 b2 (by rw [← e2]; exact badj.symm)
  exact Prod.ext e1.symm e2.symm

def PayC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (Ct : ℕ → Fin n → Prop) (u v : Fin n) : Prop :=
  CSlot G C Ct u v ∨ TopC G C Ct u v

lemma payc_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (m : ℕ) (Ct : ℕ → Fin n → Prop)
    (hok : CtOK G C m Ct) :
    Bnd (PayC G C Ct) ((1 + m) * (2 * C.gates.length) + 2 * C.gates.length) :=
  bnd_or (cslot_bnd G C h4 h2 m Ct hok) (topc_bnd G C Ct)

open PEqualNP.TopForm in
lemma centred_pay {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (m : ℕ) (Ct : ℕ → Fin n → Prop) (hok : CtOK G C m Ct)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v) (τu : ℕ)
    (hru : Relation.ReflTransGen (OrStep n C) (opnd C t i) τu) (huτ : u ∈ Lw n C τu)
    {Q : Prop} (hτu : (∀ y ∈ Lw n C τu, G.Adj v y → y = u) ∨ Q)
    (k : ℕ) (hrk : Relation.ReflTransGen (OrStep n C) (opnd C t ((1 : Fin 2) - i)) (n + k))
    (hct : Ct k v) :
    PayC G C Ct u v ∨ Q ∨ CDL G C m v u := by
  classical
  have hup : u ∈ Lw n C (opnd C t i) := Lw_mono hru huτ
  have hfu : Fires n C (opnd C t i) u := mem_Lw.mp hup
  have hvq : CcP C Ct (opnd C t ((1 : Fin 2) - i)) v := ⟨k, hrk, hct⟩
  have htm := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htm
  by_cases hbig : ∃ v', CcP C Ct (opnd C t ((1 : Fin 2) - i)) v' ∧ v' ≠ v
  · left; left
    have hterm : ¬ ∃ v', CcP C Ct (n + k) v' ∧ v' ≠ v := by
      rintro ⟨v', ⟨k', hr', hct'⟩, hne⟩
      have hkk : k' = k := by
        have := and_reach_self C k (hok.2 k v hct).1 _ hr'
        omega
      rw [hkk] at hct'
      exact hne (hok.1 k v v' hct hct')
    obtain ⟨g, c, hg, hin, hr1, _, hr3, hb1, hb2⟩ :=
      path_split C (fun r => ∃ v', CcP C Ct r v' ∧ v' ≠ v) (n + k) hterm _ hrk hbig
    refine ⟨(g, c), slot_mem C hg hin, huv, ⟨k, hr3, hct⟩, ?_, hb1,
      cl_mono G C (cl_top G C hAO2 t ht i u hfu) hr1⟩
    intro y hy
    by_contra hne
    exact hb2 ⟨y, hy, hne⟩
  · have huniq : ∀ y, CcP C Ct (opnd C t ((1 : Fin 2) - i)) y → y = v := by
      intro y hy
      by_contra hne
      exact hbig ⟨y, hy, hne⟩
    rcases hτu with hτu | hq
    · by_cases hsec : ∃ b ∈ Lw n C (opnd C t i), b ≠ u ∧ G.Adj v b
      · right; right
        refine cdl_of_path G C m v u huv.symm _ τu hru huτ hτu hsec ?_
        obtain ⟨_, M, hM, hclM⟩ := hok.2 k v hct
        have hsubB : (Lw n C (opnd C t i)).filter (fun y => ¬ G.Adj v y) ⊆ M := by
          intro x hx
          rw [Finset.mem_filter] at hx
          have hclx : Cl G C x (n + k) :=
            cl_mono G C (cl_top G C hAO2 t ht i x (mem_Lw.mp hx.1)) hrk
          rcases hclM x hclx with h | h
          · exact absurd h.symm hx.2
          · exact h
        exact (Finset.card_le_card hsubB).trans hM
      · left; right
        refine ⟨(t, i), Finset.mem_product.mpr ⟨Finset.mem_range.mpr htm.1, Finset.mem_univ _⟩,
          huv, hup, ?_, hvq, huniq⟩
        intro y hy hvy
        by_contra hne
        exact hsec ⟨y, hy, hne, hvy⟩
    · exact Or.inr (Or.inl hq)

def HB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  k ∈ PEqualNP.TopForm.junk G C ∧ v ∈ PEqualNP.TopForm.side (n := n) C k j ∧
    HcP G C K (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) v ∧
    ∀ y, HcP G C K (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) y → y = v

open PEqualNP.TopForm in
lemma hb_ok {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K) (j : Fin 2) : CtOK G C 1 (HB G C K j) := by
  classical
  refine ⟨fun k v v' h h' => h.2.2.2 v' h'.2.2.1, ?_⟩
  intro k v hb
  obtain ⟨hk, hvs, ⟨h, hrh, hh, jh, hY, hD⟩, _⟩ := hb
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  refine ⟨hand, Finset.univ.filter (fun x => ∀ d ∈ (side (n := n) C h jh).filter
    (fun y => ¬ G.Adj v y), G.Adj x d), cn_set_card G h4 _ (by omega), ?_⟩
  intro w hcl
  by_cases hwv : G.Adj w v
  · exact Or.inl hwv
  · right
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro d hd
    rw [Finset.mem_filter] at hd
    by_contra hwd
    obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ z : Fin n, X z = true ↔ (z = w ∨ z = v ∨ z = d) :=
      ⟨fun z => decide (z = w ∨ z = v ∨ z = d), fun z => by simp⟩
    have hXv : X v = true := (hx v).mpr (Or.inr (Or.inl rfl))
    have hXd : X d = true := (hx d).mpr (Or.inr (Or.inr rfl))
    have hhv : gateVal n C h X = true := by
      apply (and_val2 C hAO2 h hlenh handh X).mpr
      have a1 := side_leaf C h jh d hd.1 X hXd
      have a2 := thin_fires C h _ v hY X hXv
      rcases fin2_sub jh with ⟨e, e'⟩ | ⟨e, e'⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
    have hkv : gateVal n C k X = true := by
      apply (and_val2 C hAO2 k hlen hand X).mpr
      have a1 := side_leaf C k j v hvs X hXv
      have a2 : val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true :=
        orStep_up (n := n) (by simp) hrh hhv
      rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
    have hF : graphFun G ∅ X = true := hcl X ((hx w).mpr (Or.inl rfl)) hkv
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hF
    obtain ⟨y, z, hyz, hy, hz⟩ := hF
    rcases (hx y).mp hy with e1 | e1 | e1 <;> rcases (hx z).mp hz with e2 | e2 | e2 <;>
      rw [e1, e2] at hyz
    · exact G.irrefl hyz
    · exact hwv hyz
    · exact hwd hyz
    · exact hwv hyz.symm
    · exact G.irrefl hyz
    · exact hd.2 hyz
    · exact hwd hyz.symm
    · exact hd.2 hyz.symm
    · exact G.irrefl hyz

def HB3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  k ∈ PEqualNP.TopForm.junk G C ∧
    3 ≤ ((PEqualNP.TopForm.side (n := n) C k j).filter (fun y => ¬ G.Adj v y)).card ∧
    HcP G C K (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) v ∧
    ∀ y, HcP G C K (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) y → y = v

lemma two_good {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (Y D : Finset (Fin n)) (hY : 3 ≤ Y.card) (hD : 4 ≤ D.card) :
    ∃ y1 ∈ Y, ∃ y2 ∈ Y, y1 ≠ y2 ∧ 2 ≤ (D.filter (fun d => ¬ G.Adj y1 d)).card ∧
      2 ≤ (D.filter (fun d => ¬ G.Adj y2 d)).card := by
  classical
  have hB : (Y.filter (fun y => (D.filter (fun d => ¬ G.Adj y d)).card ≤ 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro y hy y' hy'
    rw [Finset.mem_filter] at hy hy'
    by_contra hne
    have hcn : (D.filter (fun d => G.Adj y d ∧ G.Adj y' d)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      by_contra hab
      exact hne (common_unique G h4 y y' a b ha.2.1 hb.2.1 ha.2.2 hb.2.2 hab)
    have hsub : D ⊆ (D.filter (fun d => ¬ G.Adj y d)) ∪ (D.filter (fun d => ¬ G.Adj y' d)) ∪
        (D.filter (fun d => G.Adj y d ∧ G.Adj y' d)) := by
      intro d hd
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases a1 : G.Adj y d
      · by_cases a2 : G.Adj y' d
        · exact Or.inr ⟨hd, a1, a2⟩
        · exact Or.inl (Or.inr ⟨hd, a2⟩)
      · exact Or.inl (Or.inl ⟨hd, a1⟩)
    have u0 := Finset.card_le_card hsub
    have u1 := Finset.card_union_le
      ((D.filter (fun d => ¬ G.Adj y d)) ∪ (D.filter (fun d => ¬ G.Adj y' d)))
      (D.filter (fun d => G.Adj y d ∧ G.Adj y' d))
    have u2 := Finset.card_union_le (D.filter (fun d => ¬ G.Adj y d))
      (D.filter (fun d => ¬ G.Adj y' d))
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := Y)
    (fun y => (D.filter (fun d => ¬ G.Adj y d)).card ≤ 1)
  have hgood : 1 < (Y.filter (fun y => ¬ (D.filter (fun d => ¬ G.Adj y d)).card ≤ 1)).card := by
    omega
  obtain ⟨y1, hy1, y2, hy2, hne⟩ := Finset.one_lt_card.mp hgood
  rw [Finset.mem_filter] at hy1 hy2
  exact ⟨y1, hy1.1, y2, hy2.1, hne, by omega, by omega⟩

open PEqualNP.TopForm in
lemma hb3_ok {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 3 ≤ K) (j : Fin 2) : CtOK G C 3 (HB3 G C K j) := by
  classical
  refine ⟨fun k v v' h h' => h.2.2.2 v' h'.2.2.1, ?_⟩
  intro k v hb
  obtain ⟨hk, hY3, ⟨h, hrh, hh, jh, hY, hD⟩, _⟩ := hb
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  obtain ⟨y1, hy1, y2, hy2, hne, hg1, hg2⟩ := two_good G h4
    ((side (n := n) C k j).filter (fun y => ¬ G.Adj v y))
    ((side (n := n) C h jh).filter (fun y => ¬ G.Adj v y)) hY3 (by omega)
  rw [Finset.mem_filter] at hy1 hy2
  have htest : ∀ w : Fin n, Cl G C w (n + k) → ¬ G.Adj w v →
      ∀ y ∈ side (n := n) C k j, ¬ G.Adj v y →
      ∀ d ∈ ((side (n := n) C h jh).filter (fun y => ¬ G.Adj v y)).filter
        (fun d => ¬ G.Adj y d), G.Adj w y ∨ G.Adj w d := by
    intro w hcl hwv y hy hvy d hd
    rw [Finset.mem_filter, Finset.mem_filter] at hd
    obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
        ∀ z : Fin n, X z = true ↔ (z = w ∨ z = y ∨ z = v ∨ z = d) :=
      ⟨fun z => decide (z = w ∨ z = y ∨ z = v ∨ z = d), fun z => by simp⟩
    have hXy : X y = true := (hx y).mpr (Or.inr (Or.inl rfl))
    have hXv : X v = true := (hx v).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hXd : X d = true := (hx d).mpr (Or.inr (Or.inr (Or.inr rfl)))
    have hhv : gateVal n C h X = true := by
      apply (and_val2 C hAO2 h hlenh handh X).mpr
      have a1 := side_leaf C h jh d hd.1.1 X hXd
      have a2 := thin_fires C h _ v hY X hXv
      rcases fin2_sub jh with ⟨e, e'⟩ | ⟨e, e'⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
    have hkv : gateVal n C k X = true := by
      apply (and_val2 C hAO2 k hlen hand X).mpr
      have a1 := side_leaf C k j y hy X hXy
      have a2 : val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true :=
        orStep_up (n := n) (by simp) hrh hhv
      rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
    have hF : graphFun G ∅ X = true := hcl X ((hx w).mpr (Or.inl rfl)) hkv
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hF
    obtain ⟨a, b, hab, ha, hb'⟩ := hF
    have hvd : ¬ G.Adj v d := hd.1.2
    have hyd : ¬ G.Adj y d := hd.2
    rcases (hx a).mp ha with e1 | e1 | e1 | e1 <;>
      rcases (hx b).mp hb' with e2 | e2 | e2 | e2 <;> rw [e1, e2] at hab
    all_goals first
      | exact (G.irrefl hab).elim
      | exact Or.inl hab
      | exact Or.inl hab.symm
      | exact Or.inr hab
      | exact Or.inr hab.symm
      | exact absurd hab hwv
      | exact absurd hab.symm hwv
      | exact absurd hab hvy
      | exact absurd hab.symm hvy
      | exact absurd hab hvd
      | exact absurd hab.symm hvd
      | exact absurd hab hyd
      | exact absurd hab.symm hyd
  refine ⟨hand, (Finset.univ.filter (fun x => G.Adj x y1 ∧ G.Adj x y2)) ∪
    ((Finset.univ.filter (fun x => ∀ d ∈ ((side (n := n) C h jh).filter
      (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y1 d), G.Adj x d)) ∪
    (Finset.univ.filter (fun x => ∀ d ∈ ((side (n := n) C h jh).filter
      (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y2 d), G.Adj x d))), ?_, ?_⟩
  · have c1 := cn_pair_card G h4 y1 y2 hne
    have c2 := cn_set_card G h4 (((side (n := n) C h jh).filter
      (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y1 d)) hg1
    have c3 := cn_set_card G h4 (((side (n := n) C h jh).filter
      (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y2 d)) hg2
    have u1 := Finset.card_union_le (Finset.univ.filter (fun x => G.Adj x y1 ∧ G.Adj x y2))
      ((Finset.univ.filter (fun x => ∀ d ∈ ((side (n := n) C h jh).filter
        (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y1 d), G.Adj x d)) ∪
      (Finset.univ.filter (fun x => ∀ d ∈ ((side (n := n) C h jh).filter
        (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y2 d), G.Adj x d)))
    have u2 := Finset.card_union_le
      (Finset.univ.filter (fun x => ∀ d ∈ ((side (n := n) C h jh).filter
        (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y1 d), G.Adj x d))
      (Finset.univ.filter (fun x => ∀ d ∈ ((side (n := n) C h jh).filter
        (fun y => ¬ G.Adj v y)).filter (fun d => ¬ G.Adj y2 d), G.Adj x d))
    omega
  · intro w hcl
    by_cases hwv : G.Adj w v
    · exact Or.inl hwv
    · right
      have t1 := htest w hcl hwv y1 hy1.1 hy1.2
      have t2 := htest w hcl hwv y2 hy2.1 hy2.2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases a1 : G.Adj w y1
      · by_cases a2 : G.Adj w y2
        · exact Or.inl ⟨a1, a2⟩
        · right; right
          intro d hd
          rcases t2 d (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr hd.1, hd.2⟩) with h' | h'
          · exact absurd h' a2
          · exact h'
      · right; left
        intro d hd
        rcases t1 d (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr hd.1, hd.2⟩) with h' | h'
        · exact absurd h' a1
        · exact h'

def Pay3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay2 G C K a b ∨ PayC G C (HB3 G C K 0) a b ∨ PayC G C (HB3 G C K 0) b a ∨
    PayC G C (HB3 G C K 1) a b ∨ PayC G C (HB3 G C K 1) b a

open PEqualNP.TopForm in
lemma pay3_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay3 G C 5) (2260 * C.gates.length) := by
  have p0 := payc_bnd G C h4 h2 3 (HB3 G C 5 0) (hb3_ok G C h4 hAO2 5 (by norm_num) 0)
  have p1 := payc_bnd G C h4 h2 3 (HB3 G C 5 1) (hb3_ok G C h4 hAO2 5 (by norm_num) 1)
  have hb := bnd_or (pay2_bnd G C h4 hAO2 h2) (bnd_or p0 (bnd_or (bnd_swap p0)
    (bnd_or p1 (bnd_swap p1))))
  unfold Pay3
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma shape31_Id {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k1 : ℕ) (hk1 : k1 ∈ junk G C) (hor1 : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k1)
    (j1 : Fin 2) (hu3 : u ∈ side (n := n) C k1 j1)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k1 ((1 : Fin 2) - j1)) h)
    (hr0 : u ∈ side (n := n) C h 0 ∨ v ∈ side (n := n) C h 0)
    (hr1 : u ∈ side (n := n) C h 1 ∨ v ∈ side (n := n) C h 1) :
    Pay3 G C K u v := by
  classical
  rcases shape31_Ic G C h4 hAO2 K hK t ht i u v huv hside k1 hk1 hor1 j1 hu3 h hh horh
    hr0 hr1 with h' | ⟨hR1, hdirty⟩
  · exact Or.inl h'
  · have hct : HB3 G C K j1 k1 v := ⟨hk1, by omega, hR1.1, hR1.2⟩
    have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
    have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False :=
      Or.inl (fun y hy _ => (fires_input C u y).mp (mem_Lw.mp hy))
    have hpc : PayC G C (HB3 G C K j1) u v ∨ Pay2 G C K u v := by
      rcases centred_pay G C hAO2 3 (HB3 G C K j1) (hb3_ok G C h4 hAO2 K hK j1) t ht i u v huv
        u.val (mem_orIn_reach u hside) huu hτu k1 (orReaches_reach k1 _ hor1).1 hct with
        h2 | h2 | h2
      · exact Or.inl h2
      · exact h2.elim
      · exact Or.inr (Or.inl (Or.inl
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK h2))))))))
    rcases hpc with h2 | h2
    · rcases fin2_sub j1 with ⟨e, _⟩ | ⟨e, _⟩
      · rw [e] at h2; exact Or.inr (Or.inl h2)
      · rw [e] at h2; exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
    · exact Or.inl h2

def MP {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (z x : Fin n) : Prop :=
  G.Adj z x ∧ ∃ w : ℕ, x ∈ PEqualNP.TopForm.orIn n C w ∧
    k + 2 ≤ ((PEqualNP.TopForm.orIn n C w).filter (fun y => G.Adj z y)).card ∧
    ∃ X : Finset (Fin n), X.card ≤ k ∧
      ∀ y ∈ PEqualNP.TopForm.orIn n C w, G.Adj z y ∨ ∃ c ∈ X, G.Adj c y

def MPs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (gc : ℕ × ℕ) (z x : Fin n) : Prop :=
  G.Adj z x ∧ x ∈ PEqualNP.TopForm.orIn n C gc.2 ∧
    ((PEqualNP.TopForm.orIn n C gc.2).filter (fun y => G.Adj z y)).card ≤ k + 1 ∧
    k + 2 ≤ ((PEqualNP.TopForm.orIn n C (n + gc.1)).filter (fun y => G.Adj z y)).card ∧
    ∃ X : Finset (Fin n), X.card ≤ k ∧
      ∀ y ∈ PEqualNP.TopForm.orIn n C (n + gc.1), G.Adj z y ∨ ∃ c ∈ X, G.Adj c y

lemma mp_to_slot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (z x : Fin n) (h : MP G C k z x) : ∃ gc ∈ slots C, MPs G C k gc z x := by
  classical
  obtain ⟨hzx, w, hxw, hbig, X, hX, hcov⟩ := h
  have hτ : ¬ (k + 2 ≤ ((PEqualNP.TopForm.orIn n C x.val).filter (fun y => G.Adj z y)).card) := by
    have hsub : (PEqualNP.TopForm.orIn n C x.val).filter (fun y => G.Adj z y) ⊆ {x} := by
      intro y hy
      exact Finset.mem_singleton.mpr (orIn_input C x y (Finset.mem_filter.mp hy).1)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hc
    omega
  obtain ⟨g, c, hg, hin, hr1, _, hr3, hb1, hb2⟩ :=
    path_split C (fun r => k + 2 ≤ ((PEqualNP.TopForm.orIn n C r).filter
      (fun y => G.Adj z y)).card) x.val hτ w (mem_orIn_reach x hxw) hbig
  refine ⟨(g, c), slot_mem C hg hin, hzx, reach_mem_orIn x hr3,
    Nat.lt_succ_iff.mp (not_le.mp hb2), hb1, X, hX, ?_⟩
  intro y hy
  exact hcov y (orIn_mono hr1 hy)

lemma mps_fibre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (k : ℕ) (gc : ℕ × ℕ) : Bnd (MPs G C k gc) ((k + 1) * (k + 1)) := by
  classical
  intro P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, _, _, _, X0, hX0, hcov0⟩ := hP zv0 hzv0
    have hmaps : ∀ zv ∈ P, zv.1 ∈ insert zv0.1 X0 := by
      intro zv hzv
      by_contra hnot
      obtain ⟨_, _, _, hbig, _⟩ := hP zv hzv
      have hsub : (PEqualNP.TopForm.orIn n C (n + gc.1)).filter (fun y => G.Adj zv.1 y) ⊆
          (insert zv0.1 X0).biUnion
            (fun c => Finset.univ.filter (fun y => G.Adj y zv.1 ∧ G.Adj y c)) := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_biUnion]
        rcases hcov0 y hy.1 with h | ⟨c, hc, h⟩
        · exact ⟨zv0.1, Finset.mem_insert_self _ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2.symm, h.symm⟩⟩
        · exact ⟨c, Finset.mem_insert_of_mem hc,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2.symm, h.symm⟩⟩
      have hone : ∀ c ∈ insert zv0.1 X0,
          (Finset.univ.filter (fun y => G.Adj y zv.1 ∧ G.Adj y c)).card ≤ 1 := by
        intro c hc
        apply cn_pair_card G h4 zv.1 c
        intro e
        exact hnot (by rw [e]; exact hc)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_biUnion_le (s := insert zv0.1 X0)
        (t := fun c => Finset.univ.filter (fun y => G.Adj y zv.1 ∧ G.Adj y c))
      have h3 := Finset.sum_le_card_nsmul (insert zv0.1 X0)
        (fun c => (Finset.univ.filter (fun y => G.Adj y zv.1 ∧ G.Adj y c)).card) 1 hone
      have h5 := Finset.card_insert_le zv0.1 X0
      rw [smul_eq_mul, mul_one] at h3
      omega
    have hfib : ∀ z ∈ insert zv0.1 X0, (P.filter (fun zv => zv.1 = z)).card ≤ k + 1 := by
      intro z _
      rcases (P.filter (fun zv => zv.1 = z)).eq_empty_or_nonempty with he | ⟨zv1, hzv1⟩
      · rw [he]; simp
      · rw [Finset.mem_filter] at hzv1
        obtain ⟨_, _, hsmall, _, _⟩ := hP zv1 hzv1.1
        rw [hzv1.2] at hsmall
        refine le_trans (Finset.card_le_card_of_injOn (f := Prod.snd)
          (t := (PEqualNP.TopForm.orIn n C gc.2).filter (fun y => G.Adj z y)) ?_ ?_) hsmall
        · intro zv hzv
          have hzv' := Finset.mem_filter.mp (Finset.mem_coe.mp hzv)
          obtain ⟨hadj, hmem, _⟩ := hP zv hzv'.1
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hmem, by rw [← hzv'.2]; exact hadj⟩)
        · intro zv hzv zv' hzv' heq
          have a1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hzv)).2
          have a2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hzv')).2
          exact Prod.ext (a1.trans a2.symm) heq
    have hmain := Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst)
      (t := insert zv0.1 X0) hmaps (k + 1) hfib
    have h5 := Finset.card_insert_le zv0.1 X0
    calc P.card ≤ (k + 1) * (insert zv0.1 X0).card := hmain
      _ ≤ (k + 1) * (k + 1) := Nat.mul_le_mul_left _ (by omega)

lemma mp_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (k : ℕ) :
    Bnd (MP G C k) ((k + 1) * (k + 1) * (2 * C.gates.length)) := by
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  exact bnd_imp (fun z x h => mp_to_slot G C k z x h)
    (obj_count (slots C) ((k + 1) * (k + 1)) (MPs G C k) (fun gc _ => mps_fibre G h4 C k gc))

def Pay4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay3 G C K a b ∨ MP G C K a b ∨ MP G C K b a

open PEqualNP.TopForm in
lemma pay4_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay4 G C 5) (2404 * C.gates.length) := by
  have hb := bnd_or (pay3_bnd G C h4 hAO2 h2) (bnd_or (mp_bnd G h4 C h2 5)
    (bnd_swap (mp_bnd G h4 C h2 5)))
  unfold Pay4
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma shape31_IIa {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 3 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (hv0 : v ∈ side (n := n) C h 0) (hv1 : v ∈ side (n := n) C h 1) : PayD G C K u v := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hrk := (orReaches_reach k _ hork).1
  have hrh := (orReaches_reach h _ horh).1
  have hcl : Cl G C u (n + k) := cl_mono G C (cl_top G C hAO2 t ht i u hfu) hrk
  have hvh : v ∈ Lw n C (n + h) := mem_Lw.mpr (fires_both G C hAO2 h hh v hv0 hv1)
  have hvQ : v ∈ Lw n C (opnd C k ((1 : Fin 2) - j)) := Lw_mono hrh hvh
  have hvk : v ∈ Lw n C (n + k) := by
    refine mem_Lw.mpr (fun X hX => ?_)
    apply (and_val2 C hAO2 k hlen hand X).mpr
    have a1 := side_leaf C k j v hv3 X hX
    have a2 := mem_Lw.mp hvQ X hX
    rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
  have hvv : v ∈ Lw n C v.val := mem_Lw.mpr ((fires_input C v v).mpr rfl)
  have hvq : ∀ y' ∈ Lw n C v.val, G.Adj u y' → y' = v :=
    fun y' hy' _ => (fires_input C v y').mp (mem_Lw.mp hy')
  by_cases hk1 : ∀ y ∈ Lw n C (n + k), y = v
  · have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
    have hτu : (∀ y ∈ Lw n C u.val, y = u) ∨ False :=
      Or.inl (fun y hy => (fires_input C u y).mp (mem_Lw.mp hy))
    rcases lstar_pay G C hAO2 t ht i u v u.val (n + k) (mem_orIn_reach u hside) huu hτu
      hrk hvk hk1 with h' | h' | h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    · exact h'.elim
  · obtain ⟨y, hy1⟩ := not_forall.mp hk1
    obtain ⟨hy, hyv⟩ := Classical.not_imp.mp hy1
    have huy : G.Adj u y := cl_adj G C u y _ hcl (mem_Lw.mp hy)
    have hyP : y ∈ Lw n C (opnd C k j) :=
      mem_Lw.mpr (fires_opnd G C hAO2 k hk j y (mem_Lw.mp hy))
    have hyQ : y ∈ Lw n C (opnd C k ((1 : Fin 2) - j)) :=
      mem_Lw.mpr (fires_opnd G C hAO2 k hk _ y (mem_Lw.mp hy))
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    by_cases hh1 : ∀ y' ∈ Lw n C (n + h), G.Adj u y' → y' = v
    · have hclean := fun b hb c hc => clean_rectL_sem G C hAO2 u k hk hcl b c hb hc
      have hd : ((Lw n C (opnd C k j)).filter (fun y' => ¬ G.Adj u y')).card ≤ 1 ∨
          ((Lw n C (opnd C k ((1 : Fin 2) - j))).filter (fun y' => ¬ G.Adj u y')).card ≤ 1 := by
        rcases dirt_star G h4 u _ _ hclean with hd | hd
        · rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
          · left; rw [e]; exact hd
          · right; rw [e']; exact hd
        · rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
          · right; rw [e']; exact hd
          · left; rw [e]; exact hd
      rcases hd with hd | hd
      · exact cdl_mono G C (by omega) (cdl_of_path G C 1 u v huv (opnd C k j) v.val
          (mem_orIn_reach v hv3) hvv hvq ⟨y, hyP, hyv, huy⟩ hd)
      · exact cdl_mono G C (by omega) (cdl_of_path G C 1 u v huv
          (opnd C k ((1 : Fin 2) - j)) (n + h) hrh hvh hh1 ⟨y, hyQ, hyv, huy⟩ hd)
    · obtain ⟨y', hy2⟩ := not_forall.mp hh1
      obtain ⟨hy', hy3⟩ := Classical.not_imp.mp hy2
      obtain ⟨huy', hy'v⟩ := Classical.not_imp.mp hy3
      have htri : ∀ a ∈ (Lw n C (opnd C k j)).filter (fun x => ¬ G.Adj u x),
          ∀ x1 ∈ (Lw n C (opnd C h 0)).filter (fun x => ¬ G.Adj u x),
          ∀ x2 ∈ (Lw n C (opnd C h 1)).filter (fun x => ¬ G.Adj u x),
          G.Adj a x1 ∨ G.Adj a x2 ∨ G.Adj x1 x2 := by
        intro a ha x1 hx1 x2 hx2
        rw [Finset.mem_filter] at ha hx1 hx2
        obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
            ∀ z : Fin n, X z = true ↔ (z = a ∨ z = x1 ∨ z = x2 ∨ z = u) :=
          ⟨fun z => decide (z = a ∨ z = x1 ∨ z = x2 ∨ z = u), fun z => by simp⟩
        have hhv : gateVal n C h X = true :=
          (and_val2 C hAO2 h hlenh handh X).mpr
            ⟨mem_Lw.mp hx1.1 X ((hx x1).mpr (Or.inr (Or.inl rfl))),
              mem_Lw.mp hx2.1 X ((hx x2).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩
        have hkv : gateVal n C k X = true := by
          apply (and_val2 C hAO2 k hlen hand X).mpr
          have a1 := mem_Lw.mp ha.1 X ((hx a).mpr (Or.inl rfl))
          have a2 : val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true :=
            orStep_up (n := n) (by simp) hrh hhv
          rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
          · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
          · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
        have hF : graphFun G ∅ X = true :=
          hcl X ((hx u).mpr (Or.inr (Or.inr (Or.inr rfl)))) hkv
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq] at hF
        obtain ⟨y0, z0, hyz, hy0, hz0⟩ := hF
        exact tri_of_four G a x1 x2 u y0 z0 hyz ((hx y0).mp hy0) ((hx z0).mp hz0)
          ha.2 hx1.2 hx2.2
      have hy'0 : y' ∈ Lw n C (opnd C h 0) :=
        mem_Lw.mpr (fires_opnd G C hAO2 h hh 0 y' (mem_Lw.mp hy'))
      have hy'1 : y' ∈ Lw n C (opnd C h 1) :=
        mem_Lw.mpr (fires_opnd G C hAO2 h hh 1 y' (mem_Lw.mp hy'))
      by_cases c1 : 4 ≤ ((Lw n C (opnd C h 1)).filter (fun x => ¬ G.Adj u x)).card
      · by_cases c0 : 4 ≤ ((Lw n C (opnd C h 0)).filter (fun x => ¬ G.Adj u x)).card
        · have hP := g43 G h4 _ _ _ htri c0 c1
          exact cdl_mono G C hK (cdl_of_path G C 3 u v huv (opnd C k j) v.val
            (mem_orIn_reach v hv3) hvv hvq ⟨y, hyP, hyv, huy⟩ (le_trans hP (by norm_num)))
        · exact cdl_mono G C hK (cdl_of_path G C 3 u v huv (opnd C h 0) v.val
            (mem_orIn_reach v hv0) hvv hvq ⟨y', hy'0, hy'v, huy'⟩
            (Nat.lt_succ_iff.mp (not_le.mp c0)))
      · exact cdl_mono G C hK (cdl_of_path G C 3 u v huv (opnd C h 1) v.val
          (mem_orIn_reach v hv1) hvv hvq ⟨y', hy'1, hy'v, huy'⟩
          (Nat.lt_succ_iff.mp (not_le.mp c1)))

open PEqualNP.TopForm in
lemma shape31_IIb1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (K : ℕ)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (y : Fin n) (hy3 : y ∈ side (n := n) C k j) (hyv : y ≠ v)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (hu0 : u ∈ side (n := n) C h 0) (hu1 : u ∈ side (n := n) C h 1) : CD G C K u v := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hcl : Cl G C u (n + k) :=
    cl_mono G C (cl_top G C hAO2 t ht i u hfu) (orReaches_reach k _ hork).1
  have huQ : Fires n C (opnd C k ((1 : Fin 2) - j)) u :=
    fires_mono (orReaches_reach h _ horh).1 (fires_both G C hAO2 h hh u hu0 hu1)
  have hclP : Cl G C u (opnd C k ((1 : Fin 2) - ((1 : Fin 2) - j))) :=
    cl_and G C hAO2 k hlen hand _ u hcl huQ
  rw [fin2_ss] at hclP
  have hall : ∀ x ∈ side (n := n) C k j, G.Adj u x :=
    fun x hx => cl_adj G C u x _ hclP (fires_side C k j x hx)
  refine ⟨huv, opnd C k j, hv3, ⟨y, hy3, hyv, hall y hy3⟩, ?_⟩
  have he : (PEqualNP.TopForm.orIn n C (opnd C k j)).filter (fun x => ¬ G.Adj u x) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x hx => not_not.mpr (hall x hx))
  rw [he]; simp

def SC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ)
    (An : ℕ → Fin n → Prop) (k : ℕ) (v : Fin n) : Prop :=
  An k v ∧ (gateAt C k).op = GateOp.and ∧
    ∃ M : Finset (Fin n), M.card ≤ m ∧ ∀ w : Fin n, Cl G C w (n + k) → G.Adj w v ∨ w ∈ M

lemma sc_ok {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ)
    (An : ℕ → Fin n → Prop) (hAn : ∀ k v v', An k v → An k v' → v' = v) :
    CtOK G C m (SC G C m An) :=
  ⟨fun k v v' h h' => hAn k v v' h.1 h'.1, fun _ _ h => ⟨h.2.1, h.2.2⟩⟩

def An1 {n : ℕ} (C : Circuit) (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  PEqualNP.TopForm.side (n := n) C k j = {v}

lemma an1_fun {n : ℕ} (C : Circuit) (j : Fin 2) :
    ∀ (k : ℕ) (v v' : Fin n), An1 C j k v → An1 C j k v' → v' = v :=
  fun _ _ _ h h' => (Finset.singleton_injective (h.symm.trans h')).symm

def An2 {n : ℕ} (C : Circuit) (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  Lw n C (PEqualNP.TopForm.opnd C k j) = {v}

lemma an2_fun {n : ℕ} (C : Circuit) (j : Fin 2) :
    ∀ (k : ℕ) (v v' : Fin n), An2 C j k v → An2 C j k v' → v' = v :=
  fun _ _ _ h h' => (Finset.singleton_injective (h.symm.trans h')).symm

def An3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  HcP G C K (PEqualNP.TopForm.opnd C k j) v ∧
    ∀ y, HcP G C K (PEqualNP.TopForm.opnd C k j) y → y = v

lemma an3_fun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (j : Fin 2) : ∀ (k : ℕ) (v v' : Fin n), An3 G C K j k v → An3 G C K j k v' → v' = v :=
  fun _ _ _ h h' => h.2 _ h'.1

def LineDetQ {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ O3 G u v (Lw n C (PEqualNP.TopForm.opnd C kj.1 ((1 : Fin 2) - kj.2)))
      (PEqualNP.TopForm.side (n := n) C kj.1 kj.2)

lemma linedetq_bnd {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    Bnd (LineDetQ G C) (2 * C.gates.length) := by
  have hc := prod_card C.gates.length
  unfold LineDetQ
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

def PayA {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (j : Fin 2) (u v : Fin n) : Prop :=
  PayC G C (SC G C 4 (An1 C j)) u v ∨ PayC G C (SC G C 4 (An2 C j)) u v ∨
    PayC G C (SC G C 4 (An3 G C K j)) u v

lemma paya_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) (j : Fin 2) :
    Bnd (PayA G C K j) (36 * C.gates.length) := by
  have p1 := payc_bnd G C h4 h2 4 _ (sc_ok G C 4 (An1 C j) (an1_fun C j))
  have p2 := payc_bnd G C h4 h2 4 _ (sc_ok G C 4 (An2 C j) (an2_fun C j))
  have p3 := payc_bnd G C h4 h2 4 _ (sc_ok G C 4 (An3 G C K j) (an3_fun G C K j))
  have hb := bnd_or p1 (bnd_or p2 p3)
  unfold PayA
  refine bnd_le ?_ hb
  omega

def Pay5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay4 G C K a b ∨ LineDetQ G C a b ∨ LineDetQ G C b a ∨ PayA G C K 0 a b ∨
    PayA G C K 0 b a ∨ PayA G C K 1 a b ∨ PayA G C K 1 b a

open PEqualNP.TopForm in
lemma pay5_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay5 G C 5) (2552 * C.gates.length) := by
  have q0 := paya_bnd G C h4 h2 5 0
  have q1 := paya_bnd G C h4 h2 5 1
  have hb := bnd_or (pay4_bnd G C h4 hAO2 h2) (bnd_or (linedetq_bnd G C)
    (bnd_or (bnd_swap (linedetq_bnd G C)) (bnd_or q0 (bnd_or (bnd_swap q0)
      (bnd_or q1 (bnd_swap q1))))))
  unfold Pay5
  refine bnd_le ?_ hb
  omega

lemma payd_pay5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) (h : PayD G C K u v) : Pay5 G C K u v :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))

lemma no_dirty_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (W A1 A2 : Finset (Fin n)) (hW : 5 ≤ W.card)
    (htest : ∀ w ∈ W, ∀ y1 ∈ A1, ∀ y2 ∈ A2, G.Adj w y1 ∨ G.Adj w y2 ∨ G.Adj y1 y2) :
    A1.card ≤ 3 ∨ A2.card ≤ 3 := by
  classical
  by_contra hcon
  simp only [not_or, not_le] at hcon
  by_cases hnd : ∀ y1 ∈ A1, ∀ y2 ∈ A2, G.Adj y1 y2
  · rcases biclique_star G h4 A1 A2 hnd with h | h <;> omega
  · obtain ⟨y1, hy1⟩ := not_forall.mp hnd
    obtain ⟨hy1m, hy1'⟩ := Classical.not_imp.mp hy1
    obtain ⟨y2, hy2⟩ := not_forall.mp hy1'
    obtain ⟨hy2m, hdirty⟩ := Classical.not_imp.mp hy2
    have hz : ∃ z : Fin n, 3 ≤ (W.filter (fun w => G.Adj w z)).card := by
      have hs := Finset.card_filter_add_card_filter_not (s := W) (fun w => G.Adj w y1)
      by_cases c1 : 3 ≤ (W.filter (fun w => G.Adj w y1)).card
      · exact ⟨y1, c1⟩
      · refine ⟨y2, ?_⟩
        have hsub : W.filter (fun w => ¬ G.Adj w y1) ⊆ W.filter (fun w => G.Adj w y2) := by
          intro w hw
          rw [Finset.mem_filter] at hw ⊢
          rcases htest w hw.1 y1 hy1m y2 hy2m with h | h | h
          · exact absurd h hw.2
          · exact ⟨hw.1, h⟩
          · exact absurd h hdirty
        have := Finset.card_le_card hsub
        omega
    obtain ⟨z, hz3⟩ := hz
    have hall : ∀ a1 ∈ A1.erase z, ∀ a2 ∈ A2.erase z, G.Adj a1 a2 := by
      intro a1 ha1 a2 ha2
      rw [Finset.mem_erase] at ha1 ha2
      by_contra hna
      have c1 : ((W.filter (fun w => G.Adj w z)).filter (fun w => G.Adj w a1)).card ≤ 1 := by
        refine le_trans (Finset.card_le_card ?_) (cn_pair_card G h4 z a1 (Ne.symm ha1.1))
        intro w hw
        rw [Finset.mem_filter, Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1.2, hw.2⟩
      have c2 : ((W.filter (fun w => G.Adj w z)).filter (fun w => ¬ G.Adj w a1)).card ≤ 1 := by
        refine le_trans (Finset.card_le_card ?_) (cn_pair_card G h4 z a2 (Ne.symm ha2.1))
        intro w hw
        rw [Finset.mem_filter, Finset.mem_filter] at hw
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1.2, ?_⟩
        rcases htest w hw.1.1 a1 ha1.2 a2 ha2.2 with h | h | h
        · exact absurd h hw.2
        · exact h
        · exact absurd h hna
      have hs := Finset.card_filter_add_card_filter_not (s := W.filter (fun w => G.Adj w z))
        (fun w => G.Adj w a1)
      omega
    have f1 := Finset.pred_card_le_card_erase (s := A1) (a := z)
    have f2 := Finset.pred_card_le_card_erase (s := A2) (a := z)
    rcases biclique_star G h4 _ _ hall with h | h <;> omega

open PEqualNP.TopForm in
lemma shape31_IIb2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 4 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hS3 : side (n := n) C k j = {v})
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (hu0 : u ∈ side (n := n) C h 0) (hu1 : u ∈ side (n := n) C h 1) : Pay5 G C K u v := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hv3 : v ∈ side (n := n) C k j := by rw [hS3]; exact Finset.mem_singleton_self v
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hrk := (orReaches_reach k _ hork).1
  have hrh := (orReaches_reach h _ horh).1
  have huh : u ∈ Lw n C (n + h) := mem_Lw.mpr (fires_both G C hAO2 h hh u hu0 hu1)
  have huQ : u ∈ Lw n C (opnd C k ((1 : Fin 2) - j)) := Lw_mono hrh huh
  have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
  have huq : ∀ y' ∈ Lw n C u.val, G.Adj v y' → y' = u :=
    fun y' hy' _ => (fires_input C u y').mp (mem_Lw.mp hy')
  have hmem : (k, j) ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hlen, Finset.mem_univ _⟩
  by_cases h1 : ∀ y ∈ Lw n C (opnd C k ((1 : Fin 2) - j)), G.Adj v y → y = u
  · exact Or.inr (Or.inl ⟨(k, j), hmem, huv, hS3, huQ, h1⟩)
  obtain ⟨u2, hu2a⟩ := not_forall.mp h1
  obtain ⟨hu2Q, hu2b⟩ := Classical.not_imp.mp hu2a
  obtain ⟨hvu2, hu2ne⟩ := Classical.not_imp.mp hu2b
  have ktrue : ∀ X : Fin n → Bool, X v = true →
      val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true → gateVal n C k X = true := by
    intro X hXv hQ
    apply (and_val2 C hAO2 k hlen hand X).mpr
    have a1 := side_leaf C k j v hv3 X hXv
    rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at a1; rw [e'] at hQ; exact ⟨a1, hQ⟩
    · rw [e] at a1; rw [e'] at hQ; exact ⟨hQ, a1⟩
  by_cases hW : (Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v)).card ≤ 4
  · have hsc : SC G C 4 (An1 C j) k v := by
      refine ⟨hS3, hand, _, hW, ?_⟩
      intro w hw
      by_cases hwv : G.Adj w v
      · exact Or.inl hwv
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hwv⟩)
    have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False := Or.inl huq
    rcases centred_pay G C hAO2 4 _ (sc_ok G C 4 (An1 C j) (an1_fun C j)) t ht i u v huv
      u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
    · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
      · rw [e] at h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h2))))
      · rw [e] at h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h2))))))
    · exact h2.elim
    · exact payd_pay5 G C K u v
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK h2))))))
  · have hW5 : 5 ≤ (Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v)).card := by
      omega
    refine payd_pay5 G C K u v (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    have test3 : ∀ w ∈ Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v),
        ∀ y ∈ (Lw n C (opnd C k ((1 : Fin 2) - j))).filter (fun y => ¬ G.Adj v y),
        G.Adj w y := by
      intro w hw y hy
      rw [Finset.mem_filter] at hw hy
      obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ z : Fin n, X z = true ↔ (z = w ∨ z = v ∨ z = y) :=
        ⟨fun z => decide (z = w ∨ z = v ∨ z = y), fun z => by simp⟩
      have hkv := ktrue X ((hx v).mpr (Or.inr (Or.inl rfl)))
        (mem_Lw.mp hy.1 X ((hx y).mpr (Or.inr (Or.inr rfl))))
      have hF : graphFun G ∅ X = true := hw.2.1 X ((hx w).mpr (Or.inl rfl)) hkv
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hF
      obtain ⟨a, b, hab, ha, hb⟩ := hF
      rcases (hx a).mp ha with e1 | e1 | e1 <;> rcases (hx b).mp hb with e2 | e2 | e2 <;>
        rw [e1, e2] at hab
      · exact (G.irrefl hab).elim
      · exact absurd hab hw.2.2
      · exact hab
      · exact absurd hab.symm hw.2.2
      · exact (G.irrefl hab).elim
      · exact absurd hab hy.2
      · exact hab.symm
      · exact absurd hab.symm hy.2
      · exact (G.irrefl hab).elim
    have hY1 : ((Lw n C (opnd C k ((1 : Fin 2) - j))).filter (fun y => ¬ G.Adj v y)).card ≤ 1 := by
      by_contra hc
      have hsub : Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v) ⊆
          Finset.univ.filter (fun x => ∀ d ∈ (Lw n C (opnd C k ((1 : Fin 2) - j))).filter
            (fun y => ¬ G.Adj v y), G.Adj x d) :=
        fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun d hd => test3 w hw d hd⟩
      have c1 := Finset.card_le_card hsub
      have c2 := cn_set_card G h4 ((Lw n C (opnd C k ((1 : Fin 2) - j))).filter
        (fun y => ¬ G.Adj v y)) (by omega)
      omega
    by_cases h2 : ∀ y ∈ Lw n C (n + h), G.Adj v y → y = u
    · exact cdl_mono G C (by omega) (cdl_of_path G C 1 v u huv.symm
        (opnd C k ((1 : Fin 2) - j)) (n + h) hrh huh h2 ⟨u2, hu2Q, hu2ne, hvu2⟩ hY1)
    · obtain ⟨u3, hu3a⟩ := not_forall.mp h2
      obtain ⟨hu3h, hu3b⟩ := Classical.not_imp.mp hu3a
      obtain ⟨hvu3, hu3ne⟩ := Classical.not_imp.mp hu3b
      have test4 : ∀ w ∈ Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v),
          ∀ y1 ∈ (Lw n C (opnd C h 0)).filter (fun y => ¬ G.Adj v y),
          ∀ y2 ∈ (Lw n C (opnd C h 1)).filter (fun y => ¬ G.Adj v y),
          G.Adj w y1 ∨ G.Adj w y2 ∨ G.Adj y1 y2 := by
        intro w hw y1 hy1 y2 hy2
        rw [Finset.mem_filter] at hw hy1 hy2
        obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
            ∀ z : Fin n, X z = true ↔ (z = w ∨ z = y1 ∨ z = y2 ∨ z = v) :=
          ⟨fun z => decide (z = w ∨ z = y1 ∨ z = y2 ∨ z = v), fun z => by simp⟩
        have hhv : gateVal n C h X = true :=
          (and_val2 C hAO2 h hlenh handh X).mpr
            ⟨mem_Lw.mp hy1.1 X ((hx y1).mpr (Or.inr (Or.inl rfl))),
              mem_Lw.mp hy2.1 X ((hx y2).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩
        have hkv := ktrue X ((hx v).mpr (Or.inr (Or.inr (Or.inr rfl))))
          (orStep_up (n := n) (by simp) hrh hhv)
        have hF : graphFun G ∅ X = true := hw.2.1 X ((hx w).mpr (Or.inl rfl)) hkv
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq] at hF
        obtain ⟨a, b, hab, ha, hb⟩ := hF
        exact tri_of_four G w y1 y2 v a b hab ((hx a).mp ha) ((hx b).mp hb)
          (fun hvw => hw.2.2 hvw.symm) hy1.2 hy2.2
      have hu3_0 : u3 ∈ Lw n C (opnd C h 0) :=
        mem_Lw.mpr (fires_opnd G C hAO2 h hh 0 u3 (mem_Lw.mp hu3h))
      have hu3_1 : u3 ∈ Lw n C (opnd C h 1) :=
        mem_Lw.mpr (fires_opnd G C hAO2 h hh 1 u3 (mem_Lw.mp hu3h))
      rcases no_dirty_small G h4 _ _ _ hW5 test4 with hA | hA
      · exact cdl_mono G C (by omega) (cdl_of_path G C 3 v u huv.symm (opnd C h 0) u.val
          (mem_orIn_reach u hu0) huu huq ⟨u3, hu3_0, hu3ne, hvu3⟩ hA)
      · exact cdl_mono G C (by omega) (cdl_of_path G C 3 v u huv.symm (opnd C h 1) u.val
          (mem_orIn_reach u hu1) huu huq ⟨u3, hu3_1, hu3ne, hvu3⟩ hA)

open PEqualNP.TopForm in
lemma shape31_IIb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 4 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (hu0 : u ∈ side (n := n) C h 0) (hu1 : u ∈ side (n := n) C h 1) : Pay5 G C K u v := by
  classical
  by_cases hy : ∃ y ∈ side (n := n) C k j, y ≠ v
  · obtain ⟨y, hy3, hyv⟩ := hy
    exact payd_pay5 G C K u v (Or.inl (shape31_IIb1 G C hAO2 K t ht i u v huv hside k hk hork
      j hv3 y hy3 hyv h hh horh hu0 hu1))
  · have hS3 : side (n := n) C k j = {v} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy'
        by_contra hne
        exact hy ⟨y, hy', hne⟩
      · intro e
        rw [e]; exact hv3
    exact shape31_IIb2 G C h4 hAO2 K hK t ht i u v huv hside k hk hork j hS3 h hh horh hu0 hu1

def AnLo {n : ℕ} (C : Circuit) (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  (Lw n C (PEqualNP.TopForm.opnd C k j)).card ≤ 2 ∧
    v ∈ Lw n C (PEqualNP.TopForm.opnd C k j) ∧
    ∀ y ∈ Lw n C (PEqualNP.TopForm.opnd C k j), v ≤ y

def AnHi {n : ℕ} (C : Circuit) (j : Fin 2) (k : ℕ) (v : Fin n) : Prop :=
  (Lw n C (PEqualNP.TopForm.opnd C k j)).card ≤ 2 ∧
    v ∈ Lw n C (PEqualNP.TopForm.opnd C k j) ∧
    ∀ y ∈ Lw n C (PEqualNP.TopForm.opnd C k j), y ≤ v

lemma anlo_fun {n : ℕ} (C : Circuit) (j : Fin 2) :
    ∀ (k : ℕ) (v v' : Fin n), AnLo C j k v → AnLo C j k v' → v' = v :=
  fun _ _ _ h h' => le_antisymm (h'.2.2 _ h.2.1) (h.2.2 _ h'.2.1)

lemma anhi_fun {n : ℕ} (C : Circuit) (j : Fin 2) :
    ∀ (k : ℕ) (v v' : Fin n), AnHi C j k v → AnHi C j k v' → v' = v :=
  fun _ _ _ h h' => le_antisymm (h.2.2 _ h'.2.1) (h'.2.2 _ h.2.1)

lemma lo_or_hi {n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 2) (x : Fin n) (hx : x ∈ S) :
    (∀ y ∈ S, x ≤ y) ∨ (∀ y ∈ S, y ≤ x) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le] at hcon
  obtain ⟨⟨y, hy, hyx⟩, ⟨z, hz, hxz⟩⟩ := hcon
  have h3 : ({y, x, z} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨y, x, z, hyx.ne, (hyx.trans hxz).ne, hxz.ne, rfl⟩
  have hsub : ({y, x, z} : Finset (Fin n)) ⊆ S := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hy
    · exact hx
    · exact hz
  have := Finset.card_le_card hsub
  omega

lemma thin_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (z x : Fin n) (hd : (S.filter (fun y => ¬ G.Adj z y)).card ≤ 1)
    (ho : ∀ y ∈ S, G.Adj z y → y = x) : S.card ≤ 2 := by
  classical
  have hs := Finset.card_filter_add_card_filter_not (s := S) (fun y => G.Adj z y)
  have h1 : (S.filter (fun y => G.Adj z y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact (ho a ha.1 ha.2).trans (ho b hb.1 hb.2).symm
  omega

def PayL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : Fin 2) (u v : Fin n) : Prop :=
  PayC G C (SC G C 1 (AnLo C j)) u v ∨ PayC G C (SC G C 1 (AnHi C j)) u v

lemma payl_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (j : Fin 2) :
    Bnd (PayL G C j) (12 * C.gates.length) := by
  have p1 := payc_bnd G C h4 h2 1 _ (sc_ok G C 1 (AnLo C j) (anlo_fun C j))
  have p2 := payc_bnd G C h4 h2 1 _ (sc_ok G C 1 (AnHi C j) (anhi_fun C j))
  have hb := bnd_or p1 p2
  unfold PayL
  refine bnd_le ?_ hb
  omega

def Pay6 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay5 G C K a b ∨ PayL G C 0 a b ∨ PayL G C 0 b a ∨ PayL G C 1 a b ∨ PayL G C 1 b a

open PEqualNP.TopForm in
lemma pay6_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay6 G C 5) (2600 * C.gates.length) := by
  have q0 := payl_bnd G C h4 h2 0
  have q1 := payl_bnd G C h4 h2 1
  have hb := bnd_or (pay5_bnd G C h4 hAO2 h2) (bnd_or q0 (bnd_or (bnd_swap q0)
    (bnd_or q1 (bnd_swap q1))))
  unfold Pay6
  refine bnd_le ?_ hb
  omega

lemma payd_pay6 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) (h : PayD G C K u v) : Pay6 G C K u v :=
  Or.inl (payd_pay5 G C K u v h)

open PEqualNP.TopForm in
lemma iic_ktrue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (k : ℕ) (hk : k ∈ junk G C) (j : Fin 2)
    (h : ℕ) (hh : h ∈ junk G C)
    (hrh : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + h))
    (ju : Fin 2) (X : Fin n → Bool)
    (h3 : val C (List.ofFn X) (opnd C k j) = true)
    (h1 : val C (List.ofFn X) (opnd C h ju) = true)
    (h2 : val C (List.ofFn X) (opnd C h ((1 : Fin 2) - ju)) = true) :
    gateVal n C k X = true := by
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hhv : gateVal n C h X = true := by
    apply (and_val2 C hAO2 h hlenh handh X).mpr
    rcases fin2_sub ju with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at h1; rw [e'] at h2; exact ⟨h1, h2⟩
    · rw [e] at h1; rw [e'] at h2; exact ⟨h2, h1⟩
  have hQ : val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true :=
    orStep_up (n := n) (by simp) hrh hhv
  apply (and_val2 C hAO2 k hlen hand X).mpr
  rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
  · rw [e] at h3; rw [e'] at hQ; exact ⟨h3, hQ⟩
  · rw [e] at h3; rw [e'] at hQ; exact ⟨hQ, h3⟩

open PEqualNP.TopForm in
lemma iic_utest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (k : ℕ) (hk : k ∈ junk G C) (j : Fin 2)
    (h : ℕ) (hh : h ∈ junk G C)
    (hrh : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + h))
    (ju : Fin 2) (u : Fin n) (hcl : Cl G C u (n + k)) (hu1 : Fires n C (opnd C h ju) u) :
    ∀ y3 ∈ Lw n C (opnd C k j), ∀ y2 ∈ Lw n C (opnd C h ((1 : Fin 2) - ju)),
      ¬ G.Adj u y3 → ¬ G.Adj u y2 → G.Adj y3 y2 := by
  intro y3 hy3 y2 hy2 hu3 hu2
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ z : Fin n, X z = true ↔ (z = u ∨ z = y3 ∨ z = y2) :=
    ⟨fun z => decide (z = u ∨ z = y3 ∨ z = y2), fun z => by simp⟩
  have hkv := iic_ktrue G C hAO2 k hk j h hh hrh ju X
    (mem_Lw.mp hy3 X ((hx y3).mpr (Or.inr (Or.inl rfl))))
    (hu1 X ((hx u).mpr (Or.inl rfl)))
    (mem_Lw.mp hy2 X ((hx y2).mpr (Or.inr (Or.inr rfl))))
  have hF : graphFun G ∅ X = true := hcl X ((hx u).mpr (Or.inl rfl)) hkv
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨a, b, hab, ha, hb⟩ := hF
  rcases (hx a).mp ha with e1 | e1 | e1 <;> rcases (hx b).mp hb with e2 | e2 | e2 <;>
    rw [e1, e2] at hab
  · exact (G.irrefl hab).elim
  · exact absurd hab hu3
  · exact absurd hab hu2
  · exact absurd hab.symm hu3
  · exact (G.irrefl hab).elim
  · exact hab
  · exact absurd hab.symm hu2
  · exact hab.symm
  · exact (G.irrefl hab).elim

open PEqualNP.TopForm in
lemma iic_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (k : ℕ) (hk : k ∈ junk G C) (j : Fin 2)
    (h : ℕ) (hh : h ∈ junk G C)
    (hrh : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + h))
    (ju : Fin 2) (v : Fin n) (hvP : Fires n C (opnd C k j) v)
    (hv2 : Fires n C (opnd C h ((1 : Fin 2) - ju)) v)
    (w : Fin n) (hcl : Cl G C w (n + k)) (hwv : ¬ G.Adj w v) :
    ∀ y1 ∈ (Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y), G.Adj w y1 := by
  intro y1 hy1
  rw [Finset.mem_filter] at hy1
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool, ∀ z : Fin n, X z = true ↔ (z = w ∨ z = v ∨ z = y1) :=
    ⟨fun z => decide (z = w ∨ z = v ∨ z = y1), fun z => by simp⟩
  have hXv : X v = true := (hx v).mpr (Or.inr (Or.inl rfl))
  have hkv := iic_ktrue G C hAO2 k hk j h hh hrh ju X (hvP X hXv)
    (mem_Lw.mp hy1.1 X ((hx y1).mpr (Or.inr (Or.inr rfl)))) (hv2 X hXv)
  have hF : graphFun G ∅ X = true := hcl X ((hx w).mpr (Or.inl rfl)) hkv
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨a, b, hab, ha, hb⟩ := hF
  rcases (hx a).mp ha with e1 | e1 | e1 <;> rcases (hx b).mp hb with e2 | e2 | e2 <;>
    rw [e1, e2] at hab
  · exact (G.irrefl hab).elim
  · exact absurd hab hwv
  · exact hab
  · exact absurd hab.symm hwv
  · exact (G.irrefl hab).elim
  · exact absurd hab hy1.2
  · exact hab.symm
  · exact absurd hab.symm hy1.2
  · exact (G.irrefl hab).elim

open PEqualNP.TopForm in
lemma shape31_IIc {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (ju : Fin 2) (hu1 : u ∈ side (n := n) C h ju)
    (hv2 : v ∈ side (n := n) C h ((1 : Fin 2) - ju)) :
    Pay6 G C K u v ∨
      ((((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card ≤ 1 ∧
          ∀ y ∈ Lw n C (opnd C h ju), G.Adj v y → y = u) ∧
        ((Lw n C (opnd C k j)).filter (fun y => ¬ G.Adj u y)).card ≤ 1 ∧
          ∀ y ∈ Lw n C (opnd C k j), G.Adj u y → y = v) ∨
      (2 ≤ ((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card ∧
        ((Lw n C (opnd C h ((1 : Fin 2) - ju))).filter (fun y => ¬ G.Adj u y)).card ≤ 1 ∧
          ∀ y ∈ Lw n C (opnd C h ((1 : Fin 2) - ju)), G.Adj u y → y = v) := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hrk := (orReaches_reach k _ hork).1
  have hrh := (orReaches_reach h _ horh).1
  have hcl : Cl G C u (n + k) := cl_mono G C (cl_top G C hAO2 t ht i u hfu) hrk
  have hvP : Fires n C (opnd C k j) v := fires_side C k j v hv3
  have hu1f : Fires n C (opnd C h ju) u := fires_side C h ju u hu1
  have hv2f : Fires n C (opnd C h ((1 : Fin 2) - ju)) v := fires_side C h _ v hv2
  have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
  have huq : ∀ y' ∈ Lw n C u.val, G.Adj v y' → y' = u :=
    fun y' hy' _ => (fires_input C u y').mp (mem_Lw.mp hy')
  have hvv : v ∈ Lw n C v.val := mem_Lw.mpr ((fires_input C v v).mpr rfl)
  have hvq : ∀ y' ∈ Lw n C v.val, G.Adj u y' → y' = v :=
    fun y' hy' _ => (fires_input C v y').mp (mem_Lw.mp hy')
  have payUV : CDL G C 1 u v → Pay6 G C K u v := fun c =>
    payd_pay6 G C K u v (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK c)))))
  have payVU : CDL G C 1 v u → Pay6 G C K u v := fun c =>
    payd_pay6 G C K u v (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK c))))))
  have hUt := iic_utest G C hAO2 k hk j h hh hrh ju u hcl hu1f
  have hU : CDL G C 1 u v ∨
      (((Lw n C (opnd C k j)).filter (fun y => ¬ G.Adj u y)).card ≤ 1 ∧
        ∀ y ∈ Lw n C (opnd C k j), G.Adj u y → y = v) ∨
      (((Lw n C (opnd C h ((1 : Fin 2) - ju))).filter (fun y => ¬ G.Adj u y)).card ≤ 1 ∧
        ∀ y ∈ Lw n C (opnd C h ((1 : Fin 2) - ju)), G.Adj u y → y = v) := by
    rcases dirt_star G h4 u _ _ hUt with d | d
    · by_cases hs : ∃ b ∈ Lw n C (opnd C k j), b ≠ v ∧ G.Adj u b
      · exact Or.inl (cdl_of_path G C 1 u v huv (opnd C k j) v.val (mem_orIn_reach v hv3)
          hvv hvq hs d)
      · refine Or.inr (Or.inl ⟨d, fun y hy huy => ?_⟩)
        by_contra hne
        exact hs ⟨y, hy, hne, huy⟩
    · by_cases hs : ∃ b ∈ Lw n C (opnd C h ((1 : Fin 2) - ju)), b ≠ v ∧ G.Adj u b
      · exact Or.inl (cdl_of_path G C 1 u v huv (opnd C h ((1 : Fin 2) - ju)) v.val
          (mem_orIn_reach v hv2) hvv hvq hs d)
      · refine Or.inr (Or.inr ⟨d, fun y hy huy => ?_⟩)
        by_contra hne
        exact hs ⟨y, hy, hne, huy⟩
  have hsmallA : ¬ 2 ≤ ((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card →
      CDL G C 1 v u ∨
        (((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card ≤ 1 ∧
          ∀ y ∈ Lw n C (opnd C h ju), G.Adj v y → y = u) := by
    intro hD1
    have d : ((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card ≤ 1 := by omega
    by_cases hs : ∃ b ∈ Lw n C (opnd C h ju), b ≠ u ∧ G.Adj v b
    · exact Or.inl (cdl_of_path G C 1 v u huv.symm (opnd C h ju) u.val (mem_orIn_reach u hu1)
        huu huq hs d)
    · refine Or.inr ⟨d, fun y hy hvy => ?_⟩
      by_contra hne
      exact hs ⟨y, hy, hne, hvy⟩
  rcases hU with c | hPthin | hBthin
  · exact Or.inl (payUV c)
  · by_cases hD1 : 2 ≤ ((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card
    · left
      have hcard := thin_card G (Lw n C (opnd C k j)) u v hPthin.1 hPthin.2
      have hvL : v ∈ Lw n C (opnd C k j) := mem_Lw.mpr hvP
      have hM : (Finset.univ.filter (fun x => ∀ d ∈ (Lw n C (opnd C h ju)).filter
          (fun y => ¬ G.Adj v y), G.Adj x d)).card ≤ 1 := cn_set_card G h4 _ hD1
      have hclean : ∀ w : Fin n, Cl G C w (n + k) → G.Adj w v ∨
          w ∈ Finset.univ.filter (fun x => ∀ d ∈ (Lw n C (opnd C h ju)).filter
            (fun y => ¬ G.Adj v y), G.Adj x d) := by
        intro w hw
        by_cases hwv : G.Adj w v
        · exact Or.inl hwv
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            iic_clean G C hAO2 k hk j h hh hrh ju v hvP hv2f w hw hwv⟩)
      have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False := Or.inl huq
      rcases lo_or_hi _ hcard v hvL with hlo | hhi
      · have hsc : SC G C 1 (AnLo C j) k v := ⟨⟨hcard, hvL, hlo⟩, hand, _, hM, hclean⟩
        rcases centred_pay G C hAO2 1 _ (sc_ok G C 1 (AnLo C j) (anlo_fun C j)) t ht i u v huv
          u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
        · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
          · rw [e] at h2
            exact Or.inr (Or.inl (Or.inl h2))
          · rw [e] at h2
            exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h2))))
        · exact h2.elim
        · exact payVU h2
      · have hsc : SC G C 1 (AnHi C j) k v := ⟨⟨hcard, hvL, hhi⟩, hand, _, hM, hclean⟩
        rcases centred_pay G C hAO2 1 _ (sc_ok G C 1 (AnHi C j) (anhi_fun C j)) t ht i u v huv
          u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
        · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
          · rw [e] at h2
            exact Or.inr (Or.inl (Or.inr h2))
          · rw [e] at h2
            exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h2))))
        · exact h2.elim
        · exact payVU h2
    · rcases hsmallA hD1 with c | hAthin
      · exact Or.inl (payVU c)
      · exact Or.inr (Or.inl ⟨hAthin, hPthin⟩)
  · by_cases hD1 : 2 ≤ ((Lw n C (opnd C h ju)).filter (fun y => ¬ G.Adj v y)).card
    · exact Or.inr (Or.inr ⟨hD1, hBthin⟩)
    · rcases hsmallA hD1 with c | hAthin
      · exact Or.inl (payVU c)
      · left
        have cA := thin_card G (Lw n C (opnd C h ju)) v u hAthin.1 hAthin.2
        have cB := thin_card G (Lw n C (opnd C h ((1 : Fin 2) - ju))) u v hBthin.1 hBthin.2
        have sA : (side (n := n) C h ju).card ≤ K + 1 := by
          refine le_trans (Finset.card_le_card ?_) (le_trans cA (by omega))
          intro x hx
          exact mem_Lw.mpr (fires_side C h ju x hx)
        have sB : (side (n := n) C h ((1 : Fin 2) - ju)).card ≤ K + 1 := by
          refine le_trans (Finset.card_le_card ?_) (le_trans cB (by omega))
          intro x hx
          exact mem_Lw.mpr (fires_side C h _ x hx)
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl
          (smallgate_of C (K + 1) h hlenh ju u v sA sB hu1 hv2))))))))

def LineDet2 {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ (PEqualNP.TopForm.side (n := n) C kj.1 ((1 : Fin 2) - kj.2)).card ≤ 2 ∧
    v ∈ PEqualNP.TopForm.side (n := n) C kj.1 ((1 : Fin 2) - kj.2) ∧
    u ∈ PEqualNP.TopForm.side (n := n) C kj.1 kj.2 ∧
    ∀ y ∈ PEqualNP.TopForm.side (n := n) C kj.1 kj.2, G.Adj v y → y = u

lemma linedet2_bnd {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    Bnd (LineDet2 G C) (2 * (2 * C.gates.length)) := by
  classical
  have hc := prod_card C.gates.length
  unfold LineDet2
  refine bnd_le (le_of_eq (by rw [hc])) (obj_count _ 2 _ ?_)
  intro kj _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, hcard, _, _, _⟩ := hP zv0 hzv0
    refine le_trans (Finset.card_le_card_of_injOn (f := Prod.snd)
      (t := PEqualNP.TopForm.side (n := n) C kj.1 ((1 : Fin 2) - kj.2)) ?_ ?_) hcard
    · intro zv hzv
      exact Finset.mem_coe.mpr (hP zv (Finset.mem_coe.mp hzv)).2.2.1
    · intro zv hzv zv' hzv' heq
      obtain ⟨_, _, _, _, a5⟩ := hP zv (Finset.mem_coe.mp hzv)
      obtain ⟨badj, _, _, b4, _⟩ := hP zv' (Finset.mem_coe.mp hzv')
      have e1 : zv'.1 = zv.1 := a5 zv'.1 b4 (by rw [heq]; exact badj.symm)
      exact Prod.ext e1.symm heq

def FewClean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ (∃ W : Finset (Fin n), W.card ≤ 3 ∧ ∀ w, Cl G C w (n + kj.1) → w ∈ W) ∧
    Cl G C u (n + kj.1) ∧ v ∈ PEqualNP.TopForm.side (n := n) C kj.1 kj.2 ∧
    ∀ y ∈ PEqualNP.TopForm.side (n := n) C kj.1 kj.2, G.Adj u y → y = v

lemma fewclean_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Bnd (FewClean G C) (3 * (2 * C.gates.length)) := by
  classical
  have hc := prod_card C.gates.length
  unfold FewClean
  refine bnd_le (le_of_eq (by rw [hc])) (obj_count _ 3 _ ?_)
  intro kj _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  · obtain ⟨_, ⟨W, hW, hWall⟩, _, _, _⟩ := hP zv0 hzv0
    refine le_trans (Finset.card_le_card_of_injOn (f := Prod.fst) (t := W) ?_ ?_) hW
    · intro zv hzv
      exact Finset.mem_coe.mpr (hWall zv.1 (hP zv (Finset.mem_coe.mp hzv)).2.2.1)
    · intro zv hzv zv' hzv' heq
      obtain ⟨_, _, _, _, a5⟩ := hP zv (Finset.mem_coe.mp hzv)
      obtain ⟨badj, _, _, b4, _⟩ := hP zv' (Finset.mem_coe.mp hzv')
      have e2 : zv'.2 = zv.2 := a5 zv'.2 b4 (by rw [heq]; exact badj)
      exact Prod.ext heq e2.symm

def C1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (v : Fin n) : Prop :=
  ∃ M : Finset (Fin n), M.card ≤ 1 ∧ ∀ w : Fin n, Cl G C w (n + k) → G.Adj w v ∨ w ∈ M

def An7 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : Fin 2)
    (k : ℕ) (v : Fin n) : Prop :=
  v ∈ PEqualNP.TopForm.side (n := n) C k j ∧ C1 G C k v ∧
    ∀ v' ∈ PEqualNP.TopForm.side (n := n) C k j, C1 G C k v' → v' = v

lemma an7_fun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : Fin 2) : ∀ (k : ℕ) (v v' : Fin n), An7 G C j k v → An7 G C j k v' → v' = v :=
  fun _ _ _ h h' => h.2.2 _ h'.1 h'.2.1

lemma two_c1_few {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (k : ℕ) (v v' : Fin n) (hne : v' ≠ v) (h1 : C1 G C k v) (h2 : C1 G C k v') :
    ∃ W : Finset (Fin n), W.card ≤ 3 ∧ ∀ w, Cl G C w (n + k) → w ∈ W := by
  classical
  obtain ⟨M, hM, hcl⟩ := h1
  obtain ⟨M', hM', hcl'⟩ := h2
  refine ⟨(Finset.univ.filter (fun x => G.Adj x v ∧ G.Adj x v')) ∪ (M ∪ M'), ?_, ?_⟩
  · have c1 := cn_pair_card G h4 v v' (Ne.symm hne)
    have u1 := Finset.card_union_le (Finset.univ.filter (fun x => G.Adj x v ∧ G.Adj x v'))
      (M ∪ M')
    have u2 := Finset.card_union_le M M'
    omega
  · intro w hw
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcl w hw with a | a
    · rcases hcl' w hw with b | b
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr (Or.inr b)
    · exact Or.inr (Or.inl a)

def PayM {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (u v : Fin n) : Prop :=
  LineDet2 G C u v ∨ FewClean G C u v ∨ PayC G C (SC G C 1 (An7 G C 0)) u v ∨
    PayC G C (SC G C 1 (An7 G C 1)) u v

lemma paym_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (PayM G C) (22 * C.gates.length) := by
  have p0 := payc_bnd G C h4 h2 1 _ (sc_ok G C 1 (An7 G C 0) (an7_fun G C 0))
  have p1 := payc_bnd G C h4 h2 1 _ (sc_ok G C 1 (An7 G C 1) (an7_fun G C 1))
  have hb := bnd_or (linedet2_bnd G C) (bnd_or (fewclean_bnd G C) (bnd_or p0 p1))
  unfold PayM
  refine bnd_le ?_ hb
  omega

def Pay7 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay6 G C K a b ∨ PayM G C a b ∨ PayM G C b a

open PEqualNP.TopForm in
lemma pay7_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay7 G C 5) (2644 * C.gates.length) := by
  have q := paym_bnd G C h4 h2
  have hb := bnd_or (pay6_bnd G C h4 hAO2 h2) (bnd_or q (bnd_swap q))
  unfold Pay7
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma shape31_IIc2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 1 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (ju : Fin 2) (hu1 : u ∈ side (n := n) C h ju)
    (hv2 : v ∈ side (n := n) C h ((1 : Fin 2) - ju)) :
    Pay7 G C K u v ∨
      ((Lw n C (opnd C h ju)).card ≤ 2 ∧ (Lw n C (opnd C k j)).card ≤ 2 ∧
        K < ((side (n := n) C h ((1 : Fin 2) - ju)).filter (fun y => ¬ G.Adj u y)).card ∧
        ∃ b ∈ side (n := n) C h ((1 : Fin 2) - ju), b ≠ v ∧ G.Adj u b) ∨
      ((∃ W : Finset (Fin n), W.card ≤ 3 ∧ ∀ w, Cl G C w (n + k) → w ∈ W) ∧
        K < ((side (n := n) C k j).filter (fun y => ¬ G.Adj u y)).card ∧
        (∃ b ∈ side (n := n) C k j, b ≠ v ∧ G.Adj u b) ∧
        K < ((side (n := n) C h ju).filter (fun y => ¬ G.Adj v y)).card ∧
        (∃ b ∈ side (n := n) C h ju, b ≠ u ∧ G.Adj v b) ∧
        (Lw n C (opnd C h ((1 : Fin 2) - ju))).card ≤ 2) := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hrk := (orReaches_reach k _ hork).1
  have hrh := (orReaches_reach h _ horh).1
  have hcl : Cl G C u (n + k) := cl_mono G C (cl_top G C hAO2 t ht i u hfu) hrk
  have hvP : Fires n C (opnd C k j) v := fires_side C k j v hv3
  have hv2f : Fires n C (opnd C h ((1 : Fin 2) - ju)) v := fires_side C h _ v hv2
  have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
  have huq : ∀ y' ∈ Lw n C u.val, G.Adj v y' → y' = u :=
    fun y' hy' _ => (fires_input C u y').mp (mem_Lw.mp hy')
  have hmemk : (k, j) ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hlen, Finset.mem_univ _⟩
  rcases shape31_IIc G C h4 hAO2 K hK t ht i u v huv hside k hk hork j hv3 h hh horh ju hu1
    hv2 with h' | ⟨hAthin, hPthin⟩ | ⟨hD1, hBthin⟩
  · exact Or.inl (Or.inl h')
  · have cA := thin_card G (Lw n C (opnd C h ju)) v u hAthin.1 hAthin.2
    have cP := thin_card G (Lw n C (opnd C k j)) u v hPthin.1 hPthin.2
    by_cases hs : ∃ b ∈ side (n := n) C h ((1 : Fin 2) - ju), b ≠ v ∧ G.Adj u b
    · by_cases hd : ((side (n := n) C h ((1 : Fin 2) - ju)).filter
          (fun y => ¬ G.Adj u y)).card ≤ K
      · exact Or.inl (Or.inl (payd_pay6 G C K u v
          (Or.inl ⟨huv, opnd C h ((1 : Fin 2) - ju), hv2, hs, hd⟩)))
      · exact Or.inr (Or.inl ⟨cA, cP, by omega, hs⟩)
    · left; right; right; left
      have hcardA : (side (n := n) C h ((1 : Fin 2) - ((1 : Fin 2) - ju))).card ≤ 2 := by
        rw [fin2_ss]
        refine le_trans (Finset.card_le_card ?_) cA
        intro x hx
        exact mem_Lw.mpr (fires_side C h ju x hx)
      have huA : u ∈ side (n := n) C h ((1 : Fin 2) - ((1 : Fin 2) - ju)) := by
        rw [fin2_ss]; exact hu1
      exact ⟨(h, (1 : Fin 2) - ju), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hlenh, Finset.mem_univ _⟩, huv.symm, hcardA, huA, hv2,
        fun y hy huy => by
          by_contra hne
          exact hs ⟨y, hy, hne, huy⟩⟩
  · have hS1 : Pay7 G C K u v ∨
        (K < ((side (n := n) C h ju).filter (fun y => ¬ G.Adj v y)).card ∧
          ∃ b ∈ side (n := n) C h ju, b ≠ u ∧ G.Adj v b) := by
      by_cases hs : ∃ b ∈ side (n := n) C h ju, b ≠ u ∧ G.Adj v b
      · by_cases hd : ((side (n := n) C h ju).filter (fun y => ¬ G.Adj v y)).card ≤ K
        · exact Or.inl (Or.inl (payd_pay6 G C K u v
            (Or.inr (Or.inl ⟨huv.symm, opnd C h ju, hu1, hs, hd⟩))))
        · exact Or.inr ⟨by omega, hs⟩
      · left; right; left; left
        have cB := thin_card G (Lw n C (opnd C h ((1 : Fin 2) - ju))) u v hBthin.1 hBthin.2
        have hcardB : (side (n := n) C h ((1 : Fin 2) - ju)).card ≤ 2 := by
          refine le_trans (Finset.card_le_card ?_) cB
          intro x hx
          exact mem_Lw.mpr (fires_side C h _ x hx)
        exact ⟨(h, ju), Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hlenh, Finset.mem_univ _⟩, huv, hcardB, hv2, hu1,
          fun y hy hvy => by
            by_contra hne
            exact hs ⟨y, hy, hne, hvy⟩⟩
    rcases hS1 with hpaid | hS1heavy
    · exact Or.inl hpaid
    have hc1 : C1 G C k v := by
      refine ⟨Finset.univ.filter (fun x => ∀ d ∈ (Lw n C (opnd C h ju)).filter
        (fun y => ¬ G.Adj v y), G.Adj x d), cn_set_card G h4 _ hD1, ?_⟩
      intro w hw
      by_cases hwv : G.Adj w v
      · exact Or.inl hwv
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          iic_clean G C hAO2 k hk j h hh hrh ju v hvP hv2f w hw hwv⟩)
    by_cases huniq : ∀ v' ∈ side (n := n) C k j, C1 G C k v' → v' = v
    · left
      have hsc : SC G C 1 (An7 G C j) k v := ⟨⟨hv3, hc1, huniq⟩, hand, hc1⟩
      have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False := Or.inl huq
      rcases centred_pay G C hAO2 1 _ (sc_ok G C 1 (An7 G C j) (an7_fun G C j)) t ht i u v huv
        u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
      · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
        · rw [e] at h2
          exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h2))))
        · rw [e] at h2
          exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h2))))
      · exact h2.elim
      · exact Or.inl (payd_pay6 G C K u v
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK h2)))))))
    · obtain ⟨v', hv'1⟩ := not_forall.mp huniq
      obtain ⟨hv's, hv'2⟩ := Classical.not_imp.mp hv'1
      obtain ⟨hv'c, hv'ne⟩ := Classical.not_imp.mp hv'2
      have hfew := two_c1_few G C h4 k v v' hv'ne hc1 hv'c
      by_cases hs : ∃ b ∈ side (n := n) C k j, b ≠ v ∧ G.Adj u b
      · by_cases hd : ((side (n := n) C k j).filter (fun y => ¬ G.Adj u y)).card ≤ K
        · exact Or.inl (Or.inl (payd_pay6 G C K u v
            (Or.inl ⟨huv, opnd C k j, hv3, hs, hd⟩)))
        · exact Or.inr (Or.inr ⟨hfew, by omega, hs, hS1heavy.1, hS1heavy.2,
            thin_card G (Lw n C (opnd C h ((1 : Fin 2) - ju))) u v hBthin.1 hBthin.2⟩)
      · left; right; left; right; left
        refine ⟨(k, j), hmemk, huv, hfew, hcl, hv3, ?_⟩
        intro y hy huy
        by_contra hne
        exact hs ⟨y, hy, hne, huy⟩

def WHL {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) (h : ℕ)
    (v : Fin n) : Prop :=
  h < C.gates.length ∧ (gateAt C h).op = GateOp.and ∧ ∃ j : Fin 2,
    Fires n C (PEqualNP.TopForm.opnd C h ((1 : Fin 2) - j)) v ∧
    K < ((PEqualNP.TopForm.side (n := n) C h j).filter (fun y => ¬ G.Adj v y)).card

def ZWp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) (r : ℕ)
    (v : Fin n) : Prop :=
  ∃ h : ℕ, Relation.ReflTransGen (OrStep n C) r (n + h) ∧ WHL G C K h v

lemma z5_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (D : Finset (Fin n)) (hD : 4 ≤ D.card) (x y : Fin n)
    (hx : (D.filter (fun d => ¬ G.Adj x d)).card ≤ 1)
    (hy : (D.filter (fun d => ¬ G.Adj y d)).card ≤ 1) : x = y := by
  by_contra hne
  have := card_two_centres G h4 x y hne D 1 1 hx hy
  omega

lemma z5_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (D : Finset (Fin n)) (hD : 4 ≤ D.card) :
    (Finset.univ.filter (fun x => (D.filter (fun d => ¬ G.Adj x d)).card ≤ 1)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  exact z5_unique G h4 D hD x y hx.2 hy.2

lemma cnf_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v w : Fin n) :
    (Finset.univ.filter (fun x => w ≠ v ∧ G.Adj x v ∧ G.Adj x w)).card ≤ 1 := by
  by_cases hwv : w = v
  · have he : Finset.univ.filter (fun x => w ≠ v ∧ G.Adj x v ∧ G.Adj x w) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun x _ hx => hx.1 hwv)
    rw [he]; simp
  · refine le_trans (Finset.card_le_card ?_) (cn_pair_card G h4 v w (Ne.symm hwv))
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.2⟩

open PEqualNP.TopForm in
lemma s3_test {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (k : ℕ) (j : Fin 2) (hlen : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) (u : Fin n) (hcl : Cl G C u (n + k))
    (h' : ℕ) (hr : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + h'))
    (hlen' : h' < C.gates.length) (hand' : (gateAt C h').op = GateOp.and)
    (j' : Fin 2) (w : Fin n) (hw : Fires n C (opnd C h' ((1 : Fin 2) - j')) w) :
    G.Adj u w ∨
      (((side (n := n) C h' j').filter (fun y => ¬ G.Adj w y)).filter
        (fun d => ¬ G.Adj u d)).card ≤ 1 ∨
      (((side (n := n) C k j).filter (fun y => ¬ G.Adj u y)).filter
        (fun d => ¬ G.Adj w d)).card ≤ 1 := by
  classical
  by_cases huw : G.Adj u w
  · exact Or.inl huw
  right
  have hall : ∀ s ∈ ((side (n := n) C k j).filter (fun y => ¬ G.Adj u y)).filter
      (fun d => ¬ G.Adj w d),
      ∀ a ∈ ((side (n := n) C h' j').filter (fun y => ¬ G.Adj w y)).filter
        (fun d => ¬ G.Adj u d), G.Adj s a := by
    intro s hs a ha
    rw [Finset.mem_filter, Finset.mem_filter] at hs ha
    obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
        ∀ z : Fin n, X z = true ↔ (z = u ∨ z = s ∨ z = a ∨ z = w) :=
      ⟨fun z => decide (z = u ∨ z = s ∨ z = a ∨ z = w), fun z => by simp⟩
    have hhv : gateVal n C h' X = true := by
      apply (and_val2 C hAO2 h' hlen' hand' X).mpr
      have a1 := side_leaf C h' j' a ha.1.1 X ((hx a).mpr (Or.inr (Or.inr (Or.inl rfl))))
      have a2 := hw X ((hx w).mpr (Or.inr (Or.inr (Or.inr rfl))))
      rcases fin2_sub j' with ⟨e, e'⟩ | ⟨e, e'⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
    have hkv : gateVal n C k X = true := by
      apply (and_val2 C hAO2 k hlen hand X).mpr
      have a1 := side_leaf C k j s hs.1.1 X ((hx s).mpr (Or.inr (Or.inl rfl)))
      have a2 : val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true :=
        orStep_up (n := n) (by simp) hr hhv
      rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
      · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
    have hF : graphFun G ∅ X = true := hcl X ((hx u).mpr (Or.inl rfl)) hkv
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hF
    obtain ⟨y, z, hyz, hy, hz⟩ := hF
    have hus : ¬ G.Adj u s := hs.1.2
    have hws : ¬ G.Adj w s := hs.2
    have hwa : ¬ G.Adj w a := ha.1.2
    have hua : ¬ G.Adj u a := ha.2
    rcases (hx y).mp hy with e1 | e1 | e1 | e1 <;>
      rcases (hx z).mp hz with e2 | e2 | e2 | e2 <;> rw [e1, e2] at hyz
    all_goals first
      | exact (G.irrefl hyz).elim
      | exact hyz
      | exact hyz.symm
      | exact absurd hyz hus
      | exact absurd hyz.symm hus
      | exact absurd hyz hws
      | exact absurd hyz.symm hws
      | exact absurd hyz hwa
      | exact absurd hyz.symm hwa
      | exact absurd hyz hua
      | exact absurd hyz.symm hua
      | exact absurd hyz huw
      | exact absurd hyz.symm huw
  rcases biclique_star G h4 _ _ hall with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

def Slot3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ gc ∈ slots C, G.Adj u v ∧ ZWp G C K gc.2 v ∧
    (∃ a b : Fin n, ∀ y, ZWp G C K gc.2 y → y = a ∨ y = b) ∧
    (∃ w1 w2 w3 : Fin n, w1 ≠ w2 ∧ w1 ≠ w3 ∧ w2 ≠ w3 ∧ ZWp G C K (n + gc.1) w1 ∧
      ZWp G C K (n + gc.1) w2 ∧ ZWp G C K (n + gc.1) w3) ∧
    ∃ (k : ℕ) (j : Fin 2), k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      Relation.ReflTransGen (OrStep n C)
        (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) (n + gc.1) ∧
      Cl G C u (n + k) ∧
      K < ((PEqualNP.TopForm.side (n := n) C k j).filter (fun y => ¬ G.Adj u y)).card

lemma pick3 (A1 A2 A3 G1 G2 G3 B1 B2 B3 N1 N2 N3 : Prop)
    (h1 : A1 ∨ G1 ∨ B1) (h2 : A2 ∨ G2 ∨ B2) (h3 : A3 ∨ G3 ∨ B3)
    (b12 : ¬ (B1 ∧ B2)) (b13 : ¬ (B1 ∧ B3)) (b23 : ¬ (B2 ∧ B3))
    (n12 : N1 ∨ N2) (n13 : N1 ∨ N3) (n23 : N2 ∨ N3) :
    G1 ∨ G2 ∨ G3 ∨ (A1 ∧ N1) ∨ (A2 ∧ N2) ∨ (A3 ∧ N3) := by
  rcases h1 with a1 | g1 | b1
  · rcases h2 with a2 | g2 | b2
    · rcases n12 with m1 | m2
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, m1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a2, m2⟩))))
    · exact Or.inr (Or.inl g2)
    · rcases h3 with a3 | g3 | b3
      · rcases n13 with m1 | m3
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, m1⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a3, m3⟩))))
      · exact Or.inr (Or.inr (Or.inl g3))
      · exact (b23 ⟨b2, b3⟩).elim
  · exact Or.inl g1
  · rcases h2 with a2 | g2 | b2
    · rcases h3 with a3 | g3 | b3
      · rcases n23 with m2 | m3
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a2, m2⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a3, m3⟩))))
      · exact Or.inr (Or.inr (Or.inl g3))
      · exact (b13 ⟨b1, b3⟩).elim
    · exact Or.inr (Or.inl g2)
    · exact (b12 ⟨b1, b2⟩).elim

open PEqualNP.TopForm in
lemma slot3_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) (hK : 3 ≤ K) :
    Bnd (Slot3 G C K) (12 * (2 * C.gates.length)) := by
  classical
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  unfold Slot3
  apply obj_count (slots C) 12
  intro gc _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  obtain ⟨_, _, ⟨a, b, hab⟩, ⟨w1, w2, w3, h12, h13, h23,
    ⟨g1, r1, l1, o1, j1, f1, d1⟩, ⟨g2, r2, l2, o2, j2, f2, d2⟩,
    ⟨g3, r3, l3, o3, j3, f3, d3⟩⟩, _⟩ := hP zv0 hzv0
  have hM : ∀ v : Fin n, ∃ M : Finset (Fin n), M.card ≤ 6 ∧
      ∀ zv ∈ P, zv.2 = v → zv.1 ∈ M := by
    intro v
    refine ⟨(Finset.univ.filter (fun x => w1 ≠ v ∧ G.Adj x v ∧ G.Adj x w1)) ∪
      ((Finset.univ.filter (fun x => w2 ≠ v ∧ G.Adj x v ∧ G.Adj x w2)) ∪
      ((Finset.univ.filter (fun x => w3 ≠ v ∧ G.Adj x v ∧ G.Adj x w3)) ∪
      ((Finset.univ.filter (fun x => (((side (n := n) C g1 j1).filter
        (fun y => ¬ G.Adj w1 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
      ((Finset.univ.filter (fun x => (((side (n := n) C g2 j2).filter
        (fun y => ¬ G.Adj w2 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
      (Finset.univ.filter (fun x => (((side (n := n) C g3 j3).filter
        (fun y => ¬ G.Adj w3 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)))))), ?_, ?_⟩
    · have c1 := cnf_card G h4 v w1
      have c2 := cnf_card G h4 v w2
      have c3 := cnf_card G h4 v w3
      have c4 := z5_card G h4 ((side (n := n) C g1 j1).filter (fun y => ¬ G.Adj w1 y))
        (by omega)
      have c5 := z5_card G h4 ((side (n := n) C g2 j2).filter (fun y => ¬ G.Adj w2 y))
        (by omega)
      have c6 := z5_card G h4 ((side (n := n) C g3 j3).filter (fun y => ¬ G.Adj w3 y))
        (by omega)
      have u1 := Finset.card_union_le
        (Finset.univ.filter (fun x => w1 ≠ v ∧ G.Adj x v ∧ G.Adj x w1))
        ((Finset.univ.filter (fun x => w2 ≠ v ∧ G.Adj x v ∧ G.Adj x w2)) ∪
        ((Finset.univ.filter (fun x => w3 ≠ v ∧ G.Adj x v ∧ G.Adj x w3)) ∪
        ((Finset.univ.filter (fun x => (((side (n := n) C g1 j1).filter
          (fun y => ¬ G.Adj w1 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        ((Finset.univ.filter (fun x => (((side (n := n) C g2 j2).filter
          (fun y => ¬ G.Adj w2 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun x => (((side (n := n) C g3 j3).filter
          (fun y => ¬ G.Adj w3 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1))))))
      have u2 := Finset.card_union_le
        (Finset.univ.filter (fun x => w2 ≠ v ∧ G.Adj x v ∧ G.Adj x w2))
        ((Finset.univ.filter (fun x => w3 ≠ v ∧ G.Adj x v ∧ G.Adj x w3)) ∪
        ((Finset.univ.filter (fun x => (((side (n := n) C g1 j1).filter
          (fun y => ¬ G.Adj w1 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        ((Finset.univ.filter (fun x => (((side (n := n) C g2 j2).filter
          (fun y => ¬ G.Adj w2 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun x => (((side (n := n) C g3 j3).filter
          (fun y => ¬ G.Adj w3 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)))))
      have u3 := Finset.card_union_le
        (Finset.univ.filter (fun x => w3 ≠ v ∧ G.Adj x v ∧ G.Adj x w3))
        ((Finset.univ.filter (fun x => (((side (n := n) C g1 j1).filter
          (fun y => ¬ G.Adj w1 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        ((Finset.univ.filter (fun x => (((side (n := n) C g2 j2).filter
          (fun y => ¬ G.Adj w2 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun x => (((side (n := n) C g3 j3).filter
          (fun y => ¬ G.Adj w3 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1))))
      have u4 := Finset.card_union_le
        (Finset.univ.filter (fun x => (((side (n := n) C g1 j1).filter
          (fun y => ¬ G.Adj w1 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1))
        ((Finset.univ.filter (fun x => (((side (n := n) C g2 j2).filter
          (fun y => ¬ G.Adj w2 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun x => (((side (n := n) C g3 j3).filter
          (fun y => ¬ G.Adj w3 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1)))
      have u5 := Finset.card_union_le
        (Finset.univ.filter (fun x => (((side (n := n) C g2 j2).filter
          (fun y => ¬ G.Adj w2 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1))
        (Finset.univ.filter (fun x => (((side (n := n) C g3 j3).filter
          (fun y => ¬ G.Adj w3 y)).filter (fun d => ¬ G.Adj x d)).card ≤ 1))
      omega
    · intro zv hzv hv
      obtain ⟨hadj, _, _, _, k, j, hlen, hand, hrq, hcl, hD3⟩ := hP zv hzv
      rw [hv] at hadj
      have t1 := s3_test G C h4 hAO2 k j hlen hand zv.1 hcl g1 (hrq.trans r1) l1 o1 j1 w1 f1
      have t2 := s3_test G C h4 hAO2 k j hlen hand zv.1 hcl g2 (hrq.trans r2) l2 o2 j2 w2 f2
      have t3 := s3_test G C h4 hAO2 k j hlen hand zv.1 hcl g3 (hrq.trans r3) l3 o3 j3 w3 f3
      have hD4 : 4 ≤ ((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).card := by omega
      have b12 : ¬ ((((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).filter
          (fun d => ¬ G.Adj w1 d)).card ≤ 1 ∧
          (((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).filter
          (fun d => ¬ G.Adj w2 d)).card ≤ 1) :=
        fun hh => h12 (z5_unique G h4 _ hD4 w1 w2 hh.1 hh.2)
      have b13 : ¬ ((((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).filter
          (fun d => ¬ G.Adj w1 d)).card ≤ 1 ∧
          (((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).filter
          (fun d => ¬ G.Adj w3 d)).card ≤ 1) :=
        fun hh => h13 (z5_unique G h4 _ hD4 w1 w3 hh.1 hh.2)
      have b23 : ¬ ((((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).filter
          (fun d => ¬ G.Adj w2 d)).card ≤ 1 ∧
          (((side (n := n) C k j).filter (fun y => ¬ G.Adj zv.1 y)).filter
          (fun d => ¬ G.Adj w3 d)).card ≤ 1) :=
        fun hh => h23 (z5_unique G h4 _ hD4 w2 w3 hh.1 hh.2)
      have n12 : w1 ≠ v ∨ w2 ≠ v := by
        by_contra hc
        simp only [not_or, not_not] at hc
        exact h12 (hc.1.trans hc.2.symm)
      have n13 : w1 ≠ v ∨ w3 ≠ v := by
        by_contra hc
        simp only [not_or, not_not] at hc
        exact h13 (hc.1.trans hc.2.symm)
      have n23 : w2 ≠ v ∨ w3 ≠ v := by
        by_contra hc
        simp only [not_or, not_not] at hc
        exact h23 (hc.1.trans hc.2.symm)
      have hp := pick3 _ _ _ _ _ _ _ _ _ _ _ _ t1 t2 t3 b12 b13 b23 n12 n13 n23
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with g | g | g | ⟨a1, m1⟩ | ⟨a2, m2⟩ | ⟨a3, m3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl g)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl g))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr g))))
      · exact Or.inl ⟨m1, hadj, a1⟩
      · exact Or.inr (Or.inl ⟨m2, hadj, a2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨m3, hadj, a3⟩))
  have hmaps : ∀ zv ∈ P, zv.2 ∈ ({a, b} : Finset (Fin n)) := by
    intro zv hzv
    obtain ⟨_, hz, _⟩ := hP zv hzv
    rcases hab zv.2 hz with e | e
    · rw [e]; exact Finset.mem_insert_self _ _
    · rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfib : ∀ v ∈ ({a, b} : Finset (Fin n)), (P.filter (fun zv => zv.2 = v)).card ≤ 6 := by
    intro v _
    obtain ⟨M, hMc, hMm⟩ := hM v
    refine le_trans (Finset.card_le_card_of_injOn (f := Prod.fst) (t := M) ?_ ?_) hMc
    · intro zv hzv
      have hzv' := Finset.mem_filter.mp (Finset.mem_coe.mp hzv)
      exact Finset.mem_coe.mpr (hMm zv hzv'.1 hzv'.2)
    · intro zv hzv zv' hzv' heq
      have a1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hzv)).2
      have a2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hzv')).2
      exact Prod.ext heq (a1.trans a2.symm)
  have hmain := Finset.card_le_mul_card_image_of_maps_to (f := Prod.snd)
    (t := ({a, b} : Finset (Fin n))) hmaps 6 hfib
  have hc2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  calc P.card ≤ 6 * ({a, b} : Finset (Fin n)).card := hmain
    _ ≤ 6 * 2 := Nat.mul_le_mul_left _ hc2
    _ = 12 := by norm_num

def MidFew {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ (∃ W : Finset (Fin n), W.card ≤ 3 ∧ ∀ w, Cl G C w (n + kj.1) → w ∈ W) ∧
    Cl G C u (n + kj.1) ∧
    ZWp G C K (PEqualNP.TopForm.opnd C kj.1 ((1 : Fin 2) - kj.2)) v ∧
    ∃ a b : Fin n, ∀ y,
      ZWp G C K (PEqualNP.TopForm.opnd C kj.1 ((1 : Fin 2) - kj.2)) y → y = a ∨ y = b

lemma midfew_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ) :
    Bnd (MidFew G C K) (6 * (2 * C.gates.length)) := by
  classical
  have hc := prod_card C.gates.length
  unfold MidFew
  refine bnd_le (le_of_eq (by rw [hc])) (obj_count _ 6 _ ?_)
  intro kj _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  obtain ⟨_, ⟨W, hW, hWall⟩, _, _, a, b, hab⟩ := hP zv0 hzv0
  have hsub : P ⊆ W ×ˢ ({a, b} : Finset (Fin n)) := by
    intro zv hzv
    obtain ⟨_, _, hcl, hz, _⟩ := hP zv hzv
    refine Finset.mem_product.mpr ⟨hWall zv.1 hcl, ?_⟩
    rcases hab zv.2 hz with e | e
    · rw [e]; exact Finset.mem_insert_self _ _
    · rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_product] at hc1
  have hc2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  calc P.card ≤ W.card * ({a, b} : Finset (Fin n)).card := hc1
    _ ≤ 3 * 2 := Nat.mul_le_mul hW hc2
    _ = 6 := by norm_num

lemma two_of_notbig {α : Type} (Z : α → Prop) (v : α)
    (h : ¬ ∃ w1 w2 : α, w1 ≠ v ∧ w2 ≠ v ∧ w1 ≠ w2 ∧ Z w1 ∧ Z w2) :
    ∃ a b : α, ∀ y, Z y → y = a ∨ y = b := by
  classical
  by_cases hx : ∃ y, y ≠ v ∧ Z y
  · obtain ⟨y0, hy0, hz0⟩ := hx
    refine ⟨v, y0, fun y hy => ?_⟩
    by_cases e : y = v
    · exact Or.inl e
    · right
      by_contra hne
      exact h ⟨y0, y, hy0, e, fun e' => hne e'.symm, hz0, hy⟩
  · refine ⟨v, v, fun y hy => ?_⟩
    left
    by_contra e
    exact hx ⟨y, e, hy⟩

def PayN2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  Slot3 G C K u v ∨ MidFew G C K u v

def Pay8 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay7 G C K a b ∨ PayN2 G C K a b ∨ PayN2 G C K b a

open PEqualNP.TopForm in
lemma pay8_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay8 G C 5) (2716 * C.gates.length) := by
  have q : Bnd (PayN2 G C 5) (12 * (2 * C.gates.length) + 6 * (2 * C.gates.length)) :=
    bnd_or (slot3_bnd G C h4 hAO2 h2 5 (by norm_num)) (midfew_bnd G C 5)
  have hb := bnd_or (pay7_bnd G C h4 hAO2 h2) (bnd_or q (bnd_swap q))
  unfold Pay8
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma shape31_IIc3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 2 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (ju : Fin 2) (hu1 : u ∈ side (n := n) C h ju)
    (hv2 : v ∈ side (n := n) C h ((1 : Fin 2) - ju)) :
    Pay8 G C K u v ∨
      ((Lw n C (opnd C h ju)).card ≤ 2 ∧ (Lw n C (opnd C k j)).card ≤ 2 ∧
        K < ((side (n := n) C h ((1 : Fin 2) - ju)).filter (fun y => ¬ G.Adj u y)).card ∧
        (∃ b ∈ side (n := n) C h ((1 : Fin 2) - ju), b ≠ v ∧ G.Adj u b) ∧ ¬ C1 G C k v) := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hfu : Fires n C (opnd C t i) u := fires_side C t i u hside
  have hrk := (orReaches_reach k _ hork).1
  have hrh := (orReaches_reach h _ horh).1
  have hcl : Cl G C u (n + k) := cl_mono G C (cl_top G C hAO2 t ht i u hfu) hrk
  have hvP : Fires n C (opnd C k j) v := fires_side C k j v hv3
  have hv2f : Fires n C (opnd C h ((1 : Fin 2) - ju)) v := fires_side C h _ v hv2
  have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
  have huq : ∀ y' ∈ Lw n C u.val, G.Adj v y' → y' = u :=
    fun y' hy' _ => (fires_input C u y').mp (mem_Lw.mp hy')
  rcases shape31_IIc2 G C h4 hAO2 K (by omega) t ht i u v huv hside k hk hork j hv3 h hh horh
    ju hu1 hv2 with h' | ⟨cA, cP, hheavy, hs⟩ | ⟨hfew, hS3, _, hS1, _, cB⟩
  · exact Or.inl (Or.inl h')
  · by_cases hc1 : C1 G C k v
    · left
      have hvL : v ∈ Lw n C (opnd C k j) := mem_Lw.mpr hvP
      have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False := Or.inl huq
      rcases lo_or_hi _ cP v hvL with hlo | hhi
      · have hsc : SC G C 1 (AnLo C j) k v := ⟨⟨cP, hvL, hlo⟩, hand, hc1⟩
        rcases centred_pay G C hAO2 1 _ (sc_ok G C 1 (AnLo C j) (anlo_fun C j)) t ht i u v huv
          u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
        · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
          · rw [e] at h2
            exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl h2))))
          · rw [e] at h2
            exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h2))))))
        · exact h2.elim
        · exact Or.inl (Or.inl (payd_pay6 G C K u v
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h2))))))))
      · have hsc : SC G C 1 (AnHi C j) k v := ⟨⟨cP, hvL, hhi⟩, hand, hc1⟩
        rcases centred_pay G C hAO2 1 _ (sc_ok G C 1 (AnHi C j) (anhi_fun C j)) t ht i u v huv
          u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
        · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
          · rw [e] at h2
            exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr h2))))
          · rw [e] at h2
            exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h2))))))
        · exact h2.elim
        · exact Or.inl (Or.inl (payd_pay6 G C K u v
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C (by omega) h2))))))))
    · exact Or.inr ⟨cA, cP, hheavy, hs, hc1⟩
  · left
    have hWv : WHL G C K h v := ⟨hlenh, handh, ju, hv2f, hS1⟩
    have hin : ∀ w, ZWp G C K (n + h) w → w ∈ Lw n C (opnd C h ((1 : Fin 2) - ju)) := by
      rintro w ⟨h'', hr'', _, _, j'', hf'', hd''⟩
      have e : h'' = h := by
        have := and_reach_self C h handh _ hr''
        omega
      rw [e] at hf'' hd''
      by_cases hj : j'' = ju
      · rw [hj] at hf''; exact mem_Lw.mpr hf''
      · exfalso
        have e2 := fin2_ne ju j'' hj
        have e3 : j'' = (1 : Fin 2) - ju := by rw [e2, fin2_ss]
        rw [e3] at hd''
        have c1 : ((side (n := n) C h ((1 : Fin 2) - ju)).filter
            (fun y => ¬ G.Adj w y)).card ≤ 2 := by
          refine le_trans (Finset.card_le_card ?_) cB
          intro x hx
          exact mem_Lw.mpr (fires_side C h _ x (Finset.mem_filter.mp hx).1)
        omega
    have hτ : ¬ ∃ w1 w2 : Fin n, w1 ≠ v ∧ w2 ≠ v ∧ w1 ≠ w2 ∧ ZWp G C K (n + h) w1 ∧
        ZWp G C K (n + h) w2 := by
      rintro ⟨w1, w2, n1, n2, n12, z1, z2⟩
      have m1 := hin w1 z1
      have m2 := hin w2 z2
      have mv : v ∈ Lw n C (opnd C h ((1 : Fin 2) - ju)) := mem_Lw.mpr hv2f
      have h3 : ({v, w1, w2} : Finset (Fin n)).card = 3 :=
        Finset.card_eq_three.mpr ⟨v, w1, w2, Ne.symm n1, Ne.symm n2, n12, rfl⟩
      have hsub : ({v, w1, w2} : Finset (Fin n)) ⊆ Lw n C (opnd C h ((1 : Fin 2) - ju)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact mv
        · exact m1
        · exact m2
      have := Finset.card_le_card hsub
      omega
    by_cases hBig : ∃ w1 w2 : Fin n, w1 ≠ v ∧ w2 ≠ v ∧ w1 ≠ w2 ∧
        ZWp G C K (opnd C k ((1 : Fin 2) - j)) w1 ∧ ZWp G C K (opnd C k ((1 : Fin 2) - j)) w2
    · obtain ⟨g, c, hg, hin', hr1, hr2, hr3, hb1, hb2⟩ :=
        path_split C (fun r => ∃ w1 w2 : Fin n, w1 ≠ v ∧ w2 ≠ v ∧ w1 ≠ w2 ∧
          ZWp G C K r w1 ∧ ZWp G C K r w2) (n + h) hτ _ hrh hBig
      obtain ⟨w1, w2, n1, n2, n12, z1, z2⟩ := hb1
      refine Or.inr (Or.inl (Or.inl ⟨(g, c), slot_mem C hg hin', huv, ⟨h, hr3, hWv⟩,
        two_of_notbig _ v hb2, ⟨v, w1, w2, Ne.symm n1, Ne.symm n2, n12,
          ⟨h, hr2.trans hr3, hWv⟩, z1, z2⟩, k, j, hlen, hand, hr1, hcl, hS3⟩))
    · refine Or.inr (Or.inl (Or.inr ⟨(k, j), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hlen, Finset.mem_univ _⟩, huv, hfew, hcl, ⟨h, hrh, hWv⟩,
        two_of_notbig _ v hBig⟩))

def PayL4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : Fin 2) (u v : Fin n) : Prop :=
  PayC G C (SC G C 4 (AnLo C j)) u v ∨ PayC G C (SC G C 4 (AnHi C j)) u v

lemma payl4_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (j : Fin 2) :
    Bnd (PayL4 G C j) (24 * C.gates.length) := by
  have p1 := payc_bnd G C h4 h2 4 _ (sc_ok G C 4 (AnLo C j) (anlo_fun C j))
  have p2 := payc_bnd G C h4 h2 4 _ (sc_ok G C 4 (AnHi C j) (anhi_fun C j))
  have hb := bnd_or p1 p2
  unfold PayL4
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma s3v_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (k : ℕ) (j : Fin 2) (hlen : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) (v : Fin n) (hvP : Fires n C (opnd C k j) v)
    (x : Fin n) (hcl : Cl G C x (n + k)) (hxv : ¬ G.Adj x v)
    (g' : ℕ) (hr : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + g'))
    (hlen' : g' < C.gates.length) (hand' : (gateAt C g').op = GateOp.and)
    (j' : Fin 2) (w : Fin n) (hw : Fires n C (opnd C g' ((1 : Fin 2) - j')) w)
    (hxw : ¬ G.Adj x w) (hvw : ¬ G.Adj v w) :
    ∀ s ∈ ((side (n := n) C g' j').filter (fun y => ¬ G.Adj w y)).filter
      (fun d => ¬ G.Adj v d), G.Adj s x := by
  intro s hs
  rw [Finset.mem_filter, Finset.mem_filter] at hs
  obtain ⟨X, hx⟩ : ∃ X : Fin n → Bool,
      ∀ z : Fin n, X z = true ↔ (z = x ∨ z = v ∨ z = w ∨ z = s) :=
    ⟨fun z => decide (z = x ∨ z = v ∨ z = w ∨ z = s), fun z => by simp⟩
  have hhv : gateVal n C g' X = true := by
    apply (and_val2 C hAO2 g' hlen' hand' X).mpr
    have a1 := side_leaf C g' j' s hs.1.1 X ((hx s).mpr (Or.inr (Or.inr (Or.inr rfl))))
    have a2 := hw X ((hx w).mpr (Or.inr (Or.inr (Or.inl rfl))))
    rcases fin2_sub j' with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
  have hkv : gateVal n C k X = true := by
    apply (and_val2 C hAO2 k hlen hand X).mpr
    have a1 := hvP X ((hx v).mpr (Or.inr (Or.inl rfl)))
    have a2 : val C (List.ofFn X) (opnd C k ((1 : Fin 2) - j)) = true :=
      orStep_up (n := n) (by simp) hr hhv
    rcases fin2_sub j with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a1, a2⟩
    · rw [e] at a1; rw [e'] at a2; exact ⟨a2, a1⟩
  have hF : graphFun G ∅ X = true := hcl X ((hx x).mpr (Or.inl rfl)) hkv
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨y, z, hyz, hy, hz⟩ := hF
  have hws : ¬ G.Adj w s := hs.1.2
  have hvs : ¬ G.Adj v s := hs.2
  rcases (hx y).mp hy with e1 | e1 | e1 | e1 <;>
    rcases (hx z).mp hz with e2 | e2 | e2 | e2 <;> rw [e1, e2] at hyz
  all_goals first
    | exact (G.irrefl hyz).elim
    | exact hyz
    | exact hyz.symm
    | exact absurd hyz hxv
    | exact absurd hyz.symm hxv
    | exact absurd hyz hxw
    | exact absurd hyz.symm hxw
    | exact absurd hyz hvw
    | exact absurd hyz.symm hvw
    | exact absurd hyz hws
    | exact absurd hyz.symm hws
    | exact absurd hyz hvs
    | exact absurd hyz.symm hvs

open PEqualNP.TopForm in
lemma s3v_test {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (k : ℕ) (j : Fin 2) (hlen : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) (v : Fin n) (hvP : Fires n C (opnd C k j) v)
    (X5 : Finset (Fin n)) (hX5 : 5 ≤ X5.card)
    (hXc : ∀ x ∈ X5, Cl G C x (n + k) ∧ ¬ G.Adj x v)
    (ga : ℕ) (hra : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + ga))
    (la : ga < C.gates.length) (oa : (gateAt C ga).op = GateOp.and) (ja : Fin 2) (wa : Fin n)
    (hwa : Fires n C (opnd C ga ((1 : Fin 2) - ja)) wa)
    (gb : ℕ) (hrb : Relation.ReflTransGen (OrStep n C) (opnd C k ((1 : Fin 2) - j)) (n + gb))
    (lb : gb < C.gates.length) (ob : (gateAt C gb).op = GateOp.and) (jb : Fin 2) (wb : Fin n)
    (hwb : Fires n C (opnd C gb ((1 : Fin 2) - jb)) wb)
    (hne : wa ≠ wb) (hva : ¬ G.Adj v wa) (hvb : ¬ G.Adj v wb) :
    (((side (n := n) C ga ja).filter (fun y => ¬ G.Adj wa y)).filter
        (fun d => ¬ G.Adj v d)).card ≤ 1 ∨
      (((side (n := n) C gb jb).filter (fun y => ¬ G.Adj wb y)).filter
        (fun d => ¬ G.Adj v d)).card ≤ 1 := by
  classical
  by_cases ca : 1 < (X5.filter (fun x => ¬ G.Adj x wa)).card
  · left
    obtain ⟨x1, hx1, x2, hx2, h12⟩ := Finset.one_lt_card.mp ca
    rw [Finset.mem_filter] at hx1 hx2
    refine le_trans (Finset.card_le_card ?_) (cn_pair_card G h4 x1 x2 h12)
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      s3v_one G C hAO2 k j hlen hand v hvP x1 (hXc x1 hx1.1).1 (hXc x1 hx1.1).2 ga hra la oa
        ja wa hwa hx1.2 hva s hs,
      s3v_one G C hAO2 k j hlen hand v hvP x2 (hXc x2 hx2.1).1 (hXc x2 hx2.1).2 ga hra la oa
        ja wa hwa hx2.2 hva s hs⟩
  by_cases cb : 1 < (X5.filter (fun x => ¬ G.Adj x wb)).card
  · right
    obtain ⟨x1, hx1, x2, hx2, h12⟩ := Finset.one_lt_card.mp cb
    rw [Finset.mem_filter] at hx1 hx2
    refine le_trans (Finset.card_le_card ?_) (cn_pair_card G h4 x1 x2 h12)
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      s3v_one G C hAO2 k j hlen hand v hvP x1 (hXc x1 hx1.1).1 (hXc x1 hx1.1).2 gb hrb lb ob
        jb wb hwb hx1.2 hvb s hs,
      s3v_one G C hAO2 k j hlen hand v hvP x2 (hXc x2 hx2.1).1 (hXc x2 hx2.1).2 gb hrb lb ob
        jb wb hwb hx2.2 hvb s hs⟩
  exfalso
  have hsub : X5 ⊆ (X5.filter (fun x => ¬ G.Adj x wa)) ∪ ((X5.filter (fun x => ¬ G.Adj x wb)) ∪
      (Finset.univ.filter (fun x => G.Adj x wa ∧ G.Adj x wb))) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases a1 : G.Adj x wa
    · by_cases a2 : G.Adj x wb
      · exact Or.inr (Or.inr ⟨a1, a2⟩)
      · exact Or.inr (Or.inl ⟨hx, a2⟩)
    · exact Or.inl ⟨hx, a1⟩
  have c3 := cn_pair_card G h4 wa wb hne
  have u0 := Finset.card_le_card hsub
  have u1 := Finset.card_union_le (X5.filter (fun x => ¬ G.Adj x wa))
    ((X5.filter (fun x => ¬ G.Adj x wb)) ∪
      (Finset.univ.filter (fun x => G.Adj x wa ∧ G.Adj x wb)))
  have u2 := Finset.card_union_le (X5.filter (fun x => ¬ G.Adj x wb))
    (Finset.univ.filter (fun x => G.Adj x wa ∧ G.Adj x wb))
  omega

def Slot3v {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ gc ∈ slots C, G.Adj u v ∧ ZWp G C K gc.2 u ∧
    (∃ a b : Fin n, ∀ y, ZWp G C K gc.2 y → y = a ∨ y = b) ∧
    (∃ w1 w2 w3 : Fin n, w1 ≠ w2 ∧ w1 ≠ w3 ∧ w2 ≠ w3 ∧ ZWp G C K (n + gc.1) w1 ∧
      ZWp G C K (n + gc.1) w2 ∧ ZWp G C K (n + gc.1) w3) ∧
    ∃ (k : ℕ) (j : Fin 2), k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      Relation.ReflTransGen (OrStep n C)
        (PEqualNP.TopForm.opnd C k ((1 : Fin 2) - j)) (n + gc.1) ∧
      Fires n C (PEqualNP.TopForm.opnd C k j) v ∧
      ∃ X5 : Finset (Fin n), 5 ≤ X5.card ∧ ∀ x ∈ X5, Cl G C x (n + k) ∧ ¬ G.Adj x v

open PEqualNP.TopForm in
lemma slot3v_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (K : ℕ) (hK : 3 ≤ K) :
    Bnd (Slot3v G C K) (12 * (2 * C.gates.length)) := by
  classical
  refine bnd_le (Nat.mul_le_mul_left _ (slots_card C h2)) ?_
  unfold Slot3v
  apply obj_count (slots C) 12
  intro gc _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  obtain ⟨_, _, ⟨a, b, hab⟩, ⟨w1, w2, w3, h12, h13, h23,
    ⟨g1, r1, l1, o1, j1, f1, d1⟩, ⟨g2, r2, l2, o2, j2, f2, d2⟩,
    ⟨g3, r3, l3, o3, j3, f3, d3⟩⟩, _⟩ := hP zv0 hzv0
  have hM : ∀ u : Fin n, ∃ M : Finset (Fin n), M.card ≤ 6 ∧
      ∀ zv ∈ P, zv.1 = u → zv.2 ∈ M := by
    intro u
    refine ⟨(Finset.univ.filter (fun y => w1 ≠ u ∧ G.Adj y u ∧ G.Adj y w1)) ∪
      ((Finset.univ.filter (fun y => w2 ≠ u ∧ G.Adj y u ∧ G.Adj y w2)) ∪
      ((Finset.univ.filter (fun y => w3 ≠ u ∧ G.Adj y u ∧ G.Adj y w3)) ∪
      ((Finset.univ.filter (fun y => (((side (n := n) C g1 j1).filter
        (fun z => ¬ G.Adj w1 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
      ((Finset.univ.filter (fun y => (((side (n := n) C g2 j2).filter
        (fun z => ¬ G.Adj w2 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
      (Finset.univ.filter (fun y => (((side (n := n) C g3 j3).filter
        (fun z => ¬ G.Adj w3 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)))))), ?_, ?_⟩
    · have c1 := cnf_card G h4 u w1
      have c2 := cnf_card G h4 u w2
      have c3 := cnf_card G h4 u w3
      have c4 := z5_card G h4 ((side (n := n) C g1 j1).filter (fun z => ¬ G.Adj w1 z))
        (by omega)
      have c5 := z5_card G h4 ((side (n := n) C g2 j2).filter (fun z => ¬ G.Adj w2 z))
        (by omega)
      have c6 := z5_card G h4 ((side (n := n) C g3 j3).filter (fun z => ¬ G.Adj w3 z))
        (by omega)
      have u1 := Finset.card_union_le
        (Finset.univ.filter (fun y => w1 ≠ u ∧ G.Adj y u ∧ G.Adj y w1))
        ((Finset.univ.filter (fun y => w2 ≠ u ∧ G.Adj y u ∧ G.Adj y w2)) ∪
        ((Finset.univ.filter (fun y => w3 ≠ u ∧ G.Adj y u ∧ G.Adj y w3)) ∪
        ((Finset.univ.filter (fun y => (((side (n := n) C g1 j1).filter
          (fun z => ¬ G.Adj w1 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        ((Finset.univ.filter (fun y => (((side (n := n) C g2 j2).filter
          (fun z => ¬ G.Adj w2 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun y => (((side (n := n) C g3 j3).filter
          (fun z => ¬ G.Adj w3 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1))))))
      have u2 := Finset.card_union_le
        (Finset.univ.filter (fun y => w2 ≠ u ∧ G.Adj y u ∧ G.Adj y w2))
        ((Finset.univ.filter (fun y => w3 ≠ u ∧ G.Adj y u ∧ G.Adj y w3)) ∪
        ((Finset.univ.filter (fun y => (((side (n := n) C g1 j1).filter
          (fun z => ¬ G.Adj w1 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        ((Finset.univ.filter (fun y => (((side (n := n) C g2 j2).filter
          (fun z => ¬ G.Adj w2 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun y => (((side (n := n) C g3 j3).filter
          (fun z => ¬ G.Adj w3 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)))))
      have u3 := Finset.card_union_le
        (Finset.univ.filter (fun y => w3 ≠ u ∧ G.Adj y u ∧ G.Adj y w3))
        ((Finset.univ.filter (fun y => (((side (n := n) C g1 j1).filter
          (fun z => ¬ G.Adj w1 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        ((Finset.univ.filter (fun y => (((side (n := n) C g2 j2).filter
          (fun z => ¬ G.Adj w2 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun y => (((side (n := n) C g3 j3).filter
          (fun z => ¬ G.Adj w3 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1))))
      have u4 := Finset.card_union_le
        (Finset.univ.filter (fun y => (((side (n := n) C g1 j1).filter
          (fun z => ¬ G.Adj w1 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1))
        ((Finset.univ.filter (fun y => (((side (n := n) C g2 j2).filter
          (fun z => ¬ G.Adj w2 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)) ∪
        (Finset.univ.filter (fun y => (((side (n := n) C g3 j3).filter
          (fun z => ¬ G.Adj w3 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1)))
      have u5 := Finset.card_union_le
        (Finset.univ.filter (fun y => (((side (n := n) C g2 j2).filter
          (fun z => ¬ G.Adj w2 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1))
        (Finset.univ.filter (fun y => (((side (n := n) C g3 j3).filter
          (fun z => ¬ G.Adj w3 z)).filter (fun d => ¬ G.Adj y d)).card ≤ 1))
      omega
    · intro zv hzv hu
      obtain ⟨hadj, _, _, _, k, j, hlen, hand, hrq, hvP, X5, hX5, hXc⟩ := hP zv hzv
      rw [hu] at hadj
      have pick : ∀ (ga : ℕ) (ja : Fin 2) (wa : Fin n) (gb : ℕ) (jb : Fin 2) (wb : Fin n),
          Relation.ReflTransGen (OrStep n C) (n + gc.1) (n + ga) → ga < C.gates.length →
          (gateAt C ga).op = GateOp.and → Fires n C (opnd C ga ((1 : Fin 2) - ja)) wa →
          Relation.ReflTransGen (OrStep n C) (n + gc.1) (n + gb) → gb < C.gates.length →
          (gateAt C gb).op = GateOp.and → Fires n C (opnd C gb ((1 : Fin 2) - jb)) wb →
          wa ≠ wb →
          G.Adj zv.2 wa ∨ G.Adj zv.2 wb ∨
            (((side (n := n) C ga ja).filter (fun z => ¬ G.Adj wa z)).filter
              (fun d => ¬ G.Adj zv.2 d)).card ≤ 1 ∨
            (((side (n := n) C gb jb).filter (fun z => ¬ G.Adj wb z)).filter
              (fun d => ¬ G.Adj zv.2 d)).card ≤ 1 := by
        intro ga ja wa gb jb wb ra la oa fa rb lb ob fb hne
        by_cases a1 : G.Adj zv.2 wa
        · exact Or.inl a1
        by_cases a2 : G.Adj zv.2 wb
        · exact Or.inr (Or.inl a2)
        exact Or.inr (Or.inr (s3v_test G C h4 hAO2 k j hlen hand zv.2 hvP X5 hX5 hXc
          ga (hrq.trans ra) la oa ja wa fa gb (hrq.trans rb) lb ob jb wb fb hne a1 a2))
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases n1 : w1 = u
      · have n2 : w2 ≠ u := fun e => h12 (n1.trans e.symm)
        have n3 : w3 ≠ u := fun e => h13 (n1.trans e.symm)
        rcases pick g2 j2 w2 g3 j3 w3 r2 l2 o2 f2 r3 l3 o3 f3 h23 with p | p | p | p
        · exact Or.inr (Or.inl ⟨n2, hadj.symm, p⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨n3, hadj.symm, p⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl p))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr p))))
      · by_cases n2 : w2 = u
        · have n3 : w3 ≠ u := fun e => h23 (n2.trans e.symm)
          rcases pick g1 j1 w1 g3 j3 w3 r1 l1 o1 f1 r3 l3 o3 f3 h13 with p | p | p | p
          · exact Or.inl ⟨n1, hadj.symm, p⟩
          · exact Or.inr (Or.inr (Or.inl ⟨n3, hadj.symm, p⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl p)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr p))))
        · rcases pick g1 j1 w1 g2 j2 w2 r1 l1 o1 f1 r2 l2 o2 f2 h12 with p | p | p | p
          · exact Or.inl ⟨n1, hadj.symm, p⟩
          · exact Or.inr (Or.inl ⟨n2, hadj.symm, p⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inl p)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl p))))
  have hmaps : ∀ zv ∈ P, zv.1 ∈ ({a, b} : Finset (Fin n)) := by
    intro zv hzv
    obtain ⟨_, hz, _⟩ := hP zv hzv
    rcases hab zv.1 hz with e | e
    · rw [e]; exact Finset.mem_insert_self _ _
    · rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfib : ∀ u ∈ ({a, b} : Finset (Fin n)), (P.filter (fun zv => zv.1 = u)).card ≤ 6 := by
    intro u _
    obtain ⟨M, hMc, hMm⟩ := hM u
    refine le_trans (Finset.card_le_card_of_injOn (f := Prod.snd) (t := M) ?_ ?_) hMc
    · intro zv hzv
      have hzv' := Finset.mem_filter.mp (Finset.mem_coe.mp hzv)
      exact Finset.mem_coe.mpr (hMm zv hzv'.1 hzv'.2)
    · intro zv hzv zv' hzv' heq
      have a1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hzv)).2
      have a2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hzv')).2
      exact Prod.ext (a1.trans a2.symm) heq
  have hmain := Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst)
    (t := ({a, b} : Finset (Fin n))) hmaps 6 hfib
  have hc2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  calc P.card ≤ 6 * ({a, b} : Finset (Fin n)).card := hmain
    _ ≤ 6 * 2 := Nat.mul_le_mul_left _ hc2
    _ = 12 := by norm_num

def MidThin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  ∃ kj ∈ (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))),
    G.Adj u v ∧ (Lw n C (PEqualNP.TopForm.opnd C kj.1 kj.2)).card ≤ 2 ∧
    v ∈ Lw n C (PEqualNP.TopForm.opnd C kj.1 kj.2) ∧
    ZWp G C K (PEqualNP.TopForm.opnd C kj.1 ((1 : Fin 2) - kj.2)) u ∧
    ∃ a b : Fin n, ∀ y,
      ZWp G C K (PEqualNP.TopForm.opnd C kj.1 ((1 : Fin 2) - kj.2)) y → y = a ∨ y = b

lemma midthin_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (K : ℕ) : Bnd (MidThin G C K) (4 * (2 * C.gates.length)) := by
  classical
  have hc := prod_card C.gates.length
  unfold MidThin
  refine bnd_le (le_of_eq (by rw [hc])) (obj_count _ 4 _ ?_)
  intro kj _ P hP
  rcases P.eq_empty_or_nonempty with h0 | ⟨zv0, hzv0⟩
  · rw [h0]; simp
  obtain ⟨_, hcard, _, _, a, b, hab⟩ := hP zv0 hzv0
  have hsub : P ⊆ ({a, b} : Finset (Fin n)) ×ˢ
      (Lw n C (PEqualNP.TopForm.opnd C kj.1 kj.2)) := by
    intro zv hzv
    obtain ⟨_, _, hv, hz, _⟩ := hP zv hzv
    refine Finset.mem_product.mpr ⟨?_, hv⟩
    rcases hab zv.1 hz with e | e
    · rw [e]; exact Finset.mem_insert_self _ _
    · rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_product] at hc1
  have hc2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  calc P.card ≤ ({a, b} : Finset (Fin n)).card *
        (Lw n C (PEqualNP.TopForm.opnd C kj.1 kj.2)).card := hc1
    _ ≤ 2 * 2 := Nat.mul_le_mul hc2 hcard
    _ = 4 := by norm_num

def PayN3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (u v : Fin n) : Prop :=
  PayL4 G C 0 u v ∨ PayL4 G C 1 u v ∨ Slot3v G C K u v ∨ MidThin G C K u v

def Pay9 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : ℕ)
    (a b : Fin n) : Prop :=
  Pay8 G C K a b ∨ PayN3 G C K a b ∨ PayN3 G C K b a

open PEqualNP.TopForm in
lemma pay9_bnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Bnd (Pay9 G C 5) (2876 * C.gates.length) := by
  have q : Bnd (PayN3 G C 5) (24 * C.gates.length + (24 * C.gates.length +
      (12 * (2 * C.gates.length) + 4 * (2 * C.gates.length)))) :=
    bnd_or (payl4_bnd G C h4 h2 0) (bnd_or (payl4_bnd G C h4 h2 1)
      (bnd_or (slot3v_bnd G C h4 hAO2 h2 5 (by norm_num)) (midthin_bnd G C 5)))
  have hb := bnd_or (pay8_bnd G C h4 hAO2 h2) (bnd_or q (bnd_swap q))
  unfold Pay9
  refine bnd_le ?_ hb
  omega

open PEqualNP.TopForm in
lemma shape31_IIc4 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 4 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hv3 : v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (ju : Fin 2) (hu1 : u ∈ side (n := n) C h ju)
    (hv2 : v ∈ side (n := n) C h ((1 : Fin 2) - ju)) :
    Pay9 G C K u v := by
  classical
  obtain ⟨hlen, hand⟩ := junk_lt G C k hk
  obtain ⟨hlenh, handh⟩ := junk_lt G C h hh
  have hrk := (orReaches_reach k _ hork).1
  have hrh := (orReaches_reach h _ horh).1
  have hvP : Fires n C (opnd C k j) v := fires_side C k j v hv3
  have hu1f : Fires n C (opnd C h ju) u := fires_side C h ju u hu1
  have huu : u ∈ Lw n C u.val := mem_Lw.mpr ((fires_input C u u).mpr rfl)
  have huq : ∀ y' ∈ Lw n C u.val, G.Adj v y' → y' = u :=
    fun y' hy' _ => (fires_input C u y').mp (mem_Lw.mp hy')
  rcases shape31_IIc3 G C h4 hAO2 K (by omega) t ht i u v huv hside k hk hork j hv3 h hh horh
    ju hu1 hv2 with h' | ⟨cA, cP, hheavy, _, _⟩
  · exact Or.inl h'
  have hvL : v ∈ Lw n C (opnd C k j) := mem_Lw.mpr hvP
  by_cases hfew : ∃ M : Finset (Fin n), M.card ≤ 4 ∧
      ∀ w : Fin n, Cl G C w (n + k) → G.Adj w v ∨ w ∈ M
  · have hτu : (∀ y ∈ Lw n C u.val, G.Adj v y → y = u) ∨ False := Or.inl huq
    rcases lo_or_hi _ cP v hvL with hlo | hhi
    · have hsc : SC G C 4 (AnLo C j) k v := ⟨⟨cP, hvL, hlo⟩, hand, hfew⟩
      rcases centred_pay G C hAO2 4 _ (sc_ok G C 4 (AnLo C j) (anlo_fun C j)) t ht i u v huv
        u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
      · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
        · rw [e] at h2
          exact Or.inr (Or.inl (Or.inl (Or.inl h2)))
        · rw [e] at h2
          exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl h2))))
      · exact h2.elim
      · exact Or.inl (Or.inl (Or.inl (payd_pay6 G C K u v
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK h2)))))))))
    · have hsc : SC G C 4 (AnHi C j) k v := ⟨⟨cP, hvL, hhi⟩, hand, hfew⟩
      rcases centred_pay G C hAO2 4 _ (sc_ok G C 4 (AnHi C j) (anhi_fun C j)) t ht i u v huv
        u.val (mem_orIn_reach u hside) huu hτu k hrk hsc with h2 | h2 | h2
      · rcases fin2_sub j with ⟨e, _⟩ | ⟨e, _⟩
        · rw [e] at h2
          exact Or.inr (Or.inl (Or.inl (Or.inr h2)))
        · rw [e] at h2
          exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr h2))))
      · exact h2.elim
      · exact Or.inl (Or.inl (Or.inl (payd_pay6 G C K u v
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cdl_mono G C hK h2)))))))))
  · have hX5 : 5 ≤ (Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v)).card := by
      by_contra hlt
      refine hfew ⟨Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v), by omega, ?_⟩
      intro w hw
      by_cases hwv : G.Adj w v
      · exact Or.inl hwv
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hwv⟩)
    have hXc : ∀ x ∈ Finset.univ.filter (fun w => Cl G C w (n + k) ∧ ¬ G.Adj w v),
        Cl G C x (n + k) ∧ ¬ G.Adj x v := fun x hx => (Finset.mem_filter.mp hx).2
    have hWu : WHL G C K h u := by
      refine ⟨hlenh, handh, (1 : Fin 2) - ju, ?_, hheavy⟩
      rw [fin2_ss]
      exact hu1f
    have hin : ∀ w, ZWp G C K (n + h) w → w ∈ Lw n C (opnd C h ju) := by
      rintro w ⟨h'', hr'', _, _, j'', hf'', hd''⟩
      have e : h'' = h := by
        have := and_reach_self C h handh _ hr''
        omega
      rw [e] at hf'' hd''
      by_cases hj : j'' = ju
      · exfalso
        rw [hj] at hd''
        have c1 : ((side (n := n) C h ju).filter (fun y => ¬ G.Adj w y)).card ≤ 2 := by
          refine le_trans (Finset.card_le_card ?_) cA
          intro x hx
          exact mem_Lw.mpr (fires_side C h _ x (Finset.mem_filter.mp hx).1)
        omega
      · have e2 := fin2_ne ju j'' hj
        rw [← e2] at hf''
        exact mem_Lw.mpr hf''
    have hτ : ¬ ∃ w1 w2 : Fin n, w1 ≠ u ∧ w2 ≠ u ∧ w1 ≠ w2 ∧ ZWp G C K (n + h) w1 ∧
        ZWp G C K (n + h) w2 := by
      rintro ⟨w1, w2, n1, n2, n12, z1, z2⟩
      have m1 := hin w1 z1
      have m2 := hin w2 z2
      have mu : u ∈ Lw n C (opnd C h ju) := mem_Lw.mpr hu1f
      have h3 : ({u, w1, w2} : Finset (Fin n)).card = 3 :=
        Finset.card_eq_three.mpr ⟨u, w1, w2, Ne.symm n1, Ne.symm n2, n12, rfl⟩
      have hsub : ({u, w1, w2} : Finset (Fin n)) ⊆ Lw n C (opnd C h ju) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact mu
        · exact m1
        · exact m2
      have := Finset.card_le_card hsub
      omega
    by_cases hBig : ∃ w1 w2 : Fin n, w1 ≠ u ∧ w2 ≠ u ∧ w1 ≠ w2 ∧
        ZWp G C K (opnd C k ((1 : Fin 2) - j)) w1 ∧ ZWp G C K (opnd C k ((1 : Fin 2) - j)) w2
    · obtain ⟨g, c, hg, hin', hr1, hr2, hr3, hb1, hb2⟩ :=
        path_split C (fun r => ∃ w1 w2 : Fin n, w1 ≠ u ∧ w2 ≠ u ∧ w1 ≠ w2 ∧
          ZWp G C K r w1 ∧ ZWp G C K r w2) (n + h) hτ _ hrh hBig
      obtain ⟨w1, w2, n1, n2, n12, z1, z2⟩ := hb1
      exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨(g, c), slot_mem C hg hin', huv,
        ⟨h, hr3, hWu⟩, two_of_notbig _ u hb2, ⟨u, w1, w2, Ne.symm n1, Ne.symm n2, n12,
          ⟨h, hr2.trans hr3, hWu⟩, z1, z2⟩, k, j, hlen, hand, hr1, hvP, _, hX5, hXc⟩))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨(k, j), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hlen, Finset.mem_univ _⟩, huv, cP, hvL, ⟨h, hrh, hWu⟩,
        two_of_notbig _ u hBig⟩))))

open PEqualNP.TopForm in
lemma shape31_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hAO2 : IsAO2 n C) (K : ℕ) (hK : 4 ≤ K)
    (t : ℕ) (ht : t ∈ tops G C) (i : Fin 2) (u v : Fin n) (huv : G.Adj u v)
    (hside : u ∈ side (n := n) C t i)
    (k : ℕ) (hk : k ∈ junk G C) (hork : OrReaches n C (opnd C t ((1 : Fin 2) - i)) k)
    (j : Fin 2) (hk3 : u ∈ side (n := n) C k j ∨ v ∈ side (n := n) C k j)
    (h : ℕ) (hh : h ∈ junk G C) (horh : OrReaches n C (opnd C k ((1 : Fin 2) - j)) h)
    (hr0 : u ∈ side (n := n) C h 0 ∨ v ∈ side (n := n) C h 0)
    (hr1 : u ∈ side (n := n) C h 1 ∨ v ∈ side (n := n) C h 1) :
    Pay9 G C K u v := by
  rcases hk3 with hu3 | hv3
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (shape31_Id G C h4 hAO2 K (by omega)
      t ht i u v huv hside k hk hork j hu3 h hh horh hr0 hr1))))))
  · rcases hr0 with hu0 | hv0
    · rcases hr1 with hu1 | hv1
      · exact Or.inl (Or.inl (Or.inl (Or.inl (shape31_IIb G C h4 hAO2 K hK t ht i u v huv
          hside k hk hork j hv3 h hh horh hu0 hu1))))
      · exact shape31_IIc4 G C h4 hAO2 K hK t ht i u v huv hside k hk hork j hv3 h hh horh
          0 hu0 hv1
    · rcases hr1 with hu1 | hv1
      · exact shape31_IIc4 G C h4 hAO2 K hK t ht i u v huv hside k hk hork j hv3 h hh horh
          1 hu1 hv0
      · exact Or.inl (Or.inl (Or.inl (payd_pay6 G C K u v (shape31_IIa G C h4 hAO2 K
          (by omega) t ht i u v huv hside k hk hork j hv3 h hh horh hv0 hv1))))

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

open PEqualNP.TopForm in
lemma main_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C)
    (hnn : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j) :
    (Ustar G C).card ≤ 2212 * (C.size + 1) := by
  have hin : ∀ k ∈ junk G C, k ∈ ijunk G C :=
    fun k hk => mem_ijunk.mpr ⟨hk, fun j hj => hnn j hj k hk⟩
  apply local_bound G hg C hL.1 hT (Ustar G C)
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hadjuv : G.Adj u v := by
      have h := he
      simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] at h
      exact h.1
    have hadj : ∀ a b : Fin n, s(u, v) = s(a, b) → G.Adj a b := by
      intro a b hab
      rcases Sym2.eq_iff.mp hab with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact hadjuv
      · rw [← e1, ← e2]; exact hadjuv.symm
    rcases off_star G C hL hT u v he with
      ⟨a, b, hab, t, ht, i, k, hk, hside, hor, hv⟩ |
      ⟨a, b, hab, t, ht, h, hh, k, hk, _, hor1, hor2, hv1, hv2⟩
    · exact ⟨a, b, hab, hadj a b hab, t, ht, Or.inl ⟨i, k, hin k hk, hside, hor, hv⟩⟩
    · exact ⟨a, b, hab, hadj a b hab, t, ht,
        Or.inr ⟨h, hin h hh, k, hin k hk, hor1, hor2, hv1, hv2⟩⟩

open PEqualNP.TopForm in
lemma case0 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
    ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      junk G C = ∅ → Ustar G C = ∅ := by
  intro n G _ _ _ C hL hT hj
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  revert he
  induction e using Sym2.ind with
  | _ u v =>
    intro huv
    rcases off_star G C hL hT u v huv with
      ⟨_, _, _, _, _, _, x, hx, _⟩ | ⟨_, _, _, _, _, x, hx, _⟩
    · rw [hj] at hx; simp at hx
    · rw [hj] at hx; simp at hx

open PEqualNP.TopForm in
lemma case1 : ∃ k1 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
    ∀ (C : Circuit) (g : ℕ), IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      junk G C = {g} → (Ustar G C).card ≤ k1 * (C.size + 1) :=
  ⟨12, fun _ G _ hg5 _ C g hL hT hj => main G C hg5 hL hT g hj⟩

open PEqualNP.TopForm in
lemma case2 : ∃ k2 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
    ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      2 ≤ (junk G C).card →
      (∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j) →
      (Ustar G C).card ≤ k2 * (C.size + 1) :=
  ⟨2212, fun _ G _ hg _ C hL hT _ hnn => main_bound G hg C hL hT hnn⟩

lemma assembly (nested : (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)))) : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k1, h1⟩ := case1
  obtain ⟨k2, h2⟩ := case2
  obtain ⟨k3, h3⟩ := nested
  refine ⟨max k1 (max k2 k3), ?_⟩
  intro n G _ hgirth hne C hL hT
  by_cases hj0 : (PEqualNP.TopForm.junk G C).card = 0
  · rw [case0 n G hgirth hne C hL hT (Finset.card_eq_zero.mp hj0)]
    simp
  · by_cases hj1 : (PEqualNP.TopForm.junk G C).card = 1
    · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj1
      exact (h1 n G hgirth hne C g hL hT hg).trans (Nat.mul_le_mul_right _ (le_max_left _ _))
    · have hj2 : 2 ≤ (PEqualNP.TopForm.junk G C).card := by omega
      by_cases hnest : ∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.EdgeOwnership.InCone n C i j
      · exact (h3 n G hgirth hne C hL hT hj2 hnest).trans
          (Nat.mul_le_mul_right _ ((le_max_right k2 k3).trans (le_max_right k1 _)))
      · refine (h2 n G hgirth hne C hL hT hj2 ?_).trans
          (Nat.mul_le_mul_right _ ((le_max_left k2 k3).trans (le_max_right k1 _)))
        intro i hi j hj hic
        exact hnest ⟨i, hi, j, hj, hic⟩

open PEqualNP.TopForm in
lemma leaves4_case : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    ∀ S : Finset (Sym2 (Fin n)), S ⊆ Ustar G C →
    (∀ e ∈ S, ∃ a b : Fin n, e = s(a, b) ∧ ∃ t ∈ tops G C, ∀ i : Fin 2,
        a ∈ side C t i ∨ b ∈ side C t i ∨ ∃ k ∈ junk G C, OrReaches n C (opnd C t i) k ∧
          ((∀ j : Fin 2, a ∈ side C k j ∨ b ∈ side C k j) ∨
            ∃ j : Fin 2, a ∈ side C t ((1 : Fin 2) - i) ∧ (a ∈ side C k j ∨ b ∈ side C k j) ∧
              ∃ h ∈ junk G C, OrReaches n C (opnd C k ((1 : Fin 2) - j)) h ∧
                ∀ m : Fin 2, a ∈ side C h m ∨ b ∈ side C h m)) →
    S.card ≤ c * (C.size + 1) := by
  refine ⟨5752, ?_⟩
  intro n G _ hg C hL hT S hSU hW
  have hAO2 : IsAO2 n C := hL.1
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) :=
    fun a b c d hac hbd h => no4 G hg a b c d h.1 h.2.1 h.2.2.1 h.2.2.2 hac hbd
  have h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg' => le_of_eq (hAO2.2.2 g hg')
  have e10 : ((1 : Fin 2) - 0) = 1 := by decide
  have e11 : ((1 : Fin 2) - 1) = 0 := by decide
  have hb := bnd_or (pay9_bnd G C h4 hAO2 h2) (bnd_swap (pay9_bnd G C h4 hAO2 h2))
  have hs : C.size = C.gates.length := rfl
  rw [hs]
  refine (edges_bnd _ _ hb S ?_).trans (by omega)
  intro e he
  obtain ⟨a, b, hab, t, ht, hall⟩ := hW e he
  have heU := hSU he
  have hadj : G.Adj a b := by
    have h := heU
    rw [hab] at h
    simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] at h
    exact h.1
  by_cases hp : Pay9 G C 5 a b
  · exact ⟨a, b, hab, Or.inl hp⟩
  have up : ∀ x y : Fin n, Pay G C 5 x y → Pay9 G C 5 x y :=
    fun x y h => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
  have key : ∀ i : Fin 2, a ∈ side (n := n) C t i ∨ b ∈ side (n := n) C t i ∨
      ∃ k ∈ junk G C, OrReaches n C (opnd C t i) k ∧
        ∀ j : Fin 2, a ∈ side (n := n) C k j ∨ b ∈ side (n := n) C k j := by
    intro i
    rcases hall i with h0 | h0 | ⟨k, hk, hor, hrect | ⟨j, hat, hk3, h, hh, horh, hm⟩⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨k, hk, hor, hrect⟩)
    · exfalso
      apply hp
      have hor' : OrReaches n C (opnd C t ((1 : Fin 2) - ((1 : Fin 2) - i))) k := by
        rw [fin2_ss]; exact hor
      exact shape31_all G C h4 hAO2 5 (by norm_num) t ht ((1 : Fin 2) - i) a b hadj hat
        k hk hor' j hk3 h hh horh (hm 0) (hm 1)
  have hnostar : ∀ x y : Fin n, e = s(x, y) → x ∈ side (n := n) C t 0 →
      y ∈ side (n := n) C t 1 → False := by
    intro x y hxy hx hy
    have h := heU
    simp only [Ustar, Finset.mem_sdiff] at h
    apply h.2
    unfold starEdges
    exact Finset.mem_biUnion.mpr ⟨t, ht,
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, hxy.symm⟩⟩
  have hnofire : ∀ x : Fin n, x ∈ side (n := n) C t 0 → x ∈ side (n := n) C t 1 → False := by
    intro x hx0 hx1
    have h1 : Fires n C (opnd C t ((1 : Fin 2) - 0)) x := by
      rw [e10]; exact fires_side C t 1 x hx1
    exact G.irrefl (fires_adj G C hAO2 t ht 0 x x (fires_side C t 0 x hx0) h1)
  have hba : e = s(b, a) := hab.trans Sym2.eq_swap
  have wpay : ∀ x y : Fin n, G.Adj x y → RWit G C x y → Pay9 G C 5 x y :=
    fun x y hxy hw => up x y (rwit_pay G C h4 hAO2 5 (by norm_num) x y hxy hw)
  rcases key 0 with h0 | h0 | ⟨h, hh, hor0, hjh⟩ <;>
    rcases key 1 with h1 | h1 | ⟨k, hk, hor1, hjk⟩
  · exact (hnofire a h0 h1).elim
  · exact (hnostar a b hab h0 h1).elim
  · exact ⟨a, b, hab, Or.inl (wpay a b hadj ⟨t, ht, Or.inl ⟨0, k, hk, h0,
      by rw [e10]; exact hor1, hjk 0, hjk 1⟩⟩)⟩
  · exact (hnostar b a hba h0 h1).elim
  · exact (hnofire b h0 h1).elim
  · exact ⟨a, b, hab, Or.inr (wpay b a hadj.symm ⟨t, ht, Or.inl ⟨0, k, hk, h0,
      by rw [e10]; exact hor1, (hjk 0).symm, (hjk 1).symm⟩⟩)⟩
  · exact ⟨a, b, hab, Or.inl (wpay a b hadj ⟨t, ht, Or.inl ⟨1, h, hh, h1,
      by rw [e11]; exact hor0, hjh 0, hjh 1⟩⟩)⟩
  · exact ⟨a, b, hab, Or.inr (wpay b a hadj.symm ⟨t, ht, Or.inl ⟨1, h, hh, h1,
      by rw [e11]; exact hor0, (hjh 0).symm, (hjh 1).symm⟩⟩)⟩
  · exact ⟨a, b, hab, Or.inl (wpay a b hadj ⟨t, ht, Or.inr ⟨h, hh, k, hk, hor0, hor1,
      hjh 0, hjh 1, hjk 0, hjk 1⟩⟩)⟩

end PEqualNP.Outside.L_meta_8197

theorem PEqualNP.Outside.L_meta_8197 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x6 → PEqualNP.TopForm.TopForm x3 x6 → ∀ x9 ⊆ PEqualNP.TopForm.Ustar x3 x6, (∀ x11 ∈ x9, ∃ (x13 : Fin x2) (x14 : Fin x2), x11 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x6, ∀ (x16 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x15 x16 ∨ x14 ∈ PEqualNP.TopForm.side x6 x15 x16 ∨ ∃ x17 ∈ PEqualNP.TopForm.junk x3 x6, PEqualNP.CleanedNonEdge.OrReaches x2 x6 (PEqualNP.TopForm.opnd x6 x15 x16) x17 ∧ ((∀ (x18 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x17 x18 ∨ x14 ∈ PEqualNP.TopForm.side x6 x17 x18) ∨ ∃ (x18 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x15 ((1 : Fin (2 : ℕ)) - x16) ∧ (x13 ∈ PEqualNP.TopForm.side x6 x17 x18 ∨ x14 ∈ PEqualNP.TopForm.side x6 x17 x18) ∧ ∃ x19 ∈ PEqualNP.TopForm.junk x3 x6, PEqualNP.CleanedNonEdge.OrReaches x2 x6 (PEqualNP.TopForm.opnd x6 x17 ((1 : Fin (2 : ℕ)) - x18)) x19 ∧ ∀ (x20 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x19 x20 ∨ x14 ∈ PEqualNP.TopForm.side x6 x19 x20)) → x9.card ≤ x1 * (x6.size + (1 : ℕ)) :=
  PEqualNP.Outside.L_meta_8197.leaves4_case
