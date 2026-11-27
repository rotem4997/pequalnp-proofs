import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18846

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def rgate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem rgate_op (f : ℕ → ℕ) (g : Gate) : (rgate f g).op = g.op := rfl

theorem rgate_len (f : ℕ → ℕ) (g : Gate) : (rgate f g).inputs.length = g.inputs.length := by
  simp [rgate]

theorem rgate_id (gs : List Gate) : gs.map (rgate id) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, ih]
    cases g
    simp [rgate]

theorem rgate_eval (f : ℕ → ℕ) (g : Gate) (w : List Bool) :
    (rgate f g).op.eval ((rgate f g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD (f i) false) := by
  show g.op.eval ((g.inputs.map f).map fun i => w.getD i false) = _
  rw [List.map_map]
  rfl

def gateRel (R : Bool → Bool → Prop) (g : Gate) : Prop :=
  ∀ a b : ℕ → Bool, (∀ i ∈ g.inputs, R (a i) (b i)) →
    R (g.op.eval (g.inputs.map a)) (g.op.eval (g.inputs.map b))

theorem gateRel_eq (g : Gate) : gateRel Eq g := by
  intro a b h
  rw [List.map_congr_left h]

theorem gateRel_of_opMono {R : Bool → Bool → Prop} (hR : OpMono R) {g : Gate}
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) : gateRel R g :=
  fun a b h => hR g.op hop g.inputs a b h

theorem flow_step_ne (w : List Bool) (g : Gate) (i : ℕ) (h : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact step_lt w g i hi
  · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by omega)]

theorem flow_span (R : Bool → Bool → Prop) (p q : ℕ → ℕ) (gs : List Gate) :
    ∀ (w v : List Bool),
    (∀ g ∈ gs, gateRel R g) →
    (∀ i k, k < gs.length → (p i = w.length + k ↔ q i = v.length + k)) →
    (∀ i, R (w.getD (p i) false) (v.getD (q i) false)) →
    ∀ i, R ((W (gs.map (rgate p)) w).getD (p i) false)
      ((W (gs.map (rgate q)) v).getD (q i) false) := by
  induction gs with
  | nil =>
    intro w v _ _ hf i
    exact hf i
  | cons g gs ih =>
    intro w v hops hs hf
    rw [List.map_cons, List.map_cons, W_cons, W_cons]
    refine ih (step w (rgate p g)) (step v (rgate q g))
      (fun a ha => hops a (List.mem_cons_of_mem _ ha)) ?_ ?_
    · intro i k hk
      have h0 := hs i (k + 1) (by rw [List.length_cons]; omega)
      rw [step_len, step_len]
      have e1 : w.length + 1 + k = w.length + (k + 1) := by omega
      have e2 : v.length + 1 + k = v.length + (k + 1) := by omega
      rw [e1, e2]
      exact h0
    · intro j
      have h0 := hs j 0 (by rw [List.length_cons]; omega)
      simp only [Nat.add_zero] at h0
      by_cases hp : p j = w.length
      · have hq := h0.mp hp
        rw [step_last _ _ _ hp, step_last _ _ _ hq, rgate_eval, rgate_eval]
        exact hops g List.mem_cons_self (fun i => w.getD (p i) false)
          (fun i => v.getD (q i) false) (fun i _ => hf i)
      · have hq : q j ≠ v.length := fun h => hp (h0.mpr h)
        rw [flow_step_ne _ _ _ hp, flow_step_ne _ _ _ hq]
        exact hf j

theorem flow_map (R : Bool → Bool → Prop) (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hops : ∀ g ∈ gs, gateRel R g)
    (hs : ∀ i k, k < gs.length → (i = w.length + k ↔ f i = v.length + k))
    (hf : ∀ i, R (w.getD i false) (v.getD (f i) false)) :
    ∀ i, R ((W gs w).getD i false) ((W (gs.map (rgate f)) v).getD (f i) false) := by
  have h := flow_span R id f gs w v hops hs hf
  rw [rgate_id] at h
  exact h

theorem flow_map_eq (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hs : ∀ i k, k < gs.length → (i = w.length + k ↔ f i = v.length + k))
    (hf : ∀ i, w.getD i false = v.getD (f i) false) :
    ∀ i, (W gs w).getD i false = (W (gs.map (rgate f)) v).getD (f i) false :=
  flow_map Eq f gs w v (fun g _ => gateRel_eq g) hs hf

theorem flow_map_mono (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hs : ∀ i k, k < gs.length → (i = w.length + k ↔ f i = v.length + k))
    (hf : ∀ i, w.getD i false = true → v.getD (f i) false = true) :
    ∀ i, (W gs w).getD i false = true → (W (gs.map (rgate f)) v).getD (f i) false = true :=
  flow_map (fun a b => a = true → b = true) f gs w v
    (fun g hg => gateRel_of_opMono opMono_imp (hops g hg)) hs hf

theorem flow_rename (f : ℕ → ℕ) (n : ℕ) (hf1 : ∀ i, n ≤ i → f i = i) (hf2 : ∀ i, i < n → f i < n)
    (gs : List Gate) (x y : List Bool) (hl : x.length = y.length) (hn : n ≤ x.length)
    (hxy : ∀ i, i < x.length → x.getD i false = y.getD (f i) false) :
    ∀ i, (W gs x).getD i false = (W (gs.map (rgate f)) y).getD (f i) false := by
  refine flow_map_eq f gs x y ?_ ?_
  · intro i k _
    by_cases hi : i < n
    · have := hf2 i hi
      constructor <;> intro h <;> omega
    · rw [hf1 i (by omega), ← hl]
  · intro i
    by_cases hi : i < x.length
    · exact hxy i hi
    · rw [hf1 i (by omega), getD_ge x i (by omega), getD_ge y i (by omega)]

theorem flow_rename_eval (C : Circuit) (f : ℕ → ℕ) (n : ℕ) (hf1 : ∀ i, n ≤ i → f i = i)
    (hf2 : ∀ i, i < n → f i < n) (x y : List Bool) (hl : x.length = y.length) (hn : n ≤ x.length)
    (hxy : ∀ i, i < x.length → x.getD i false = y.getD (f i) false) :
    Circuit.eval ⟨C.gates.map (rgate f), f C.output⟩ y = C.eval x :=
  (flow_rename f n hf1 hf2 C.gates x y hl hn hxy C.output).symm

def flow_del (L t i : ℕ) : ℕ := if i < L then i else if i = L then t else i - 1

theorem flow_drop (g : Gate) (rest : List Gate) (w : List Bool) (t : ℕ)
    (ht : t < w.length ∨ w.length + rest.length ≤ t)
    (hval : g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD t false) :
    ∀ o, (W (g :: rest) w).getD o false
      = (W (rest.map (rgate (flow_del w.length t))) w).getD (flow_del w.length t o) false := by
  rw [W_cons]
  refine flow_map_eq (flow_del w.length t) rest (step w g) w ?_ ?_
  · intro i k hk
    rw [step_len]
    unfold flow_del
    split_ifs <;> constructor <;> intro h <;> omega
  · intro i
    unfold flow_del
    split_ifs with h1 h2
    · exact step_lt w g i h1
    · rw [step_last w g i h2]
      exact hval
    · rw [getD_ge _ i (by rw [step_len]; omega), getD_ge w (i - 1) (by omega)]

theorem flow_drop_mid (pre post : List Gate) (g : Gate) (w : List Bool) (t : ℕ)
    (ht : t < w.length + pre.length ∨ w.length + pre.length + post.length ≤ t)
    (hval : g.op.eval (g.inputs.map fun i => (W pre w).getD i false) = (W pre w).getD t false) :
    ∀ o, (W (pre ++ g :: post) w).getD o false
      = (W (pre ++ post.map (rgate (flow_del (w.length + pre.length) t))) w).getD
          (flow_del (w.length + pre.length) t o) false := by
  intro o
  rw [W_append, W_append]
  have hl := W_length pre w
  rw [← hl]
  exact flow_drop g post (W pre w) t (by rw [hl]; exact ht) hval o

theorem flow_drop_eval (C : Circuit) (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post)
    (n : ℕ) (x : List Bool) (hx : x.length = n) (t : ℕ)
    (ht : t < n + pre.length ∨ n + pre.length + post.length ≤ t)
    (hval : g.op.eval (g.inputs.map fun i => (W pre x).getD i false) = (W pre x).getD t false) :
    C.eval x = Circuit.eval ⟨pre ++ post.map (rgate (flow_del (n + pre.length) t)),
      flow_del (n + pre.length) t C.output⟩ x := by
  subst hx
  show (W C.gates x).getD C.output false = _
  rw [hC]
  exact flow_drop_mid pre post g x t ht hval C.output

theorem flow_drop_len (pre post : List Gate) (g : Gate) (h : Gate → Gate) :
    (pre ++ post.map h).length + 1 = (pre ++ g :: post).length := by
  simp
  omega

theorem flow_bool (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem flow_gate (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i ∈ ins, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    have ih' := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have hi := h i List.mem_cons_self
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih' ⊢
      exact (flow_bool t _ _ _ _ hi ih').1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih' ⊢
      exact (flow_bool t _ _ _ _ hi ih').2

theorem flow_redirect (t : Bool) (f : ℕ → ℕ) (gs : List Gate) : ∀ (w v : List Bool),
    w.length = v.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, f i ≠ i →
      i < w.length + k ∧ f i < w.length + k) →
    (∀ i, f i ≠ i → (W gs w).getD i false = t → (W gs w).getD (f i) false = t) →
    (∀ i, w.getD i false = t → v.getD i false = t) →
    ∀ i, (W gs w).getD i false = t → (W (gs.map (rgate f)) v).getD i false = t := by
  induction gs with
  | nil =>
    intro w v _ _ _ _ hf i h
    exact hf i h
  | cons g gs ih =>
    intro w v hl hops hr hab hf
    rw [List.map_cons, W_cons, W_cons]
    rw [W_cons] at hab
    have hside : ∀ i ∈ g.inputs, w.getD i false = t → v.getD (f i) false = t := by
      intro i hi h1
      by_cases hfi : f i = i
      · rw [hfi]
        exact hf i h1
      · obtain ⟨hk1, hk2⟩ := hr 0 (by rw [List.length_cons]; omega) i
          (by simpa [List.getD_cons_zero] using hi) hfi
        have h2 : (W gs (step w g)).getD i false = t := by
          rw [W_prefix gs _ i (by rw [step_len]; omega), step_lt w g i (by omega)]
          exact h1
        have h3 := hab i hfi h2
        rw [W_prefix gs _ (f i) (by rw [step_len]; omega), step_lt w g (f i) (by omega)] at h3
        exact hf _ h3
    have hstep : g.op.eval (g.inputs.map fun i => w.getD i false) = t →
        (rgate f g).op.eval ((rgate f g).inputs.map fun i => v.getD i false) = t := by
      rw [rgate_eval]
      exact flow_gate t g.op (hops g List.mem_cons_self) g.inputs
        (fun i => w.getD i false) (fun i => v.getD (f i) false) hside
    refine ih (step w g) (step v (rgate f g)) (by rw [step_len, step_len, hl])
      (fun a ha => hops a (List.mem_cons_of_mem _ ha)) ?_ hab ?_
    · intro k hk i hm hfi
      obtain ⟨h1, h2⟩ := hr (k + 1) (by rw [List.length_cons]; omega) i
        (by simpa [List.getD_cons_succ] using hm) hfi
      rw [step_len]
      exact ⟨by omega, by omega⟩
    · intro i hi
      by_cases h1 : i < w.length
      · rw [step_lt w g i h1] at hi
        rw [step_lt v _ i (by omega)]
        exact hf i hi
      · by_cases h2 : i = w.length
        · rw [step_last w g i h2] at hi
          rw [step_last v _ i (by omega)]
          exact hstep hi
        · rw [getD_ge _ _ (by rw [step_len]; omega)] at hi
          rw [getD_ge _ _ (by rw [step_len]; omega)]
          exact hi

theorem flow_redirect_fun (n : ℕ) (C : Circuit) (w w' : ℕ) (hm : Monotone2 C) (hrb : ReadsBack n C)
    (hread : ∀ k < C.gates.length, w ∈ (gateAt C k).inputs → w' < n + k)
    (h4 : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn x)).getD w' false = true)
    (h5 : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w' false = true →
      (C.wires (List.ofFn x)).getD w false = true ∨ circuitFun n C x = true) :
    circuitFun n ⟨C.gates.map (rgate fun ii => if ii = w then w' else ii),
      if C.output = w then w' else C.output⟩ = circuitFun n C := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hm g hg).1
  funext x
  have hy : (List.ofFn x).length = n := List.length_ofFn
  have hr : ∀ k < C.gates.length, ∀ i ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs,
      (fun ii => if ii = w then w' else ii) i ≠ i →
      i < (List.ofFn x).length + k ∧ (fun ii => if ii = w then w' else ii) i < (List.ofFn x).length + k := by
    intro k hk i hi hfi
    have hiw : i = w := by
      by_contra hc
      exact hfi (if_neg hc)
    rw [hiw] at hi
    show i < (List.ofFn x).length + k ∧ (if i = w then w' else i) < (List.ofFn x).length + k
    rw [if_pos hiw, hy, hiw]
    exact ⟨hrb k hk w hi, hread k hk hi⟩
  have key : ∀ t : Bool, ((W C.gates (List.ofFn x)).getD w false = t →
      (W C.gates (List.ofFn x)).getD w' false = t) →
      ∀ i, (W C.gates (List.ofFn x)).getD i false = t →
      (W (C.gates.map (rgate fun ii => if ii = w then w' else ii)) (List.ofFn x)).getD i false = t := by
    intro t ht
    refine flow_redirect t (fun ii => if ii = w then w' else ii) C.gates (List.ofFn x) (List.ofFn x)
      rfl hops hr ?_ (fun i h => h)
    intro i hfi
    have hiw : i = w := by
      by_contra hc
      exact hfi (if_neg hc)
    show _ → (W C.gates (List.ofFn x)).getD (if i = w then w' else i) false = t
    rw [if_pos hiw, hiw]
    exact ht
  have h4x : (W C.gates (List.ofFn x)).getD w false = true →
      (W C.gates (List.ofFn x)).getD w' false = true := h4 x
  have h5x : (W C.gates (List.ofFn x)).getD w' false = true →
      (W C.gates (List.ofFn x)).getD w false = true ∨
        (W C.gates (List.ofFn x)).getD C.output false = true := h5 x
  show (W (C.gates.map (rgate fun ii => if ii = w then w' else ii)) (List.ofFn x)).getD
      (if C.output = w then w' else C.output) false
    = (W C.gates (List.ofFn x)).getD C.output false
  generalize W C.gates (List.ofFn x) = WW at key h4x h5x ⊢
  generalize W (C.gates.map (rgate fun ii => if ii = w then w' else ii)) (List.ofFn x) = VV
    at key ⊢
  have hup := key true h4x
  by_cases heq : WW.getD w false = WW.getD w' false
  · have hdn := key false (fun h => by rw [← heq]; exact h)
    have hall : ∀ i, VV.getD i false = WW.getD i false := by
      intro i
      cases hW : WW.getD i false
      · exact hdn i hW
      · exact hup i hW
    by_cases ho : C.output = w
    · rw [if_pos ho, hall, ho, heq]
    · rw [if_neg ho, hall]
  · have hw : WW.getD w false = false := by
      cases h1 : WW.getD w false
      · rfl
      · exact absurd (h1.trans (h4x h1).symm) heq
    have hw' : WW.getD w' false = true := by
      cases h2 : WW.getD w' false
      · exact absurd (hw.trans h2.symm) heq
      · rfl
    have ho1 : WW.getD C.output false = true := by
      rcases h5x hw' with h | h
      · rw [hw] at h
        exact absurd h Bool.false_ne_true
      · exact h
    rw [ho1]
    by_cases ho : C.output = w
    · rw [if_pos ho]
      exact hup w' hw'
    · rw [if_neg ho]
      exact hup _ ho1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_cons (b : ℕ) (g : Gate) (gs : List Gate) (hg : ∀ i ∈ g.inputs, i < b)
    (h : RBo (b + 1) gs) : RBo b (g :: gs) := by
  intro p hp i hi
  cases p with
  | zero =>
    have hi' : i ∈ g.inputs := hi
    have := hg i hi'
    omega
  | succ q =>
    have hq : q < gs.length := by
      rw [List.length_cons] at hp
      omega
    have hi' : i ∈ (gs.getD q ⟨GateOp.or, []⟩).inputs := hi
    have := h q hq i hi'
    omega

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

def keepL (S : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => !decide (j ∈ S))

def rk (S : Finset ℕ) (m : ℕ) : ℕ := (keepL S m).length

def rn (n : ℕ) (S : Finset ℕ) (w : ℕ) : ℕ := if w < n then w else n + rk S (w - n)

def mkG (n : ℕ) (C : Circuit) (S : Finset ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (rn n S)⟩

def Dg (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : List Gate := (keepL S m).map (mkG n C S)

theorem keepL_succ_in (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : keepL S (m + 1) = keepL S m := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem keepL_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    keepL S (m + 1) = keepL S m ++ [m] := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem rk_mono (S : Finset ℕ) (a b : ℕ) (h : a ≤ b) : rk S a ≤ rk S b := by
  unfold rk keepL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem rk_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : rk S (m + 1) = rk S m + 1 := by
  unfold rk
  rw [keepL_succ_out S m h, List.length_append, List.length_singleton]

theorem rk_lt (S : Finset ℕ) (j m : ℕ) (hj : j < m) (hS : j ∉ S) : rk S j < rk S m := by
  have h1 := rk_succ_out S j hS
  have h2 := rk_mono S (j + 1) m hj
  omega

theorem rn_lt (n : ℕ) (S : Finset ℕ) (i m : ℕ) (hi : i < n + m) (hS : i < n ∨ i - n ∉ S) :
    rn n S i < n + rk S m := by
  unfold rn
  by_cases h : i < n
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hS2 : i - n ∉ S := by
      rcases hS with h1 | h1
      · exact absurd h1 h
      · exact h1
    have := rk_lt S (i - n) m (by omega) hS2
    omega

theorem rn_gate (n : ℕ) (S : Finset ℕ) (o : ℕ) : rn n S (n + o) = n + rk S o := by
  unfold rn
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem Dg_succ_in (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∈ S) :
    Dg n C S (m + 1) = Dg n C S m := by
  unfold Dg
  rw [keepL_succ_in S m h]

theorem Dg_succ_out (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    Dg n C S (m + 1) = Dg n C S m ++ [mkG n C S m] := by
  unfold Dg
  rw [keepL_succ_out S m h, List.map_append, List.map_singleton]

theorem Dg_len (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : (Dg n C S m).length = rk S m := by
  unfold Dg rk
  rw [List.length_map]

theorem keep_gate (C : Circuit) (S : Finset ℕ) (j : ℕ) (hj : j ∈ keepL S C.gates.length) :
    gateAt C j ∈ C.gates := by
  have hjl : j < C.gates.length := by
    have := (List.mem_filter.mp hj).1
    exact List.mem_range.mp this
  exact gateAt_mem hjl

theorem restrict_val (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : List Bool) (hx : x.length = n) :
    ∀ m, m ≤ C.gates.length →
      (W (Dg n C S m) x).length = n + rk S m ∧
      ∀ w, w < n + m → (w < n ∨ w - n ∉ S) →
        (W (Dg n C S m) x).getD (rn n S w) false = val C x w := by
  have hsn : ∀ (l : List Bool) (b : Bool) (k : ℕ), l.length = k → (l ++ [b]).getD k false = b := by
    intro l b k hk
    subst hk
    exact getD_app_len l b
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [W_length, Dg_len, hx]
    · intro w hw _
      have hw' : w < n := by omega
      have e : rn n S w = w := by unfold rn; rw [if_pos hw']
      rw [e, W_prefix (Dg n C S 0) x w (by omega), val_input hx hw']
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    by_cases hS : m ∈ S
    · have e2 : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hS]
      rw [Dg_succ_in n C S m hS, e2]
      refine ⟨hlen, ?_⟩
      intro w hw hk
      have hne : w ≠ n + m := by
        intro hwe
        rcases hk with h1 | h1
        · omega
        · apply h1
          have : w - n = m := by omega
          rw [this]
          exact hS
      exact hval w (by omega) hk
    · rw [Dg_succ_out n C S m hS, rk_succ_out S m hS, W_append]
      have hsingle : ∀ v : List Bool, W [mkG n C S m] v =
          v ++ [(gateAt C m).op.eval (((gateAt C m).inputs.map (rn n S)).map
            fun i => v.getD i false)] :=
        fun v => rfl
      rw [hsingle]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · intro w hw hk
        by_cases hwm : w = n + m
        · subst hwm
          rw [rn_gate, hsn _ _ _ hlen, val_gate_rb hx (by omega) (hRB m (by omega)), List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hval i (hRB m (by omega) i hi) (hcl m (by omega) hS i hi)
        · have hw2 : w < n + m := by omega
          rw [getD_app_lt _ _ _ (by rw [hlen]; exact rn_lt n S w m hw2 hk)]
          exact hval w hw2 hk

theorem restrict_rb (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∀ m, m ≤ C.gates.length → RBo n (Dg n C S m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact RBo_nil n
  | succ m ih =>
    intro hm
    by_cases hS : m ∈ S
    · rw [Dg_succ_in n C S m hS]
      exact ih (by omega)
    · rw [Dg_succ_out n C S m hS]
      apply RBo_append _ _ _ (ih (by omega))
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      have hi' : i ∈ (gateAt C m).inputs.map (rn n S) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
      rw [Dg_len]
      exact rn_lt n S i0 m (hRB m (by omega) i0 hi0) (hcl m (by omega) hS i0 hi0)

theorem restrict_size (n : ℕ) (C : Circuit) (S : Finset ℕ) (hS : ∀ j ∈ S, j < C.gates.length) :
    (Dg n C S C.gates.length).length + S.card ≤ C.gates.length := by
  have h3 : (List.range C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length +
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length :=
    List.length_eq_length_filter_add _
  have h4 : S.card ≤ ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length := by
    refine le_trans (Finset.card_le_card ?_)
      (List.toFinset_card_le (l := (List.range C.gates.length).filter (fun j => decide (j ∈ S))))
    intro j hj
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr (hS j hj), by simpa using hj⟩
  have h5 : (Dg n C S C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length := Dg_len n C S _
  rw [List.length_range] at h3
  omega

theorem restrict_circ (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (o : ℕ) (ho : o < C.gates.length) (hoS : o ∉ S) (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + S.card ≤ C.size := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  refine ⟨⟨Dg n C S C.gates.length, n + rk S o⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact hao (gateAt C j) (keep_gate C S j hj)
  · exact restrict_rb n C S hRB hcl _ le_rfl
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    have := h2 _ (keep_gate C S j hj)
    show ((gateAt C j).inputs.map (rn n S)).length = 2
    rw [List.length_map]
    exact this
  · funext x
    have h := (restrict_val n C S hRB hcl (List.ofFn x) (by simp) C.gates.length le_rfl).2 (n + o)
      (by omega) (Or.inr (by rw [Nat.add_sub_cancel_left]; exact hoS))
    rw [rn_gate] at h
    show (W (Dg n C S C.gates.length) (List.ofFn x)).getD (n + rk S o) false =
      val C (List.ofFn x) C.output
    rw [hout]
    exact h
  · exact restrict_size n C S hS

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ocg : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | t, i :: L, b => ⟨GateOp.or, [t, i]⟩ :: ocg b L (b + 1)

def octop : ℕ → List ℕ → ℕ → ℕ
  | t, [], _ => t
  | _, _ :: L, b => octop b L (b + 1)

theorem oc_ex (L : List ℕ) (w1 w : List Bool) (h : ∀ i ∈ L, w1.getD i false = w.getD i false) :
    (∃ i ∈ L, w1.getD i false = true) ↔ (∃ i ∈ L, w.getD i false = true) := by
  constructor
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [← h i hi]; exact h1⟩
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [h i hi]; exact h1⟩

theorem ocg_len (L : List ℕ) : ∀ (t b : ℕ), (ocg t L b).length = L.length := by
  induction L with
  | nil => intro t b; rfl
  | cons i L ih =>
    intro t b
    show (ocg b L (b + 1)).length + 1 = L.length + 1
    rw [ih]

theorem octop_nil (t b : ℕ) : octop t [] b = t := rfl

theorem octop_cons (L : List ℕ) : ∀ (t b : ℕ), L ≠ [] → octop t L b = b + L.length - 1 := by
  induction L with
  | nil => intro t b h; exact absurd rfl h
  | cons i L ih =>
    intro t b _
    show octop b L (b + 1) = b + (L.length + 1) - 1
    by_cases h : L = []
    · subst h
      rfl
    · rw [ih b (b + 1) h]
      omega

theorem octop_lt (L : List ℕ) (t b : ℕ) (ht : t < b) : octop t L b < b + L.length := by
  by_cases h : L = []
  · subst h
    rw [octop_nil]
    simp
    exact ht
  · rw [octop_cons L t b h]
    have : L.length ≠ 0 := by
      intro h0
      exact h (List.length_eq_zero_iff.mp h0)
    omega

theorem ocg_gate (L : List ℕ) : ∀ (t b : ℕ) (g : Gate), g ∈ ocg t L b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction L with
  | nil => intro t b g hg; simp [ocg] at hg
  | cons i L ih =>
    intro t b g hg
    have hg' : g ∈ (⟨GateOp.or, [t, i]⟩ : Gate) :: ocg b L (b + 1) := hg
    rcases List.mem_cons.mp hg' with h1 | h1
    · subst h1
      exact ⟨rfl, rfl⟩
    · exact ih b (b + 1) g h1

theorem ocg_val (L : List ℕ) : ∀ (t b : ℕ) (w : List Bool), w.length = b → t < b → (∀ i ∈ L, i < b) →
    ((W (ocg t L b) w).getD (octop t L b) false = true ↔
      (w.getD t false = true ∨ ∃ i ∈ L, w.getD i false = true)) := by
  induction L with
  | nil =>
    intro t b w _ _ _
    simp [ocg, octop, W_nil]
  | cons i L ih =>
    intro t b w hw ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    have hs : ∀ a, a < b → (step w ⟨GateOp.or, [t, i]⟩).getD a false = w.getD a false :=
      fun a ha => step_lt w _ a (by omega)
    have hb : (step w ⟨GateOp.or, [t, i]⟩).getD b false = (w.getD t false || w.getD i false) := by
      rw [step_last w _ b hw.symm]
      simp [GateOp.eval]
    show (W (ocg b L (b + 1)) (step w ⟨GateOp.or, [t, i]⟩)).getD (octop b L (b + 1)) false = true ↔ _
    rw [ih b (b + 1) _ (by rw [step_len, hw]) (by omega) (fun a ha => by have := hL2 a ha; omega)]
    rw [hb, oc_ex L _ w (fun a ha => hs a (hL2 a ha))]
    constructor
    · rintro (h | ⟨a, ha, h⟩)
      · simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro (h | ⟨a, ha, h⟩)
      · exact Or.inl (by rw [h]; rfl)
      · rcases List.mem_cons.mp ha with h2 | ha2
        · subst h2
          exact Or.inl (by rw [h, Bool.or_true])
        · exact Or.inr ⟨a, ha2, h⟩

theorem ocg_rb (L : List ℕ) : ∀ (t b : ℕ), t < b → (∀ i ∈ L, i < b) → RBo b (ocg t L b) := by
  induction L with
  | nil => intro t b _ _; exact RBo_nil b
  | cons i L ih =>
    intro t b ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    apply RBo_cons
    · intro a ha
      have ha' : a ∈ [t, i] := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with h | h <;> omega
    · exact ih b (b + 1) (by omega)
        (fun a ha => by have := hL a (List.mem_cons.mpr (Or.inr ha)); omega)

def ostar : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | c, i :: L, b => ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]

theorem ostar_len (c : ℕ) (L : List ℕ) (b : ℕ) : (ostar c L b).length = L.length := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b ++ [_]).length = L.length + 1
    rw [List.length_append, ocg_len]
    rfl

theorem ostar_gate (c : ℕ) (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ostar c L b) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ostar] at hg
  | cons i L =>
    have hg' : g ∈ ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩] := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · have := ocg_gate L i b g h1
      exact ⟨Or.inr this.1, this.2⟩
    · rw [List.mem_singleton] at h1
      subst h1
      exact ⟨Or.inl rfl, rfl⟩

theorem ostar_val (c : ℕ) (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    ((W (ostar c L b) w).getD (b + L.length - 1) false = true ↔
      (w.getD c false = true ∧ ∃ i ∈ L, w.getD i false = true)) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show (W (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]) w).getD (b + (L.length + 1) - 1) false = true ↔ _
    have hlen : (W (ocg i L b) w).length = b + L.length := by rw [W_length, ocg_len, hw]
    rw [W_snoc, step_last _ _ _ (by rw [hlen]; omega)]
    have h1 : (W (ocg i L b) w).getD c false = w.getD c false := W_prefix _ w c (by omega)
    have h2 := ocg_val L i b w hw hi hL2
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    rw [h1, h2]
    constructor
    · rintro ⟨hc1, h | ⟨a, ha, h⟩⟩
      · exact ⟨hc1, i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨hc1, a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro ⟨hc1, a, ha, h⟩
      refine ⟨hc1, ?_⟩
      rcases List.mem_cons.mp ha with h3 | h3
      · subst h3
        exact Or.inl h
      · exact Or.inr ⟨a, h3, h⟩

theorem ostar_rb (c : ℕ) (L : List ℕ) (b : ℕ) (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    RBo b (ostar c L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show RBo b (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩])
    apply RBo_append _ _ _ (ocg_rb L i b hi hL2)
    apply RBo_cons _ _ _ _ (RBo_nil _)
    intro a ha
    have ha' : a ∈ [c, octop i L b] := ha
    have htop := octop_lt L i b hi
    rw [ocg_len]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with h | h <;> omega

def ostars (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | c :: cs, b => ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)

def ostarW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, b, d => if c = d then b + (Lf c).length - 1 else ostarW Lf cs (b + (Lf c).length) d

theorem ostars_len (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b,
    (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum := by
  induction cs with
  | nil => intro b; rfl
  | cons c cs ih =>
    intro b
    show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
    rw [List.length_append, ostar_len, ih, List.map_cons, List.sum_cons]

theorem ostars_gate (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b (g : Gate), g ∈ ostars Lf cs b →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction cs with
  | nil => intro b g hg; simp [ostars] at hg
  | cons c cs ih =>
    intro b g hg
    have hg' : g ∈ ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ostar_gate c (Lf c) b g h1
    · exact ih _ g h1

theorem ostars_rb (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b, (∀ c ∈ cs, c < b) →
    (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → RBo b (ostars Lf cs b) := by
  induction cs with
  | nil => intro b _ _; exact RBo_nil b
  | cons c cs ih =>
    intro b hc hi
    show RBo b (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length))
    apply RBo_append _ _ _ (ostar_rb c (Lf c) b (hc c (List.mem_cons.mpr (Or.inl rfl)))
      (hi c (List.mem_cons.mpr (Or.inl rfl))))
    rw [ostar_len]
    apply ih
    · intro d hd
      have := hc d (List.mem_cons.mpr (Or.inr hd))
      omega
    · intro d hd i hi2
      have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
      omega

theorem ostars_val (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ c ∈ cs, c < b) → (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → ∀ d ∈ cs, Lf d ≠ [] →
    ostarW Lf cs b d < b + (ostars Lf cs b).length ∧
    ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true ↔
      (w.getD d false = true ∧ ∃ i ∈ Lf d, w.getD i false = true)) := by
  induction cs with
  | nil => intro b w _ _ _ d hd; simp at hd
  | cons c cs ih =>
    intro b w hw hc hi d hd hLd
    have hc0 : c < b := hc c (List.mem_cons.mpr (Or.inl rfl))
    have hi0 : ∀ i ∈ Lf c, i < b := hi c (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ostar c (Lf c) b) w).length = b + (Lf c).length := by
      rw [W_length, ostar_len, hw]
    have hpre : ∀ a, a < b → (W (ostar c (Lf c) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ostars Lf (c :: cs) b) w = W (ostars Lf cs (b + (Lf c).length)) (W (ostar c (Lf c) b) w) :=
      W_append _ _ w
    have eL : (ostars Lf (c :: cs) b).length = (Lf c).length + (ostars Lf cs (b + (Lf c).length)).length := by
      show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
      rw [List.length_append, ostar_len]
    rw [eW, eL]
    by_cases hcd : c = d
    · subst hcd
      have ew : ostarW Lf (c :: cs) b c = b + (Lf c).length - 1 := by
        show (if c = c then b + (Lf c).length - 1 else _) = _
        rw [if_pos rfl]
      have hpos : (Lf c).length ≠ 0 := by
        intro h0
        exact hLd (List.length_eq_zero_iff.mp h0)
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact ostar_val c (Lf c) b w hLd hw hc0 hi0
    · have ew : ostarW Lf (c :: cs) b d = ostarW Lf cs (b + (Lf c).length) d := by
        show (if c = d then b + (Lf c).length - 1 else _) = _
        rw [if_neg hcd]
      have hd2 : d ∈ cs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hcd
        · exact h
      have hcs : ∀ e ∈ cs, e < b := fun e he => hc e (List.mem_cons.mpr (Or.inr he))
      have his : ∀ e ∈ cs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (Lf c).length) _ hlen1
        (fun e he => by have := hcs e he; omega)
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, hpre d (hcs d hd2), oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def ochain : List ℕ → ℕ → List Gate
  | [], _ => []
  | i :: L, b => ocg i L b

def ochainTop : List ℕ → ℕ → ℕ
  | [], _ => 0
  | i :: L, b => octop i L b

theorem ochain_len (L : List ℕ) (b : ℕ) : (ochain L b).length = L.length - 1 := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b).length = L.length + 1 - 1
    rw [ocg_len]
    omega

theorem ochain_gate (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ochain L b) :
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ochain] at hg
  | cons i L => exact ocg_gate L i b g hg

theorem ochain_rb (L : List ℕ) (b : ℕ) (hL : ∀ i ∈ L, i < b) : RBo b (ochain L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    exact ocg_rb L i b (hL i (List.mem_cons.mpr (Or.inl rfl)))
      (fun a ha => hL a (List.mem_cons.mpr (Or.inr ha)))

theorem ochain_val (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hL : ∀ i ∈ L, i < b) :
    ochainTop L b < b + (ochain L b).length ∧
    ((W (ochain L b) w).getD (ochainTop L b) false = true ↔ ∃ i ∈ L, w.getD i false = true) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    refine ⟨?_, ?_⟩
    · show octop i L b < b + (ocg i L b).length
      rw [ocg_len]
      exact octop_lt L i b hi
    · show (W (ocg i L b) w).getD (octop i L b) false = true ↔ _
      rw [ocg_val L i b w hw hi hL2]
      constructor
      · rintro (h | ⟨a, ha, h⟩)
        · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
        · exact ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
      · rintro ⟨a, ha, h⟩
        rcases List.mem_cons.mp ha with h2 | h2
        · subst h2
          exact Or.inl h
        · exact Or.inr ⟨a, h2, h⟩

def ochains (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | X :: Xs, b => ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)

def ochainsW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | X :: Xs, b, d => if X = d then ochainTop (Lf X) b else ochainsW Lf Xs (b + (ochain (Lf X) b).length) d

theorem ochains_len (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b,
    (ochains Lf Xs b).length = (Xs.map fun X => (Lf X).length - 1).sum := by
  induction Xs with
  | nil => intro b; rfl
  | cons X Xs ih =>
    intro b
    show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
    rw [List.length_append, ochain_len, ih, List.map_cons, List.sum_cons]

theorem ochains_gate (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b (g : Gate), g ∈ ochains Lf Xs b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction Xs with
  | nil => intro b g hg; simp [ochains] at hg
  | cons X Xs ih =>
    intro b g hg
    have hg' : g ∈ ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ochain_gate (Lf X) b g h1
    · exact ih _ g h1

theorem ochains_rb (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b, (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) →
    RBo b (ochains Lf Xs b) := by
  induction Xs with
  | nil => intro b _; exact RBo_nil b
  | cons X Xs ih =>
    intro b hi
    show RBo b (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length))
    apply RBo_append _ _ _ (ochain_rb (Lf X) b (hi X (List.mem_cons.mpr (Or.inl rfl))))
    apply ih
    intro d hd i hi2
    have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
    omega

theorem ochains_val (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) → ∀ d ∈ Xs, Lf d ≠ [] →
    ochainsW Lf Xs b d < b + (ochains Lf Xs b).length ∧
    ((W (ochains Lf Xs b) w).getD (ochainsW Lf Xs b d) false = true ↔
      ∃ i ∈ Lf d, w.getD i false = true) := by
  induction Xs with
  | nil => intro b w _ _ d hd; simp at hd
  | cons X Xs ih =>
    intro b w hw hi d hd hLd
    have hi0 : ∀ i ∈ Lf X, i < b := hi X (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ochain (Lf X) b) w).length = b + (ochain (Lf X) b).length := by
      rw [W_length, hw]
    have hpre : ∀ a, a < b → (W (ochain (Lf X) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ochains Lf (X :: Xs) b) w =
        W (ochains Lf Xs (b + (ochain (Lf X) b).length)) (W (ochain (Lf X) b) w) := W_append _ _ w
    have eL : (ochains Lf (X :: Xs) b).length =
        (ochain (Lf X) b).length + (ochains Lf Xs (b + (ochain (Lf X) b).length)).length := by
      show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
      rw [List.length_append]
    rw [eW, eL]
    by_cases hXd : X = d
    · subst hXd
      have ew : ochainsW Lf (X :: Xs) b X = ochainTop (Lf X) b := by
        show (if X = X then ochainTop (Lf X) b else _) = _
        rw [if_pos rfl]
      obtain ⟨hlt, hv⟩ := ochain_val (Lf X) b w hLd hw hi0
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact hv
    · have ew : ochainsW Lf (X :: Xs) b d = ochainsW Lf Xs (b + (ochain (Lf X) b).length) d := by
        show (if X = d then ochainTop (Lf X) b else _) = _
        rw [if_neg hXd]
      have hd2 : d ∈ Xs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hXd
        · exact h
      have his : ∀ e ∈ Xs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (ochain (Lf X) b).length) _ hlen1
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def tpAB (n : ℕ) : List Gate :=
  (List.range (2 * n)).map (fun k => (⟨GateOp.or, [k, if k < n then 3 * n + k else n + k]⟩ : Gate))

def tpLA (n : ℕ) : List ℕ := (List.range n).map (fun k => 4 * n + k)

def tpLB (n : ℕ) : List ℕ := (List.range n).map (fun k => 5 * n + k)

def tpP (n : ℕ) : List Gate :=
  tpAB n ++ (ochain (tpLA n) (6 * n) ++ ochain (tpLB n) (6 * n + (n - 1)))

def tpK (n : ℕ) : ℕ := 4 * n + (tpP n).length

def tpF (n : ℕ) (i : ℕ) : ℕ := if i < 2 * n then 4 * n + i else i - 2 * n + tpK n

def tpAw (n : ℕ) : ℕ := ochainTop (tpLA n) (6 * n)

def tpBw (n : ℕ) : ℕ := ochainTop (tpLB n) (6 * n + (n - 1))

def tpC (n : ℕ) (C : Circuit) : Circuit :=
  ⟨tpP n ++ (C.gates.map (rgate (tpF n)) ++
    [⟨GateOp.and, [tpF n C.output, tpAw n]⟩, ⟨GateOp.and, [tpK n + C.gates.length, tpBw n]⟩]),
   tpK n + C.gates.length + 1⟩

theorem tpAB_len (n : ℕ) : (tpAB n).length = 2 * n := by simp [tpAB]

theorem tpP_len (n : ℕ) : (tpP n).length = 2 * n + ((n - 1) + (n - 1)) := by
  unfold tpP
  rw [List.length_append, List.length_append, tpAB_len, ochain_len, ochain_len]
  simp [tpLA, tpLB]

theorem tpC_len (n : ℕ) (C : Circuit) :
    (tpC n C).gates.length = (tpP n).length + C.gates.length + 2 := by
  unfold tpC
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem tpAB_get (n k : ℕ) (hk : k < (tpAB n).length) :
    (tpAB n)[k] = (⟨GateOp.or, [k, if k < n then 3 * n + k else n + k]⟩ : Gate) := by
  simp [tpAB]

theorem tpAB_val (n : ℕ) (x : List Bool) (hx : x.length = 4 * n) (k : ℕ) (hk : k < 2 * n) :
    (W (tpAB n) x).getD (4 * n + k) false =
      (x.getD k false || x.getD (if k < n then 3 * n + k else n + k) false) := by
  have hk2 : k < (tpAB n).length := by rw [tpAB_len]; exact hk
  have h := W_gate (tpAB n) x k hk2
  rw [tpAB_get n k hk2, hx] at h
  rw [h]
  have hk1 : k < 4 * n + k := by omega
  have he : (if k < n then 3 * n + k else n + k) < 4 * n + k := by split_ifs <;> omega
  simp only [List.map_cons, List.map_nil]
  rw [if_pos hk1, if_pos he, W_prefix (tpAB n) x k (by omega),
    W_prefix (tpAB n) x (if k < n then 3 * n + k else n + k) (by rw [hx]; split_ifs <;> omega),
    eval_or2]

theorem tp_oe {a b : ℕ} (u : Fin a) (v : Fin b) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = a + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold PEqualNP.Represents.oneEach
  by_cases h : i < a
  · have h' : i < (List.ofFn fun j : Fin a => decide (j = u)).length := by
      simp only [List.length_ofFn]; exact h
    rw [getD_app_lt _ _ i h', ofFn_getD _ i h, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_mk]
    omega
  · have h' : (List.ofFn fun j : Fin a => decide (j = u)).length ≤ i := by
      simp only [List.length_ofFn]; omega
    rw [List.getD_append_right _ _ _ _ h', List.length_ofFn]
    by_cases h2 : i - a < b
    · rw [ofFn_getD _ (i - a) h2, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_mk]
      omega
    · rw [ofFn_getD_ge _ (i - a) (by omega)]
      symm
      rw [decide_eq_false_iff_not]
      omega

theorem tp_zv (n : ℕ) (x : List Bool) (hx : x.length = 4 * n) (u v : ℕ) (hu : u < 2 * n)
    (hv : v < 2 * n) (hxv : ∀ i, x.getD i false = decide (i = u ∨ i = 2 * n + v))
    (k : ℕ) (hk : k < 2 * n) :
    (W (tpAB n) x).getD (4 * n + k) false =
      decide (k = u ∨ (k < n ∧ n + k = v) ∨ (n ≤ k ∧ k = n + v)) := by
  rw [tpAB_val n x hx k hk, hxv k, hxv (if k < n then 3 * n + k else n + k), Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  split_ifs <;> omega

theorem tp_exA (n : ℕ) (x : List Bool) (hx : x.length = 4 * n) (u v : ℕ) (hu : u < 2 * n)
    (hv : v < 2 * n) (hxv : ∀ i, x.getD i false = decide (i = u ∨ i = 2 * n + v)) :
    (∃ i ∈ tpLA n, (W (tpAB n) x).getD i false = true) ↔ (u < n ∨ n ≤ v) := by
  constructor
  · rintro ⟨i, hi, h⟩
    unfold tpLA at hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    rw [List.mem_range] at hk
    rw [tp_zv n x hx u v hu hv hxv k (by omega), decide_eq_true_eq] at h
    omega
  · intro h
    by_cases h1 : u < n
    · refine ⟨4 * n + u, by unfold tpLA; exact List.mem_map.mpr ⟨u, List.mem_range.mpr h1, rfl⟩, ?_⟩
      rw [tp_zv n x hx u v hu hv hxv u (by omega), decide_eq_true_eq]
      omega
    · refine ⟨4 * n + (v - n), by
        unfold tpLA; exact List.mem_map.mpr ⟨v - n, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
      rw [tp_zv n x hx u v hu hv hxv (v - n) (by omega), decide_eq_true_eq]
      omega

theorem tp_exB (n : ℕ) (x : List Bool) (hx : x.length = 4 * n) (u v : ℕ) (hu : u < 2 * n)
    (hv : v < 2 * n) (hxv : ∀ i, x.getD i false = decide (i = u ∨ i = 2 * n + v)) :
    (∃ i ∈ tpLB n, (W (tpAB n) x).getD i false = true) ↔ (n ≤ u ∨ v < n) := by
  constructor
  · rintro ⟨i, hi, h⟩
    unfold tpLB at hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    rw [List.mem_range] at hk
    have e : 5 * n + k = 4 * n + (n + k) := by omega
    rw [e, tp_zv n x hx u v hu hv hxv (n + k) (by omega), decide_eq_true_eq] at h
    omega
  · intro h
    by_cases h1 : n ≤ u
    · refine ⟨5 * n + (u - n), by
        unfold tpLB; exact List.mem_map.mpr ⟨u - n, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have e : 5 * n + (u - n) = 4 * n + (n + (u - n)) := by omega
      rw [e, tp_zv n x hx u v hu hv hxv (n + (u - n)) (by omega), decide_eq_true_eq]
      omega
    · refine ⟨5 * n + v, by
        unfold tpLB; exact List.mem_map.mpr ⟨v, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have e : 5 * n + v = 4 * n + (n + v) := by omega
      rw [e, tp_zv n x hx u v hu hv hxv (n + v) (by omega), decide_eq_true_eq]
      omega

theorem tpP_pre (n : ℕ) (x : List Bool) (hx : x.length = 4 * n) (j : ℕ) (hj : j < 6 * n) :
    (W (tpP n) x).getD j false = (W (tpAB n) x).getD j false := by
  unfold tpP
  rw [W_append]
  exact W_prefix _ _ j (by rw [W_length, hx, tpAB_len]; omega)

theorem tp_A (n : ℕ) (hn : 1 ≤ n) (x : List Bool) (hx : x.length = 4 * n) :
    tpAw n < 6 * n + (n - 1) ∧
    ((W (tpP n) x).getD (tpAw n) false = true ↔
      ∃ i ∈ tpLA n, (W (tpAB n) x).getD i false = true) := by
  have hwa : (W (tpAB n) x).length = 6 * n := by rw [W_length, hx, tpAB_len]; omega
  have hlA : (tpLA n).length = n := by simp [tpLA]
  have hL0 : tpLA n ≠ [] := fun h => by
    have h2 := congrArg List.length h
    rw [hlA, List.length_nil] at h2
    omega
  have hL : ∀ i ∈ tpLA n, i < 6 * n := by
    intro i hi
    unfold tpLA at hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    rw [List.mem_range] at hk
    omega
  obtain ⟨h1, h2⟩ := ochain_val (tpLA n) (6 * n) (W (tpAB n) x) hL0 hwa hL
  rw [ochain_len, hlA] at h1
  refine ⟨h1, ?_⟩
  have e : W (tpP n) x =
      W (ochain (tpLB n) (6 * n + (n - 1))) (W (ochain (tpLA n) (6 * n)) (W (tpAB n) x)) := by
    unfold tpP; rw [W_append, W_append]
  have hlt : tpAw n < (W (ochain (tpLA n) (6 * n)) (W (tpAB n) x)).length := by
    rw [W_length, hwa, ochain_len, hlA]; exact h1
  rw [e, W_prefix _ _ (tpAw n) hlt]
  exact h2

theorem tp_B (n : ℕ) (hn : 1 ≤ n) (x : List Bool) (hx : x.length = 4 * n) :
    tpBw n < 6 * n + (n - 1) + (n - 1) ∧
    ((W (tpP n) x).getD (tpBw n) false = true ↔
      ∃ i ∈ tpLB n, (W (tpAB n) x).getD i false = true) := by
  have hwa : (W (tpAB n) x).length = 6 * n := by rw [W_length, hx, tpAB_len]; omega
  have hlA : (tpLA n).length = n := by simp [tpLA]
  have hlB : (tpLB n).length = n := by simp [tpLB]
  have hwb : (W (ochain (tpLA n) (6 * n)) (W (tpAB n) x)).length = 6 * n + (n - 1) := by
    rw [W_length, hwa, ochain_len, hlA]
  have hL0 : tpLB n ≠ [] := fun h => by
    have h2 := congrArg List.length h
    rw [hlB, List.length_nil] at h2
    omega
  have hL6 : ∀ i ∈ tpLB n, i < 6 * n := by
    intro i hi
    unfold tpLB at hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    rw [List.mem_range] at hk
    omega
  have hL : ∀ i ∈ tpLB n, i < 6 * n + (n - 1) := fun i hi => by
    have := hL6 i hi
    omega
  obtain ⟨h1, h2⟩ := ochain_val (tpLB n) (6 * n + (n - 1)) _ hL0 hwb hL
  rw [ochain_len, hlB] at h1
  refine ⟨h1, ?_⟩
  have e : W (tpP n) x =
      W (ochain (tpLB n) (6 * n + (n - 1))) (W (ochain (tpLA n) (6 * n)) (W (tpAB n) x)) := by
    unfold tpP; rw [W_append, W_append]
  rw [e]
  refine h2.trans ?_
  apply oc_ex
  intro i hi
  exact W_prefix _ _ i (by rw [hwa]; exact hL6 i hi)

theorem tp_tail (w0 : List Bool) (a A B : ℕ) (hB : B < w0.length) :
    (W [(⟨GateOp.and, [a, A]⟩ : Gate), ⟨GateOp.and, [w0.length, B]⟩] w0).getD
        (w0.length + 1) false =
      ((w0.getD a false && w0.getD A false) && w0.getD B false) := by
  rw [W_cons, W_single, step_last _ _ (w0.length + 1) (step_len _ _).symm]
  show GateOp.and.eval [(step w0 ⟨GateOp.and, [a, A]⟩).getD w0.length false,
    (step w0 ⟨GateOp.and, [a, A]⟩).getD B false] = _
  rw [eval_and2, step_last _ _ w0.length rfl, step_lt _ _ B hB]
  show (GateOp.and.eval [w0.getD a false, w0.getD A false] && w0.getD B false) = _
  rw [eval_and2]

theorem tp_flow (n : ℕ) (C : Circuit) (x x' : List Bool) (hx : x.length = 4 * n)
    (hx' : x'.length = 2 * n)
    (hz : ∀ k, k < 2 * n → x'.getD k false = (W (tpAB n) x).getD (4 * n + k) false) :
    (W (C.gates.map (rgate (tpF n))) (W (tpP n) x)).getD (tpF n C.output) false = C.eval x' := by
  have hw1 : (W (tpP n) x).length = tpK n := by
    unfold tpK; rw [W_length, hx]
  have hK : 6 * n ≤ tpK n := by unfold tpK; rw [tpP_len]; omega
  have hs : ∀ i k, k < C.gates.length →
      (i = x'.length + k ↔ tpF n i = (W (tpP n) x).length + k) := by
    intro i k _
    rw [hx', hw1]
    unfold tpF
    split_ifs with h1 <;> omega
  have hf : ∀ i, x'.getD i false = (W (tpP n) x).getD (tpF n i) false := by
    intro i
    by_cases h1 : i < 2 * n
    · have e : tpF n i = 4 * n + i := if_pos h1
      rw [e, hz i h1, tpP_pre n x hx (4 * n + i) (by omega)]
    · have e : tpF n i = i - 2 * n + tpK n := if_neg h1
      rw [e, getD_ge x' i (by omega), getD_ge (W (tpP n) x) (i - 2 * n + tpK n) (by omega)]
  rw [eval_W]
  exact (flow_map_eq (tpF n) C.gates x' (W (tpP n) x) hs hf C.output).symm

theorem tp_out (n : ℕ) (hn : 1 ≤ n) (C : Circuit) (x : List Bool) (hx : x.length = 4 * n) :
    (tpC n C).eval x =
      (((W (C.gates.map (rgate (tpF n))) (W (tpP n) x)).getD (tpF n C.output) false &&
        (W (tpP n) x).getD (tpAw n) false) && (W (tpP n) x).getD (tpBw n) false) := by
  have hw1 : (W (tpP n) x).length = tpK n := by
    unfold tpK; rw [W_length, hx]
  have hw0 : (W (C.gates.map (rgate (tpF n))) (W (tpP n) x)).length = tpK n + C.gates.length := by
    rw [W_length, hw1, List.length_map]
  have hK : tpK n = 6 * n + (n - 1) + (n - 1) := by unfold tpK; rw [tpP_len]; omega
  have hA := (tp_A n hn x hx).1
  have hB := (tp_B n hn x hx).1
  have hA1 : tpAw n < (W (tpP n) x).length := by rw [hw1]; omega
  have hB1 : tpBw n < (W (tpP n) x).length := by rw [hw1]; omega
  have hB0 : tpBw n < (W (C.gates.map (rgate (tpF n))) (W (tpP n) x)).length := by
    rw [hw0]; omega
  show (W (tpP n ++ (C.gates.map (rgate (tpF n)) ++
    [⟨GateOp.and, [tpF n C.output, tpAw n]⟩, ⟨GateOp.and, [tpK n + C.gates.length, tpBw n]⟩])) x).getD
      (tpK n + C.gates.length + 1) false = _
  rw [W_append, W_append, ← hw0, tp_tail _ _ _ _ hB0, W_prefix _ _ (tpAw n) hA1,
    W_prefix _ _ (tpBw n) hB1]

theorem tp_ff {b : Bool} {P : Prop} (h : b = true ↔ P) (hP : ¬P) : b = false := by
  cases b
  · rfl
  · exact absurd (h.mp rfl) hP

theorem tp_fan2 (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (tpC n C) := by
  intro g hg
  have hg' : g ∈ tpP n ++ (C.gates.map (rgate (tpF n)) ++
    [⟨GateOp.and, [tpF n C.output, tpAw n]⟩, ⟨GateOp.and, [tpK n + C.gates.length, tpBw n]⟩]) := hg
  rcases List.mem_append.mp hg' with h | h
  · unfold tpP at h
    rcases List.mem_append.mp h with h | h
    · unfold tpAB at h
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp h
      exact ⟨by simp, by simp⟩
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨h1, h2⟩ := ochain_gate _ _ g h
        exact ⟨by rw [h1]; simp, by omega⟩
      · obtain ⟨h1, h2⟩ := ochain_gate _ _ g h
        exact ⟨by rw [h1]; simp, by omega⟩
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
      exact ⟨by rw [rgate_op]; exact (hC g0 hg0).1, by rw [rgate_len]; exact (hC g0 hg0).2⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩

theorem tp_rep (n : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → Bool) (C : Circuit)
    (hCr : PEqualNP.Represents.Represents (fun u v : Fin n => G u.val v.val) C)
    (u v : Fin (2 * n)) :
    (tpC n C).eval (PEqualNP.Represents.oneEach u v) =
      decide ((u.val < n ∧ v.val < n ∧ G u.val v.val = true) ∨
        (n ≤ u.val ∧ n ≤ v.val ∧ G (v.val - n) (u.val - n) = true)) := by
  have hu := u.isLt
  have hv := v.isLt
  have hx : (PEqualNP.Represents.oneEach u v).length = 4 * n := by
    simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]; omega
  have hxv : ∀ i, (PEqualNP.Represents.oneEach u v).getD i false =
      decide (i = u.val ∨ i = 2 * n + v.val) := tp_oe u v
  obtain ⟨_, hA⟩ := tp_A n hn _ hx
  obtain ⟨_, hB⟩ := tp_B n hn _ hx
  rw [tp_exA n _ hx u.val v.val hu hv hxv] at hA
  rw [tp_exB n _ hx u.val v.val hu hv hxv] at hB
  rw [tp_out n hn C _ hx]
  by_cases h1 : u.val < n <;> by_cases h2 : v.val < n
  · have hx' : (PEqualNP.Represents.oneEach (⟨u.val, h1⟩ : Fin n) (⟨v.val, h2⟩ : Fin n)).length
        = 2 * n := by
      simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]; omega
    have hz : ∀ k, k < 2 * n →
        (PEqualNP.Represents.oneEach (⟨u.val, h1⟩ : Fin n) (⟨v.val, h2⟩ : Fin n)).getD k false
          = (W (tpAB n) (PEqualNP.Represents.oneEach u v)).getD (4 * n + k) false := by
      intro k hk
      rw [tp_oe, tp_zv n _ hx u.val v.val hu hv hxv k hk, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Fin.val_mk]
      omega
    have hc : C.eval (PEqualNP.Represents.oneEach (⟨u.val, h1⟩ : Fin n) (⟨v.val, h2⟩ : Fin n))
        = G u.val v.val := hCr _ _
    rw [tp_flow n C _ _ hx hx' hz, hc, hA.mpr (Or.inl h1), hB.mpr (Or.inr h2), Bool.and_true,
      Bool.and_true, Bool.eq_iff_iff, decide_eq_true_eq]
    constructor
    · intro h
      exact Or.inl ⟨h1, h2, h⟩
    · rintro (⟨_, _, h⟩ | ⟨h3, _, _⟩)
      · exact h
      · omega
  · rw [tp_ff hB (by omega), Bool.and_false]
    symm
    rw [decide_eq_false_iff_not]
    rintro (⟨_, h, _⟩ | ⟨h, _, _⟩) <;> omega
  · rw [tp_ff hA (by omega), Bool.and_false, Bool.false_and]
    symm
    rw [decide_eq_false_iff_not]
    rintro (⟨h, _, _⟩ | ⟨_, h, _⟩) <;> omega
  · have hx' : (PEqualNP.Represents.oneEach (⟨v.val - n, by omega⟩ : Fin n)
        (⟨u.val - n, by omega⟩ : Fin n)).length = 2 * n := by
      simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]; omega
    have hz : ∀ k, k < 2 * n →
        (PEqualNP.Represents.oneEach (⟨v.val - n, by omega⟩ : Fin n)
          (⟨u.val - n, by omega⟩ : Fin n)).getD k false
          = (W (tpAB n) (PEqualNP.Represents.oneEach u v)).getD (4 * n + k) false := by
      intro k hk
      rw [tp_oe, tp_zv n _ hx u.val v.val hu hv hxv k hk, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Fin.val_mk]
      omega
    have hc : C.eval (PEqualNP.Represents.oneEach (⟨v.val - n, by omega⟩ : Fin n)
        (⟨u.val - n, by omega⟩ : Fin n)) = G (v.val - n) (u.val - n) := hCr _ _
    rw [tp_flow n C _ _ hx hx' hz, hc, hA.mpr (Or.inr (by omega)), hB.mpr (Or.inl (by omega)),
      Bool.and_true, Bool.and_true, Bool.eq_iff_iff, decide_eq_true_eq]
    constructor
    · intro h
      exact Or.inr ⟨by omega, by omega, h⟩
    · rintro (⟨h3, _, _⟩ | ⟨_, _, h⟩)
      · omega
      · exact h

def FanRepAtMost {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C

theorem tp_main_fan2 : ∀ (n : ℕ), 1 ≤ n → ∀ (G : ℕ → ℕ → Bool) (s : ℕ),
  FanRepAtMost (fun u v : Fin n => G u.val v.val) s →
  FanRepAtMost
    (fun u v : Fin (2 * n) => decide ((u.val < n ∧ v.val < n ∧ G u.val v.val = true) ∨
                                      (n ≤ u.val ∧ n ≤ v.val ∧ G (v.val - n) (u.val - n) = true)))
    (s + 4 * n) := by
  intro n hn G s hrep
  obtain ⟨C, hCm, hCs, hCr⟩ := hrep
  refine ⟨tpC n C, tp_fan2 n C hCm, ?_, ?_⟩
  · have h1 := tpC_len n C
    have h2 := tpP_len n
    have h3 : C.gates.length ≤ s := hCs
    show (tpC n C).gates.length ≤ s + 4 * n
    omega
  · intro u v
    exact tp_rep n hn G C hCr u v

def blkH (n : ℕ) (G : ℕ → ℕ → Bool) (u v : ℕ) : Bool :=
  decide (u / n = v / n ∧ G (u % n) (v % n) = true)

theorem blk_congr_fan2 {a b : ℕ} (F K : ℕ → ℕ → Bool) (s t : ℕ) (hab : a = b) (hst : s ≤ t)
    (hFK : ∀ u v, u < b → v < b → F u v = K u v)
    (h : FanRepAtMost (fun u v : Fin a => F u.val v.val) s) :
    FanRepAtMost (fun u v : Fin b => K u.val v.val) t := by
  subst hab
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨C, h1, le_trans h2 hst, ?_⟩
  intro u v
  exact (h3 u v).trans (hFK u.val v.val u.isLt v.isLt)

theorem blk_pt (n m : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → Bool)
    (hG : ∀ u v : ℕ, u < n → v < n → G u v = G v u) (u v : ℕ) :
    decide ((u < m * n ∧ v < m * n ∧ blkH n G u v = true) ∨
      (m * n ≤ u ∧ m * n ≤ v ∧ blkH n G (v - m * n) (u - m * n) = true)) = blkH n G u v := by
  have hn0 : 0 < n := hn
  rw [Bool.eq_iff_iff]
  simp only [blkH, decide_eq_true_eq]
  by_cases hu : u < m * n <;> by_cases hv : v < m * n
  · constructor
    · rintro (⟨_, _, h⟩ | ⟨h, _, _⟩)
      · exact h
      · omega
    · intro h
      exact Or.inl ⟨hu, hv, h⟩
  · have h1 : u / n < m := (Nat.div_lt_iff_lt_mul hn0).2 hu
    have h2 : m ≤ v / n := (Nat.le_div_iff_mul_le hn0).2 (by omega)
    constructor
    · rintro (⟨_, h, _⟩ | ⟨h, _, _⟩) <;> omega
    · rintro ⟨h, _⟩
      omega
  · have h1 : v / n < m := (Nat.div_lt_iff_lt_mul hn0).2 hv
    have h2 : m ≤ u / n := (Nat.le_div_iff_mul_le hn0).2 (by omega)
    constructor
    · rintro (⟨h, _, _⟩ | ⟨_, h, _⟩) <;> omega
    · rintro ⟨h, _⟩
      omega
  · obtain ⟨a, rfl⟩ : ∃ a, u = a + m * n := ⟨u - m * n, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = b + m * n := ⟨v - m * n, by omega⟩
    have ea : a + m * n - m * n = a := Nat.add_sub_cancel a (m * n)
    have eb : b + m * n - m * n = b := Nat.add_sub_cancel b (m * n)
    rw [ea, eb, Nat.add_mul_div_right a m hn0, Nat.add_mul_div_right b m hn0,
      Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      hG (b % n) (a % n) (Nat.mod_lt _ hn0) (Nat.mod_lt _ hn0)]
    constructor
    · rintro (⟨h, _, _⟩ | ⟨_, _, h3, h4⟩)
      · omega
      · exact ⟨by omega, h4⟩
    · rintro ⟨h3, h4⟩
      exact Or.inr ⟨by omega, by omega, by omega, h4⟩

theorem blk_size (s n k : ℕ) :
    s + 4 * n * (2 ^ k - 1) + 4 * (2 ^ k * n) ≤ s + 4 * n * (2 ^ (k + 1) - 1) := by
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [pow_succ, hq]
  have e1 : q + 1 - 1 = q := Nat.add_sub_cancel q 1
  have e2 : (q + 1) * 2 - 1 = 2 * q + 1 := by omega
  rw [e1, e2]
  apply le_of_eq
  ring

theorem blk_gen_fan2 (n : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → Bool) (s : ℕ)
    (hG : ∀ u v : ℕ, u < n → v < n → G u v = G v u)
    (hrep : FanRepAtMost (fun u v : Fin n => G u.val v.val) s) (k : ℕ) :
    FanRepAtMost (fun u v : Fin (2 ^ k * n) => blkH n G u.val v.val)
      (s + 4 * n * (2 ^ k - 1)) := by
  induction k with
  | zero =>
    refine blk_congr_fan2 G (blkH n G) s (s + 4 * n * (2 ^ 0 - 1)) (by simp) (by simp) ?_ hrep
    intro u v hu hv
    simp only [pow_zero, one_mul] at hu hv
    simp only [blkH, Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hu,
      Nat.mod_eq_of_lt hv]
    simp
  | succ k ih =>
    have hN : 1 ≤ 2 ^ k * n := by
      have := Nat.one_le_two_pow (n := k)
      nlinarith
    have t := tp_main_fan2 (2 ^ k * n) hN (blkH n G) (s + 4 * n * (2 ^ k - 1)) ih
    exact blk_congr_fan2
      (fun u v => decide ((u < 2 ^ k * n ∧ v < 2 ^ k * n ∧ blkH n G u v = true) ∨
        (2 ^ k * n ≤ u ∧ 2 ^ k * n ≤ v ∧ blkH n G (v - 2 ^ k * n) (u - 2 ^ k * n) = true)))
      (blkH n G) _ _ (by ring) (blk_size s n k)
      (fun u v _ _ => blk_pt n (2 ^ k) hn G hG u v) t

theorem main_18846 : ∀ (n k : ℕ), 1 ≤ n → ∀ (G : ℕ → ℕ → Bool) (s : ℕ),
  (∀ u v : ℕ, u < n → v < n → G u v = G v u) →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
    PEqualNP.Represents.Represents (fun u v : Fin n => G u.val v.val) C) →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ (s + 4 * n * (2 ^ k - 1)) ∧
    PEqualNP.Represents.Represents (fun u v : Fin (2 ^ k * n) =>
      decide (u.val / n = v.val / n ∧ G (u.val % n) (v.val % n) = true)) C) := by
  intro n k hn G s hG hrep
  exact blk_gen_fan2 n hn G s hG hrep k

end PEqualNP.Outside.L_meta_18846

theorem PEqualNP.Outside.L_meta_18846 : (∀ (n k : ℕ), 1 ≤ n → ∀ (G : ℕ → ℕ → Bool) (s : ℕ), (∀ u v : ℕ, u < n → v < n → G u v = G v u) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents (fun u v : Fin n => G u.val v.val) C) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ (s + 4 * n * (2 ^ k - 1)) ∧ PEqualNP.Represents.Represents (fun u v : Fin (2 ^ k * n) => decide (u.val / n = v.val / n ∧ G (u.val % n) (v.val % n) = true)) C)) :=
  PEqualNP.Outside.L_meta_18846.main_18846
