import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545

-- FRAGMENT fold    DEPENDS: (none)
-- Wire list as a fold over the gate list. C.wires x = W C.gates x (rfl), C.eval x = (W C.gates x).getD C.output false.
-- Exports:
--   def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--   def W (gs : List Gate) (w : List Bool) := gs.foldl step w
--   wires_W C x : C.wires x = W C.gates x
--   eval_W C x : C.eval x = (W C.gates x).getD C.output false
--   circuitFun_W n C x : circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false
--   W_nil, W_cons : W (g :: gs) w = W gs (step w g), W_single : W [g] w = step w g
--   W_append : W (a ++ b) w = W b (W a w),  W_snoc : W (gs ++ [g]) w = step (W gs w) g
--   W_split j : W gs w = W (gs.drop j) (W (gs.take j) w)
--   step_len : (step w g).length = w.length + 1,  W_length : (W gs w).length = w.length + gs.length
--   getD_app_lt (i < l.length) : (l ++ l2).getD i false = l.getD i false
--   getD_app_len : (l ++ [v]).getD l.length false = v
--   getD_ge (l.length <= i) : l.getD i false = false
--   step_lt (i < w.length) : (step w g).getD i false = w.getD i false
--   step_last (k = w.length) : (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false)
--   W_prefix (i < w.length) : (W gs w).getD i false = w.getD i false
--   W_ge (w.length + gs.length <= i) : (W gs w).getD i false = false
--   W_snoc_getD : (W (gs ++ [g]) w).getD t false = if t = w.length + gs.length then (eval of g on W gs w) else (W gs w).getD t false
--   W_gate (j < gs.length) : (W gs w).getD (w.length + j) false
--        = gs[j].op.eval (gs[j].inputs.map fun i => if i < w.length + j then (W gs w).getD i false else false)
--   W_gate_pre (gs = pre ++ g :: post) : (W gs w).getD (w.length + pre.length) false = g.op.eval (g.inputs.map fun i => (W pre w).getD i false)
--   ofFn_getD (u < n) : (List.ofFn x).getD u false = x u
--   ofFn_getD_ge (n <= u) : (List.ofFn x).getD u false = false
--   split_gates (j < gs.length) : exists pre post, gs = pre ++ gs[j] :: post and pre.length = j
--   split2 (gs[j]? = some g) : exists pre post, pre.length = j, gs = pre ++ g :: post, and for all g2, gs.set j g2 = pre ++ g2 :: post
--   step_congr : same gate value on P gives same step
--   gateAt_eq (j < C.gates.length) : gateAt C j = C.gates[j],  gateAt_mem : gateAt C j in C.gates
--   gateAt_ge (C.gates.length <= j) : gateAt C j = (OR of nothing)
--   getElem?_gateAt : C.gates[j]? = some g -> gateAt C j = g and j < C.gates.length
--   eval_and_iff : GateOp.and.eval (l.map f) = true iff all i in l, f i = true
--   eval_or_iff : GateOp.or.eval (l.map f) = true iff exists i in l, f i = true
--   eval_and2 / eval_or2 : GateOp.and.eval [a, b] = (a and b) / GateOp.or.eval [a, b] = (a or b);  eval_or1 / eval_and1 : one operand copies it
-- Use: rewrite C.wires/eval/circuitFun into W, split the gate list at the changed gate with split2,
-- then compare W post (step P g1) with W post (step P g2) (W_prefix for wires below, W_gate for gate wires).

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

-- FRAGMENT mono    DEPENDS: fold
-- Wire values val, gate-by-gate value equations, monotonicity of AND/OR circuits, Monotone2 / IsAO2 facts,
-- minimal true points.
-- Exports:
--   def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false     (val C x u = (W C.gates x).getD u false by rfl)
--   eval_eq_val : C.eval x = val C x C.output ;  circuitFun_val : circuitFun n C x = val C (List.ofFn x) C.output
--   val_input (hx : x.length = n) (hu : u < n) : val C x u = x.getD u false
--   val_ofFn (u : Fin n) : val C (List.ofFn x) u.val = x u ;  val_ofFn_lt (hu : u < n) : val C (List.ofFn x) u = x (u, hu)
--   val_ge (hx : x.length = n) (hu : n + C.gates.length <= u) : val C x u = false
--   val_gate (hx : x.length = n) (hj : j < C.gates.length) :
--       val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => if i < n + j then val C x i else false)
--   val_gate_rb : same, without the if, when every input i of gate j has i < n + j (ReadsBack)
--   val_or  (op = or)  : val C x (n + r) = true iff exists i in inputs, i < n + r and val C x i = true
--   val_and (op = and) : val C x (n + r) = true iff all i in inputs, i < n + r and val C x i = true
--   and_val (IsAO2, op = and) : val C x (n + j) = (val of input 0 && val of input 1)  (inputs.getD 0 0 / getD 1 0)
--   or_val  (IsAO2, op = or)  : val C x (n + j) = (val of input 0 || val of input 1)
--   def OpMono R : AND and OR are monotone for relation R on Bool ;  opMono_eq : OpMono Eq ;  opMono_imp : OpMono (a = true -> b = true)
--   andOrOnly_of_monotone2 : Monotone2 C -> AndOrOnly C ;  andOrOnly_of_isAO2 : IsAO2 n C -> AndOrOnly C
--   mono (AndOrOnly C) (x <= y pointwise) : for all w, val C (ofFn x) w = true -> val C (ofFn y) w = true
--   circuitFun_mono (AndOrOnly C) (x <= y) : circuitFun n C x = true -> circuitFun n C y = true
--   monotone2_len : Monotone2 C -> g in C.gates -> g.inputs.length <= 2 ;  isAO2_len : IsAO2 n C -> g in C.gates -> g.inputs.length = 2
--   isAO2_rb : IsAO2 n C -> j < C.gates.length -> i in (gateAt C j).inputs -> i < n + j
--   def tr y : Finset of true coordinates ;  tr_lt : z < y strictly -> (tr z).card < (tr y).card
--   exists_min F x (F x = true) : exists y <= x, F y = true and every z < y (z <= y, z ne y) has F z = false
-- Use: induction on the wire index w (Nat.strong_induction_on) with val_input / val_ge / val_gate to compare two runs.

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

-- FRAGMENT cones    DEPENDS: fold mono
-- Strict cones (PEqualNP.EdgeOwnership.cones / coneStep / InCone), PEqualNP.Core.coneSet, the leaves of a cone,
-- and: the value of a gate depends only on the inputs read inside its cone.
-- Exports (EO = PEqualNP.EdgeOwnership):
--   cones_len gs cs : (gs.foldl (EO.coneStep n) cs).length = cs.length + gs.length ;  cones_length : (EO.cones n C).length = C.gates.length
--   cones_char gs : i in (gs.foldl (coneStep n) []).getD j [] iff j < gs.length and exists w in (gs.getD j (OR of nothing)).inputs,
--       n <= w, w < n + j, (i = w - n or i in (fold).getD (w - n) [])
--   inCone_iff : EO.InCone n C i j iff j < C.gates.length and exists k, k < j and n + k in (gateAt C j).inputs and (i = k or InCone n C i k)
--   inCone_lt : InCone n C i j -> i < j and j < C.gates.length
--   inCone_of_read (j < C.gates.length) (k < j) (n + k in (gateAt C j).inputs) : InCone n C k j
--   inCone_trans : InCone n C i k -> InCone n C k j -> InCone n C i j
--   inCone_irrefl : not InCone n C j j
--   mem_coneSet : i in PEqualNP.Core.coneSet n C j iff i = j or InCone n C i j
--   self_mem_coneSet : j in coneSet n C j ;  coneSet_mono : InCone n C k j -> coneSet n C k subset coneSet n C j
--   coneSet_le (i in coneSet n C j) : i <= j ;  coneSet_sub_range (j < C.gates.length) : coneSet n C j subset Finset.range C.gates.length
--   def coneLeaves n C j : Finset (Fin n) := the inputs t with t read by some gate of coneSet n C j
--   mem_coneLeaves : t in coneLeaves n C j iff exists i in coneSet n C j, t.val in (gateAt C i).inputs
--   coneLeaves_mono : InCone n C k j -> coneLeaves n C k subset coneLeaves n C j
--   cone_agree (x, x' agree on coneLeaves n C j) : val C (List.ofFn x) (n + j) = val C (List.ofFn x') (n + j)
--   cone_agree_gateVal : same for EO.gateVal n C j x = EO.gateVal n C j x'
--   def coneRd n C z w : n <= w, w < n + C.gates.length, z in (gateAt C (w - n)).inputs  (wire w reads wire z)
--   coneRd_of_input, coneRd_lt (ReadsBack) : coneRd z w -> z < w ;  coneRtg_le (ReadsBack) : ReflTransGen coneRd z w -> z <= w
--   coneRtg_inCone (ReadsBack) : ReflTransGen coneRd w b -> n <= w -> w ne b -> InCone n C (w - n) (b - n)
--   inCone_coneRtg : InCone n C k i -> ReflTransGen coneRd (n + k) (n + i)
--   coneSet_iff_rtg (ReadsBack, j < len) : i in coneSet n C j iff i < C.gates.length and ReflTransGen coneRd (n + i) (n + j)
--   coneRd_reach_iff (ReadsBack, j < len, w ne n + j) : ReflTransGen coneRd w (n + j) iff exists i in coneSet n C j, w in (gateAt C i).inputs
-- Use: inCone_iff to unfold one level, mem_coneSet to move between coneSet and InCone, cone_agree to compare a gate at two inputs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_length (n : ℕ) (C : Circuit) :
    (PEqualNP.EdgeOwnership.cones n C).length = C.gates.length := by
  unfold PEqualNP.EdgeOwnership.cones
  rw [cones_len]; simp

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
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

theorem inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

theorem inCone_irrefl (n : ℕ) (C : Circuit) (j : ℕ) : ¬ PEqualNP.EdgeOwnership.InCone n C j j := by
  intro h
  have := (inCone_lt n C j j h).1
  omega

theorem mem_coneSet (n : ℕ) (C : Circuit) (i j : ℕ) :
    i ∈ PEqualNP.Core.coneSet n C j ↔ i = j ∨ PEqualNP.EdgeOwnership.InCone n C i j := by
  unfold PEqualNP.Core.coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · have := inCone_lt n C i j h
      exact Or.inr ⟨by omega, h⟩

theorem self_mem_coneSet (n : ℕ) (C : Circuit) (j : ℕ) : j ∈ PEqualNP.Core.coneSet n C j :=
  (mem_coneSet n C j j).mpr (Or.inl rfl)

theorem coneSet_mono (n : ℕ) (C : Circuit) (k j : ℕ) (h : PEqualNP.EdgeOwnership.InCone n C k j) :
    PEqualNP.Core.coneSet n C k ⊆ PEqualNP.Core.coneSet n C j := by
  intro i hi
  rw [mem_coneSet] at hi ⊢
  right
  rcases hi with hi | hi
  · rw [hi]; exact h
  · exact inCone_trans n C i k hi j h

theorem coneSet_le (n : ℕ) (C : Circuit) (i j : ℕ) (h : i ∈ PEqualNP.Core.coneSet n C j) : i ≤ j := by
  rw [mem_coneSet] at h
  rcases h with h | h
  · omega
  · have := (inCone_lt n C i j h).1
    omega

theorem coneSet_sub_range (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.Core.coneSet n C j ⊆ Finset.range C.gates.length := by
  intro i hi
  have := coneSet_le n C i j hi
  rw [Finset.mem_range]
  omega

def coneLeaves (n : ℕ) (C : Circuit) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t => ∃ i ∈ PEqualNP.Core.coneSet n C j, t.val ∈ (gateAt C i).inputs

theorem mem_coneLeaves (n : ℕ) (C : Circuit) (j : ℕ) (t : Fin n) :
    t ∈ coneLeaves n C j ↔ ∃ i ∈ PEqualNP.Core.coneSet n C j, t.val ∈ (gateAt C i).inputs := by
  unfold coneLeaves
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem coneLeaves_mono (n : ℕ) (C : Circuit) (k j : ℕ) (h : PEqualNP.EdgeOwnership.InCone n C k j) :
    coneLeaves n C k ⊆ coneLeaves n C j := by
  intro t ht
  rw [mem_coneLeaves] at ht ⊢
  obtain ⟨i, hi, hti⟩ := ht
  exact ⟨i, coneSet_mono n C k j h hi, hti⟩

theorem cone_agree (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) :
    ∀ j, (∀ t ∈ coneLeaves n C j, x t = x' t) →
      val C (List.ofFn x) (n + j) = val C (List.ofFn x') (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hxx
    by_cases hj : j < C.gates.length
    · rw [val_gate (n := n) (by simp) hj, val_gate (n := n) (by simp) hj]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases hlt : w < n + j
      · rw [if_pos hlt, if_pos hlt]
        by_cases hwn : w < n
        · rw [val_ofFn_lt C x w hwn, val_ofFn_lt C x' w hwn]
          apply hxx
          rw [mem_coneLeaves]
          exact ⟨j, self_mem_coneSet n C j, hw⟩
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < j := by omega
          apply ih k hk
          intro t ht
          exact hxx t (coneLeaves_mono n C k j (inCone_of_read n C k j hj hk hw) ht)
      · rw [if_neg hlt, if_neg hlt]
    · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]

theorem cone_agree_gateVal (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (j : ℕ)
    (hxx : ∀ t ∈ coneLeaves n C j, x t = x' t) :
    PEqualNP.EdgeOwnership.gateVal n C j x = PEqualNP.EdgeOwnership.gateVal n C j x' :=
  cone_agree n C x x' j hxx

def coneRd (n : ℕ) (C : Circuit) (z w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ z ∈ (gateAt C (w - n)).inputs

theorem coneRd_of_input {n : ℕ} {C : Circuit} {t w : ℕ} (ht : t < C.gates.length)
    (hw : w ∈ (gateAt C t).inputs) : coneRd n C w (n + t) :=
  ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hw⟩

theorem coneRd_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ} (h : coneRd n C z w) :
    z < w := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hRB (w - n) (by omega) z h3
  omega

theorem coneRtg_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ}
    (h : Relation.ReflTransGen (coneRd n C) z w) : z ≤ w := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => have := coneRd_lt hRB hbc; omega

theorem coneRtg_inCone {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w b : ℕ)
    (h : Relation.ReflTransGen (coneRd n C) w b) :
    n ≤ w → w ≠ b → PEqualNP.EdgeOwnership.InCone n C (w - n) (b - n) := by
  induction h with
  | refl => intro _ h; exact absurd rfl h
  | @tail b c hab hbc ih =>
    intro hw _
    have hbn : b < c := coneRd_lt hRB hbc
    have hwb : w ≤ b := coneRtg_le hRB hab
    obtain ⟨h1, h2, h3⟩ := hbc
    rw [inCone_iff]
    refine ⟨by omega, b - n, by omega, ?_, ?_⟩
    · have e : n + (b - n) = b := by omega
      rw [e]; exact h3
    · by_cases hwb' : w = b
      · left; rw [hwb']
      · right; exact ih hw hwb'

theorem inCone_coneRtg {n : ℕ} {C : Circuit} : ∀ i k, PEqualNP.EdgeOwnership.InCone n C k i →
    Relation.ReflTransGen (coneRd n C) (n + k) (n + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro k h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    have hst : coneRd n C (n + k') (n + i) := coneRd_of_input h0 hin
    rcases h3 with rfl | h3
    · exact Relation.ReflTransGen.single hst
    · exact (ih k' hk' k h3).tail hst

theorem coneSet_iff_rtg {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (i : ℕ) : i ∈ PEqualNP.Core.coneSet n C j ↔
      i < C.gates.length ∧ Relation.ReflTransGen (coneRd n C) (n + i) (n + j) := by
  rw [mem_coneSet]
  constructor
  · rintro (rfl | hc)
    · exact ⟨hj, Relation.ReflTransGen.refl⟩
    · exact ⟨by have := inCone_lt n C i j hc; omega, inCone_coneRtg j i hc⟩
  · rintro ⟨_, hr⟩
    by_cases hij : i = j
    · left; exact hij
    · right
      have := coneRtg_inCone hRB (n + i) (n + j) hr (by omega) (by omega)
      simpa using this

theorem coneRd_reach_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (w : ℕ) (hw : w ≠ n + j) :
    Relation.ReflTransGen (coneRd n C) w (n + j) ↔
      ∃ i ∈ PEqualNP.Core.coneSet n C j, w ∈ (gateAt C i).inputs := by
  constructor
  · intro h
    rcases h.cases_head with h | ⟨c, hc, hcJ⟩
    · exact absurd h hw
    · refine ⟨c - n, ?_, hc.2.2⟩
      rw [coneSet_iff_rtg hRB hj]
      refine ⟨by have := hc.2.1; omega, ?_⟩
      have e : n + (c - n) = c := by have := hc.1; omega
      rw [e]; exact hcJ
  · rintro ⟨i, hiK, hwi⟩
    have hh := (coneSet_iff_rtg hRB hj i).mp hiK
    exact Relation.ReflTransGen.head (coneRd_of_input hh.1 hwi) hh.2

-- FRAGMENT restrict    DEPENDS: fold mono
-- Dropping a set S of gates that no kept gate reads (S read-closed), with renumbering of the kept wires
-- (rows 2774, 3312). Reading back with an offset (RBo) for gate lists built piece by piece.
-- Abbreviation: hcl = for all k < C.gates.length, k not in S -> for all i in (gateAt C k).inputs, i < n or i - n not in S.
-- Exports:
--   def RBo b gs : for all p < gs.length, every input i of gs.getD p (OR of nothing) has i < b + p
--       (RBo n C.gates is ReadsBack n C by unfolding; RBo n D.gates proves the ReadsBack part of IsAO2 n D)
--   RBo_nil b ;  RBo_cons (all inputs of g below b) (RBo (b + 1) gs) : RBo b (g :: gs)
--   RBo_append (RBo b g1) (RBo (b + g1.length) g2) : RBo b (g1 ++ g2)
--   def keepL S m := (List.range m).filter (not in S) ;  def rk S m := (keepL S m).length (new index of old gate m)
--   def rn n S w := if w < n then w else n + rk S (w - n)  (new wire of old wire w)
--   def mkG n C S j := gate j with inputs mapped by rn n S ;  def Dg n C S m := (keepL S m).map (mkG n C S)
--   keepL_succ_in / keepL_succ_out, Dg_succ_in (m in S) : Dg (m+1) = Dg m ;  Dg_succ_out : Dg (m+1) = Dg m ++ [mkG m]
--   rk_mono (a <= b) : rk S a <= rk S b ;  rk_lt (j < m) (j not in S) : rk S j < rk S m ;  rk_succ_out (m not in S) : rk S (m+1) = rk S m + 1
--   rn_lt (i < n + m) (i < n or i - n not in S) : rn n S i < n + rk S m ;  rn_gate : rn n S (n + o) = n + rk S o
--   Dg_len : (Dg n C S m).length = rk S m ;  keep_gate : j in keepL S C.gates.length -> gateAt C j in C.gates
--   restrict_val (ReadsBack n C) hcl (x.length = n) : for m <= len, (W (Dg n C S m) x).length = n + rk S m and
--       for every w < n + m with (w < n or w - n not in S), (W (Dg n C S m) x).getD (rn n S w) false = val C x w
--   restrict_rb (ReadsBack n C) hcl : m <= len -> RBo n (Dg n C S m)
--   restrict_size (all j in S below len) : (Dg n C S C.gates.length).length + S.card <= C.gates.length
--   restrict_circ (IsAO2 n C) hcl (S below len) (o < len, o not in S, C.output = n + o) :
--       exists D, IsAO2 n D and circuitFun n D = circuitFun n C and D.size + S.card <= C.size
--       (D = the circuit with gates Dg n C S C.gates.length and output n + rk S o)
-- Use: pick the dead set S, prove hcl, then restrict_circ; for other gate shapes use restrict_val / restrict_rb directly
-- (keep_gate transports per-gate properties such as op or fan-in). For S = gates outside the output cone see frag live.

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

-- FRAGMENT live    DEPENDS: fold mono cones restrict
-- Liveness (PEqualNP.FactorSubst.liveGates / liveSize): the gates in the cone of the output gate, and the live
-- circuit liveCirc n C = C restricted to them (frag restrict with S = deadSet), from row 3312.
-- Abbreviation: LG = PEqualNP.FactorSubst.liveGates n C, LS = PEqualNP.FactorSubst.liveSize n C = LG.card.
-- Exports:
--   mem_liveGates : j in LG iff j < C.gates.length and n <= C.output and (j = C.output - n or InCone n C j (C.output - n))
--   def deadSet n C := (Finset.range C.gates.length).filter (not in LG) ;  mem_deadSet : j in deadSet iff j < len and j not in LG
--   live_closed (ReadsBack n C) : the read-closure hypothesis hcl of frag restrict for S = deadSet n C
--   keepL_dead_mem : j in keepL (deadSet n C) C.gates.length iff j in LG
--   dead_size : (Dg n C (deadSet n C) C.gates.length).length = LS
--   liveSize_zero (not (n <= C.output and C.output - n < len)) : LS = 0
--   liveSize_le : LS <= C.gates.length ;  output_live (n <= C.output < n + len) : C.output - n in LG
--   def liveCirc n C : if the output is a gate then (Dg n C deadSet len, output n + rk deadSet (C.output - n)) else ([], C.output)
--   liveCirc_isAO2 : IsAO2 n C -> IsAO2 n (liveCirc n C) ;  liveCirc_size : (liveCirc n C).size = LS
--   liveCirc_val (IsAO2 n C) x : CleanedNonEdge.wireVal n (liveCirc n C) (liveCirc n C).output x = wireVal n C C.output x
--   liveCirc_fun (IsAO2 n C) : circuitFun n (liveCirc n C) = circuitFun n C
--   liveCirc_gate (j < (liveCirc n C).gates.length) : exists i in LG, gateAt (liveCirc n C) j = mkG n C (deadSet n C) i
-- Use: liveCirc gives a circuit of size liveSize computing the same function (rows asking for D.size = liveSize);
-- for a hypothesis about LG elements use mem_liveGates with the cones lemmas (inCone_iff, inCone_trans).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem mem_liveGates (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ PEqualNP.FactorSubst.liveGates n C ↔ j < C.gates.length ∧ n ≤ C.output ∧
      (j = C.output - n ∨ PEqualNP.EdgeOwnership.InCone n C j (C.output - n)) := by
  unfold PEqualNP.FactorSubst.liveGates
  rw [Finset.mem_filter, Finset.mem_range]

def deadSet (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => j ∉ PEqualNP.FactorSubst.liveGates n C)

theorem mem_deadSet (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ deadSet n C ↔ j < C.gates.length ∧ j ∉ PEqualNP.FactorSubst.liveGates n C := by
  unfold deadSet
  rw [Finset.mem_filter, Finset.mem_range]

theorem live_closed (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) :
    ∀ k < C.gates.length, k ∉ deadSet n C →
      ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ deadSet n C := by
  intro k hk hkS i hi
  have hkL : k ∈ PEqualNP.FactorSubst.liveGates n C := by
    by_contra hno
    exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hno⟩)
  by_cases hin : i < n
  · exact Or.inl hin
  · right
    intro hd
    apply (Finset.mem_filter.mp hd).2
    obtain ⟨_, hno, hc⟩ := (mem_liveGates n C k).mp hkL
    have hilt : i < n + k := hRB k hk i hi
    have hc1 : PEqualNP.EdgeOwnership.InCone n C (i - n) k :=
      inCone_of_read n C (i - n) k hk (by omega)
        (by rw [show n + (i - n) = i by omega]; exact hi)
    rw [mem_liveGates]
    refine ⟨by omega, hno, Or.inr ?_⟩
    rcases hc with e | e
    · rw [← e]; exact hc1
    · exact inCone_trans n C (i - n) k hc1 _ e

theorem keepL_dead_mem (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ keepL (deadSet n C) C.gates.length ↔ j ∈ PEqualNP.FactorSubst.liveGates n C := by
  constructor
  · intro h
    have h' := List.mem_filter.mp h
    have hj : j < C.gates.length := List.mem_range.mp h'.1
    have hd : j ∉ deadSet n C := by
      intro hd
      have h2 := h'.2
      simp [hd] at h2
    by_contra hno
    exact hd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hno⟩)
  · intro h
    have hj : j < C.gates.length := ((mem_liveGates n C j).mp h).1
    have hd : j ∉ deadSet n C := fun hd => (Finset.mem_filter.mp hd).2 h
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hj, ?_⟩
    simp [hd]

theorem dead_size (n : ℕ) (C : Circuit) :
    (Dg n C (deadSet n C) C.gates.length).length = PEqualNP.FactorSubst.liveSize n C := by
  rw [Dg_len]
  unfold rk PEqualNP.FactorSubst.liveSize
  have hnd : (keepL (deadSet n C) C.gates.length).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext j
  rw [List.mem_toFinset]
  exact keepL_dead_mem n C j

theorem liveSize_le (n : ℕ) (C : Circuit) : PEqualNP.FactorSubst.liveSize n C ≤ C.gates.length := by
  unfold PEqualNP.FactorSubst.liveSize PEqualNP.FactorSubst.liveGates
  exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])

theorem output_live (n : ℕ) (C : Circuit) (h1 : n ≤ C.output) (h2 : C.output < n + C.gates.length) :
    C.output - n ∈ PEqualNP.FactorSubst.liveGates n C :=
  (mem_liveGates n C _).mpr ⟨by omega, h1, Or.inl rfl⟩

theorem liveSize_zero (n : ℕ) (C : Circuit)
    (h : ¬ (n ≤ C.output ∧ C.output - n < C.gates.length)) :
    PEqualNP.FactorSubst.liveSize n C = 0 := by
  unfold PEqualNP.FactorSubst.liveSize
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro j hj
  obtain ⟨hj1, hno, hc⟩ := (mem_liveGates n C j).mp hj
  rcases hc with e | e
  · exact h ⟨hno, by omega⟩
  · exact h ⟨hno, (inCone_lt n C j _ e).2⟩

def liveCirc (n : ℕ) (C : Circuit) : Circuit :=
  if n ≤ C.output ∧ C.output - n < C.gates.length then
    ⟨Dg n C (deadSet n C) C.gates.length, n + rk (deadSet n C) (C.output - n)⟩
  else ⟨[], C.output⟩

theorem liveCirc_gate (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < (liveCirc n C).gates.length) :
    ∃ i ∈ PEqualNP.FactorSubst.liveGates n C, gateAt (liveCirc n C) j = mkG n C (deadSet n C) i := by
  unfold liveCirc at hj ⊢
  split_ifs at hj ⊢ with hc
  · have hj' : j < ((keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C))).length := hj
    rw [List.length_map] at hj'
    refine ⟨(keepL (deadSet n C) C.gates.length)[j],
      (keepL_dead_mem n C _).mp (List.getElem_mem hj'), ?_⟩
    show (Dg n C (deadSet n C) C.gates.length).getD j ⟨GateOp.or, []⟩ = _
    unfold Dg
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]
  · exact absurd hj (by simp)

theorem liveCirc_isAO2 (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (liveCirc n C) := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  unfold liveCirc
  split_ifs with hc
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      have hg' : g ∈ (keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C)) := hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
      exact hao (gateAt C j) (keep_gate C _ j hj)
    · exact restrict_rb n C _ hRB (live_closed n C hRB) _ le_rfl
    · intro g hg
      have hg' : g ∈ (keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C)) := hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
      have := h2 _ (keep_gate C _ j hj)
      show ((gateAt C j).inputs.map (rn n (deadSet n C))).length = 2
      rw [List.length_map]
      exact this
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact absurd hg (by simp)
    · intro j hj
      exact absurd hj (by simp)
    · intro g hg
      exact absurd hg (by simp)

theorem liveCirc_size (n : ℕ) (C : Circuit) :
    (liveCirc n C).size = PEqualNP.FactorSubst.liveSize n C := by
  unfold liveCirc
  split_ifs with hc
  · exact dead_size n C
  · rw [liveSize_zero n C hc]
    rfl

theorem liveCirc_val (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n (liveCirc n C) (liveCirc n C).output x =
      PEqualNP.CleanedNonEdge.wireVal n C C.output x := by
  have hRB := hAO.2.1
  unfold liveCirc
  split_ifs with hc
  · obtain ⟨hno, hlt⟩ := hc
    have hoL : C.output - n ∉ deadSet n C := fun hd =>
      (Finset.mem_filter.mp hd).2 ((mem_liveGates n C _).mpr ⟨hlt, hno, Or.inl rfl⟩)
    have h := (restrict_val n C (deadSet n C) hRB (live_closed n C hRB) (List.ofFn x) (by simp)
      C.gates.length le_rfl).2 C.output (by omega) (Or.inr hoL)
    have e3 : rn n (deadSet n C) C.output = n + rk (deadSet n C) (C.output - n) := by
      unfold rn
      rw [if_neg (by omega)]
    rw [e3] at h
    exact h
  · show (List.ofFn x).getD C.output false = (W C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n
    · rw [W_prefix C.gates (List.ofFn x) C.output (by rw [List.length_ofFn]; exact hlt)]
    · have h1 : n + C.gates.length ≤ C.output := by
        by_contra h0
        exact hc ⟨by omega, by omega⟩
      rw [getD_ge _ _ (by rw [List.length_ofFn]; omega),
        W_ge C.gates (List.ofFn x) C.output (by rw [List.length_ofFn]; omega)]

theorem liveCirc_fun (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    circuitFun n (liveCirc n C) = circuitFun n C := by
  funext x
  exact liveCirc_val n C hAO x

theorem nm_gate (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (out b : ℕ)
    (hb : b < C.gates.length) :
    gateAt (⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)), out⟩ : Circuit) (G0.length + b) =
      ⟨(gateAt C b).op, (gateAt C b).inputs.map (rho b)⟩ := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_mapIdx,
    List.getElem?_eq_getElem hb]
  simp

def nmR (n : ℕ) (C : Circuit) (m : ℕ) (u : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (rho : ℕ → ℕ → ℕ)
    (L : ℕ) (a13 b13 : ℕ) : Prop :=
  a13 < b13 ∧ b13 < C.gates.length ∧ ((n + a13 ∈ (gateAt C b13).inputs ∧
    ¬ ∃ k13 < m, a13 = u k13 ∧ NR k13 b13) ∨ ∃ k14 < m, NR k14 b13 ∧ rho b13 (n + u k14) = n + L + a13)

theorem nm_U (n : ℕ) (C D : Circuit) (m : ℕ) (u : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (G0 : List Gate)
    (rho : ℕ → ℕ → ℕ) (hRB : ReadsBack n C)
    (hDg : ∀ b < C.gates.length, gateAt D (G0.length + b) =
      ⟨(gateAt C b).op, (gateAt C b).inputs.map (rho b)⟩)
    (hDlen : D.gates.length = G0.length + C.gates.length)
    (hr8 : ∀ r8 < C.gates.length, ∀ i8 ∈ (gateAt C r8).inputs,
      (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length)
    (x : Fin n → Bool) : ∀ b, b < C.gates.length →
      (∀ k < m, ∀ r, NR k r → r ≠ b ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r b) →
      val D (List.ofFn x) (n + (G0.length + b)) = val C (List.ofFn x) (n + b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb hfree
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [val_gate hlen (show G0.length + b < D.gates.length by omega), val_gate hlen hb, hDg b hb]
    dsimp only
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    have hrb : i < n + b := hRB b hb i hi
    have hnn : ∀ k8 < m, ¬ (NR k8 b ∧ i = n + u k8) := fun k8 hk8 h => (hfree k8 hk8 b h.1).1 rfl
    rw [hr8 b hb i hi hnn, if_pos hrb]
    by_cases hin : i < n
    · rw [if_pos hin, if_pos (show i < n + (G0.length + b) by omega), val_input hlen hin,
        val_input hlen hin]
    · rw [if_neg hin, if_pos (show i + G0.length < n + (G0.length + b) by omega)]
      obtain ⟨a, rfl⟩ : ∃ a, i = n + a := ⟨i - n, by omega⟩
      rw [show n + a + G0.length = n + (G0.length + a) by omega]
      apply ih a (by omega) (by omega)
      intro k hk r hr
      obtain ⟨h1, h2⟩ := hfree k hk r hr
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact h2 (inCone_of_read n C r b hb (by omega) hi)
      · intro hc
        exact h2 (inCone_trans n C _ _ hc b (inCone_of_read n C a b hb (by omega) hi))

theorem nm_read (n : ℕ) (C D : Circuit) (m : ℕ) (u : ℕ → ℕ) (NR : ℕ → ℕ → Prop)
    (P : ℕ → (Fin n → Bool) → Bool) (G0 : List Gate)
    (rho : ℕ → ℕ → ℕ) (hRB : ReadsBack n C)
    (hDg : ∀ b < C.gates.length, gateAt D (G0.length + b) =
      ⟨(gateAt C b).op, (gateAt C b).inputs.map (rho b)⟩)
    (hDlen : D.gates.length = G0.length + C.gates.length)
    (hDgs : ∃ M : List Gate, D.gates = G0 ++ M)
    (hr8 : ∀ r8 < C.gates.length, ∀ i8 ∈ (gateAt C r8).inputs,
      (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length)
    (hr9 : ∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9)))
    (x : Fin n → Bool) : ∀ k < m, ∀ b < C.gates.length, NR k b →
      (if rho b (n + u k) < n + (G0.length + b) then val D (List.ofFn x) (rho b (n + u k))
        else false) = P k x := by
  intro k hk b hb hnr
  rcases hr9 b k hk hnr with ⟨hlt, hv⟩ | ⟨g9, hg9, he, hv, hfree⟩ | ⟨hv, hge⟩
  · rw [if_pos (show rho b (n + u k) < n + (G0.length + b) by omega), ← hv x]
    obtain ⟨M, hM⟩ := hDgs
    show (W D.gates (List.ofFn x)).getD _ false = (W G0 (List.ofFn x)).getD _ false
    rw [hM, W_append]
    exact W_prefix _ _ _ (by rw [W_length, List.length_ofFn]; omega)
  · rw [he, if_pos (show n + G0.length + g9 < n + (G0.length + b) by omega),
      show n + G0.length + g9 = n + (G0.length + g9) by omega,
      nm_U n C D m u NR G0 rho hRB hDg hDlen hr8 x g9 (by omega) hfree, ← hv x]
    rfl
  · rw [if_neg (show ¬ rho b (n + u k) < n + (G0.length + b) by omega), hv x]

theorem nm_M (n : ℕ) (C D : Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop)
    (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hNR : ∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (gateAt C r0).inputs ∧
      (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (gateAt C r0).op = GateOp.or)))
    (hT : ∀ k < m, T k < C.gates.length ∧ (gateAt C (T k)).op = GateOp.and ∧ z k < n ∧
      ((gateAt C (T k)).inputs = [W k, z k] ∨ (gateAt C (T k)).inputs = [z k, W k]))
    (hO : ∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 →
      (gateAt C g3).op = GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 →
      C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (gateAt C r3).inputs → r3 = T k3 ∨
        (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (gateAt C r3).op = GateOp.or))
    (hDg : ∀ b < C.gates.length, gateAt D (G0.length + b) =
      ⟨(gateAt C b).op, (gateAt C b).inputs.map (rho b)⟩)
    (hDlen : D.gates.length = G0.length + C.gates.length)
    (hr8 : ∀ r8 < C.gates.length, ∀ i8 ∈ (gateAt C r8).inputs,
      (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length)
    (R : Bool → Bool → Prop) (hR : OpMono R) (xD xC : Fin n → Bool) (K : ℕ → Prop)
    (hinH : ∀ i < n, R (val D (List.ofFn xD) i) (val C (List.ofFn xC) i))
    (hnarH : ∀ k < m, ¬ K k → ∀ b < C.gates.length, NR k b →
      R (if rho b (n + u k) < n + (G0.length + b) then val D (List.ofFn xD) (rho b (n + u k))
        else false) (val C (List.ofFn xC) (n + u k)))
    (hkill : ∀ k < m, K k → ∀ a c : Bool,
      R (a && val D (List.ofFn xD) (z k)) (c && val C (List.ofFn xC) (z k)) ∧
      R (val D (List.ofFn xD) (z k) && a) (val C (List.ofFn xC) (z k) && c)) :
    ∀ b, b < C.gates.length →
      (R (val D (List.ofFn xD) (n + (G0.length + b))) (val C (List.ofFn xC) (n + b)) ∨
        ∃ k < m, K k ∧ PEqualNP.CleanedNonEdge.OrReaches n C (W k) b ∧
          (gateAt C b).op = GateOp.or ∧ PEqualNP.EdgeOwnership.InCone n C (u k) b) := by
  have hRB : ReadsBack n C := hAO.2.1
  have hlD : (List.ofFn xD).length = n := List.length_ofFn
  have hlC : (List.ofFn xC).length = n := List.length_ofFn
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    by_cases hA : ∃ k < m, K k ∧ b = T k
    · left
      obtain ⟨k, hk, hK, rfl⟩ := hA
      obtain ⟨hTl, hop, hz, hinp⟩ := hT k hk
      have hzin : z k ∈ (gateAt C (T k)).inputs := by
        rcases hinp with h | h <;> rw [h] <;> simp
      have hzr : rho (T k) (z k) = z k := by
        rw [hr8 (T k) hTl (z k) hzin (fun k8 hk8 h => by have := h.2; omega), if_pos hz]
      have hz1 : z k < n + (G0.length + T k) := by omega
      have hz2 : z k < n + T k := by omega
      rw [val_gate hlD (show G0.length + T k < D.gates.length by omega), val_gate hlC hTl,
        hDg (T k) hTl]
      dsimp only
      rw [hop]
      rcases hinp with h | h <;> rw [h] <;>
        simp only [List.map_cons, List.map_nil, hzr, eval_and2] <;>
        rw [if_pos hz1, if_pos hz2]
      · exact (hkill k hk hK _ _).1
      · exact (hkill k hk hK _ _).2
    · by_cases hB : ∃ k < m, K k ∧ NR k b
      · right
        obtain ⟨k, hk, hK, hnr⟩ := hB
        obtain ⟨-, hin, hor⟩ := (hNR k b).mp hnr
        rcases hor with e | ⟨hor, hop⟩
        · exact absurd ⟨k, hk, hK, e⟩ hA
        · exact ⟨k, hk, hK, hor, hop,
            inCone_of_read n C (u k) b hb (by have := hRB b hb _ hin; omega) hin⟩
      · by_cases hCc : ∃ a, a < b ∧ n + a ∈ (gateAt C b).inputs ∧ ∃ k < m, K k ∧
            PEqualNP.CleanedNonEdge.OrReaches n C (W k) a ∧ (gateAt C a).op = GateOp.or ∧
            PEqualNP.EdgeOwnership.InCone n C (u k) a
        · right
          obtain ⟨a, hab, hain, k, hk, hK, hor, hop, hcone⟩ := hCc
          obtain ⟨-, hrd⟩ := hO k hk a (by omega) hor hop hcone
          rcases hrd b hb hain with e | ⟨hor', hop'⟩
          · exact absurd ⟨k, hk, hK, e⟩ hA
          · exact ⟨k, hk, hK, hor', hop',
              inCone_trans n C _ _ hcone b (inCone_of_read n C a b hb hab hain)⟩
        · left
          rw [val_gate hlD (show G0.length + b < D.gates.length by omega), val_gate hlC hb,
            hDg b hb]
          dsimp only
          rw [List.map_map]
          apply hR _ (hAO.1 _ (gateAt_mem hb))
          intro i hi
          simp only [Function.comp_apply]
          have hrb : i < n + b := hRB b hb i hi
          rw [if_pos hrb]
          by_cases hnar : ∃ k < m, NR k b ∧ i = n + u k
          · obtain ⟨k, hk, hnr, rfl⟩ := hnar
            exact hnarH k hk (fun hK => hB ⟨k, hk, hK, hnr⟩) b hb hnr
          · have hnn : ∀ k8 < m, ¬ (NR k8 b ∧ i = n + u k8) :=
              fun k8 hk8 h => hnar ⟨k8, hk8, h⟩
            rw [hr8 b hb i hi hnn]
            by_cases hin : i < n
            · rw [if_pos hin, if_pos (show i < n + (G0.length + b) by omega)]
              exact hinH i hin
            · rw [if_neg hin, if_pos (show i + G0.length < n + (G0.length + b) by omega)]
              obtain ⟨a, rfl⟩ : ∃ a, i = n + a := ⟨i - n, by omega⟩
              rcases ih a (by omega) (by omega) with h | ⟨k, hk, hK, hor, hop, hcone⟩
              · rw [show n + a + G0.length = n + (G0.length + a) by omega]
                exact h
              · exact absurd ⟨a, by omega, hi, k, hk, hK, hor, hop, hcone⟩ hCc

theorem nm_out (n : ℕ) (C D : Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop)
    (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hNR : ∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (gateAt C r0).inputs ∧
      (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (gateAt C r0).op = GateOp.or)))
    (hT : ∀ k < m, T k < C.gates.length ∧ (gateAt C (T k)).op = GateOp.and ∧ z k < n ∧
      ((gateAt C (T k)).inputs = [W k, z k] ∨ (gateAt C (T k)).inputs = [z k, W k]))
    (hO : ∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 →
      (gateAt C g3).op = GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 →
      C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (gateAt C r3).inputs → r3 = T k3 ∨
        (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (gateAt C r3).op = GateOp.or))
    (hDg : ∀ b < C.gates.length, gateAt D (G0.length + b) =
      ⟨(gateAt C b).op, (gateAt C b).inputs.map (rho b)⟩)
    (hDlen : D.gates.length = G0.length + C.gates.length)
    (hDout : D.output = if C.output < n then C.output else C.output + G0.length)
    (hr8 : ∀ r8 < C.gates.length, ∀ i8 ∈ (gateAt C r8).inputs,
      (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length)
    (R : Bool → Bool → Prop) (hR : OpMono R) (hRff : R false false)
    (xD xC : Fin n → Bool) (K : ℕ → Prop)
    (hinH : ∀ i < n, R (val D (List.ofFn xD) i) (val C (List.ofFn xC) i))
    (hnarH : ∀ k < m, ¬ K k → ∀ b < C.gates.length, NR k b →
      R (if rho b (n + u k) < n + (G0.length + b) then val D (List.ofFn xD) (rho b (n + u k))
        else false) (val C (List.ofFn xC) (n + u k)))
    (hkill : ∀ k < m, K k → ∀ a c : Bool,
      R (a && val D (List.ofFn xD) (z k)) (c && val C (List.ofFn xC) (z k)) ∧
      R (val D (List.ofFn xD) (z k) && a) (val C (List.ofFn xC) (z k) && c)) :
    R (val D (List.ofFn xD) D.output) (val C (List.ofFn xC) C.output) := by
  have hM := nm_M n C D m u T W z NR G0 rho hAO hNR hT hO hDg hDlen hr8 R hR xD xC K hinH hnarH hkill
  have hlD : (List.ofFn xD).length = n := List.length_ofFn
  have hlC : (List.ofFn xC).length = n := List.length_ofFn
  rw [hDout]
  by_cases h1 : C.output < n
  · rw [if_pos h1]; exact hinH _ h1
  · rw [if_neg h1]
    by_cases h2 : C.output < n + C.gates.length
    · obtain ⟨b, hbe⟩ : ∃ b, C.output = n + b := ⟨C.output - n, by omega⟩
      have hb : b < C.gates.length := by omega
      rw [show C.output + G0.length = n + (G0.length + b) by omega, hbe]
      rcases hM b hb with h | ⟨k, hk, -, hor, hop, hcone⟩
      · exact h
      · exact absurd hbe (hO k hk b hb hor hop hcone).1
    · rw [val_ge hlD (show n + D.gates.length ≤ C.output + G0.length by omega),
        val_ge hlC (show n + C.gates.length ≤ C.output by omega)]
      exact hRff

theorem nm_opMono_rev : OpMono (fun a b => b = true → a = true) :=
  fun op hop l f g h => opMono_imp op hop l g f h

theorem main_aux : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hq hAO hC hNR hP hpair hO hU hG0 hD hr8 hr9 y12
  have hRB : ReadsBack n C := hAO.2.1
  have hDlen : D.gates.length = G0.length + C.gates.length := by subst hD; simp
  have hDout : D.output = if C.output < n then C.output else C.output + G0.length := by
    subst hD; rfl
  have hDg : ∀ b < C.gates.length, gateAt D (G0.length + b) =
      ⟨(gateAt C b).op, (gateAt C b).inputs.map (rho b)⟩ := by
    intro b hb; subst hD; exact nm_gate C G0 rho _ b hb
  have hDgs : ∃ M : List Gate, D.gates = G0 ++ M := ⟨_, by subst hD; rfl⟩
  have hT : ∀ k < m, T k < C.gates.length ∧ (gateAt C (T k)).op = GateOp.and ∧ z k < n ∧
      ((gateAt C (T k)).inputs = [W k, z k] ∨ (gateAt C (T k)).inputs = [z k, W k]) :=
    fun k hk => ⟨(hpair k hk).2.1, (hpair k hk).2.2.1, (hpair k hk).2.2.2.1,
      (hpair k hk).2.2.2.2.1⟩
  have hread := nm_read n C D m u NR P G0 rho hRB hDg hDlen hDgs hr8 hr9
  have hlen : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => List.length_ofFn
  -- upper bound
  have hup : D.eval (List.ofFn y12) = true → qH y12 = true := by
    intro h
    have hout := nm_out n C D m u T W z NR G0 rho hAO hNR hT hO hDg hDlen hDout hr8
      (fun a b => a = true → b = true) opMono_imp (fun h => h) y12 y12
      (fun k => val C (List.ofFn y12) (z k) = false)
      (by
        intro i hi hv
        rw [val_input (hlen y12) hi] at hv ⊢
        exact hv)
      (by
        intro k hk hK b hb hnr
        rw [hread y12 k hk b hb hnr]
        intro hPk
        rw [hP] at hPk
        obtain ⟨w, hw, hu⟩ := of_decide_eq_true hPk
        have hz : z k < n := (hT k hk).2.2.1
        have hzt : y12 ⟨z k, hz⟩ = true := by
          rw [← val_ofFn_lt C y12 (z k) hz]
          cases hv : val C (List.ofFn y12) (z k)
          · exact absurd hv hK
          · rfl
        apply mono n C (andOrOnly_of_isAO2 hAO) _ y12 _ (n + u k) hu
        intro i hi
        rcases of_decide_eq_true hi with e | e
        · rw [e]; exact hw
        · have : i = ⟨z k, hz⟩ := Fin.ext e
          rw [this]; exact hzt)
      (by
        intro k hk hK a c
        have hz : z k < n := (hT k hk).2.2.1
        have e : val D (List.ofFn y12) (z k) = false := by
          rw [val_input (hlen y12) hz]; rw [val_input (hlen y12) hz] at hK; exact hK
        refine ⟨?_, ?_⟩ <;> simp [e, hK])
    rw [← hC y12]
    exact hout h
  -- lower bound
  have hlow : qH y12 = true → D.eval (List.ofFn y12) = true := by
    intro hqt
    obtain ⟨a0, b0, hadj, ha, hb⟩ := (hq y12).mp hqt
    obtain ⟨x0, hx0⟩ : ∃ x0 : Fin n → Bool, x0 = fun j => decide (j = a0 ∨ j = b0) := ⟨_, rfl⟩
    have hx0q : qH x0 = true := (hq x0).mpr ⟨a0, b0, hadj, by simp [hx0], by simp [hx0]⟩
    have hC0 : C.eval (List.ofFn x0) = true := by rw [hC]; exact hx0q
    have hout := nm_out n C D m u T W z NR G0 rho hAO hNR hT hO hDg hDlen hDout hr8
      (fun a b => b = true → a = true) nm_opMono_rev (fun h => h) y12 x0
      (fun k => val C (List.ofFn x0) (z k) = false)
      (by
        intro i hi hv
        rw [val_ofFn_lt C x0 i hi] at hv
        rw [val_ofFn_lt D y12 i hi]
        rw [hx0] at hv
        rcases of_decide_eq_true hv with e | e
        · rw [e]; exact ha
        · rw [e]; exact hb)
      (by
        intro k hk hK b hb' hnr
        rw [hread y12 k hk b hb' hnr]
        intro hu
        rw [hP]
        apply decide_eq_true
        have hz : z k < n := (hT k hk).2.2.1
        have hzt : x0 ⟨z k, hz⟩ = true := by
          rw [← val_ofFn_lt C x0 (z k) hz]
          cases hv : val C (List.ofFn x0) (z k)
          · exact absurd hv hK
          · rfl
        rw [hx0] at hzt
        rcases of_decide_eq_true hzt with e | e
        · refine ⟨b0, hb, ?_⟩
          have hzv : z k = (a0 : ℕ) := by rw [← e]
          have hfun : (fun j1 : Fin n => decide (j1 = b0 ∨ (j1 : ℕ) = z k)) = x0 := by
            funext j
            rw [hx0]
            by_cases h1 : j = a0 <;> by_cases h2 : j = b0 <;> simp [h1, h2, hzv, Fin.val_inj]
          rw [hfun]
          exact hu
        · refine ⟨a0, ha, ?_⟩
          have hzv : z k = (b0 : ℕ) := by rw [← e]
          have hfun : (fun j1 : Fin n => decide (j1 = a0 ∨ (j1 : ℕ) = z k)) = x0 := by
            funext j
            rw [hx0]
            by_cases h1 : j = a0 <;> by_cases h2 : j = b0 <;> simp [h1, h2, hzv, Fin.val_inj]
          rw [hfun]
          exact hu)
      (by
        intro k hk hK a c
        refine ⟨?_, ?_⟩ <;> simp [hK])
    exact hout hC0
  rw [Bool.eq_iff_iff]
  exact ⟨hup, hlow⟩

end PEqualNP.Outside.L_meta_3545

theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 :=
  PEqualNP.Outside.L_meta_3545.main_aux
