import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5535

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

-- FRAGMENT table1a    DEPENDS: fold mono
-- Table 1a rows: RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s, upper and lower bounds.
-- Profiles: the profile of a wire is the 16-bit Nat whose bit k is its value at input t1_inp k = oneEach (k / 4) (k % 4).
-- Every gate of a Monotone2 circuit has profile a AND b or a OR b of earlier profiles or the constants 0 and 65535,
-- so a circuit of at most s gates gives a chain of s such steps from t1_base reaching the target T; t1_reach
-- (a Bool search, evaluated by decide +kernel) checks that no such chain exists.
-- Exports:
--   def t1_bits (f : Nat -> Bool) (m) : Nat  (bit k is f k for k < m) ;  t1_bits_testBit : testBit (t1_bits f m) i = (decide (i < m) and f i)
--   t1_bits_ext (agree below m) ;  t1_bits_and / t1_bits_or : t1_bits of pointwise and / or = land / lor ;  t1_bits_false : t1_bits (fun _ => false) m = 0
--   def t1_inp k : List Bool := oneEach (k / 4 % 4) (k % 4) ;  t1_inp_len : (t1_inp k).length = 8
--   def t1_prof C w := t1_bits (fun k => val C (t1_inp k) w) 16 ;  def t1_base : the 10 base profiles (0, 65535, 4 rows, 4 columns)
--   def t1_St C j : t1_base with the profiles of gate wires 8 .. 8 + j - 1 pushed in front ;  def t1_Step S p : exists a b in S, p = a land b or p = a lor b
--   t1_St_prof : i < 8 + j -> t1_prof C i in t1_St C j ;  t1_gate_step : one AND / OR gate of fan-in at most 2 is a t1_Step
--   def t1_mem, t1_pany (pairs a b with a before or equal b), t1_one T S (T is one step from S), t1_reach T S r (T within r steps)
--   t1_reach_step : a, b in S, p = a op b, t1_reach T (p :: S) r -> t1_reach T S (r + 1) ;  t1_chain : chains of steps are found by t1_reach
--   t1_lower M s T (hT : t1_bits (fun k => M.testBit k) 16 = T) (hc : t1_reach T t1_base s = false) : not RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s
--   def t1_okop ;  t1_mono2 (h : C.gates.all (fun g => t1_okop g.op and decide (g.inputs.length <= 2)) = true) : Monotone2 C
-- Use: exact t1_lower 1023 3 1023 (by decide +kernel) (by decide +kernel)   (SP/tools/table1a.py writes whole files).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def t1_bits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Nat.bit (f 0) (t1_bits (fun i => f (i + 1)) m)

theorem t1_bits_testBit (m : ℕ) : ∀ (f : ℕ → Bool) (i : ℕ),
    (t1_bits f m).testBit i = (decide (i < m) && f i) := by
  induction m with
  | zero => intro f i; simp [t1_bits]
  | succ m ih =>
    intro f i
    cases i with
    | zero => simp [t1_bits, Nat.testBit_bit_zero]
    | succ i =>
      have e : (t1_bits f (m + 1)).testBit (i + 1) = (t1_bits (fun i => f (i + 1)) m).testBit i :=
        Nat.testBit_bit_succ i _ _
      rw [e, ih]
      simp

theorem t1_bits_ext {f g : ℕ → Bool} {m : ℕ} (h : ∀ k, k < m → f k = g k) :
    t1_bits f m = t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [t1_bits_testBit, t1_bits_testBit]
  by_cases hi : i < m
  · rw [h i hi]
  · simp [hi]

theorem t1_bits_and (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i && g i) m = t1_bits f m &&& t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_or (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i || g i) m = t1_bits f m ||| t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_false (m : ℕ) : t1_bits (fun _ => false) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [t1_bits_testBit]

theorem t1_bits_true16 : t1_bits (fun _ => true) 16 = 65535 := by decide

theorem t1_land_comm (a b : ℕ) : a &&& b = b &&& a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_comm (a b : ℕ) : a ||| b = b ||| a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_land_absl (a b : ℕ) : a &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_land_absr (a b : ℕ) : b &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_absl (a b : ℕ) : a ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_absr (a b : ℕ) : b ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl


-- Mask 375: rows 0 and 1 meet columns 0, 1, 2; row 2 meets column 0; row 3 and column 3 are empty.
-- Profiles on 18 test inputs: k < 16 is the one-each input (k / 4 % 4, k % 4), 16 has only wire 0 on,
-- 17 has only wire 4 on.  A circuit of at most s gates gives a chain of s AND / OR steps from q_base.
-- Every profile in the chain is monotone on the pairs (16, 3) and (17, 12).  The output depends on each
-- of the six wires 0, 1, 2, 4, 5, 6 (a pair of test inputs that differ only there), dependence passes
-- through AND and OR only from an input, so a backward count over the chain leaves a read-once merge of
-- the six wire profiles into the output; srch checks every such merge.

def q_inp (k : ℕ) : List Bool :=
  if k = 16 then [true, false, false, false, false, false, false, false]
  else if k = 17 then [false, false, false, false, true, false, false, false]
  else PEqualNP.Represents.oneEach (n := 4) (m := 4) ⟨k / 4 % 4, by omega⟩ ⟨k % 4, by omega⟩

theorem q_inp_len (k : ℕ) : (q_inp k).length = 8 := by
  unfold q_inp
  split_ifs <;> simp [PEqualNP.Represents.oneEach]

def q_prof (C : Circuit) (w : ℕ) : ℕ := t1_bits (fun k => val C (q_inp k) w) 18

def q_base : List ℕ := [0, 262143, 65551, 240, 3840, 61440, 135441, 8738, 17476, 34952]

theorem q_base_ok : ∀ u, u < 8 → t1_bits (fun k => (q_inp k).getD u false) 18 ∈ q_base := by
  decide +kernel

theorem t1_bits_true18 : t1_bits (fun _ => true) 18 = 262143 := by decide

def q_St (C : Circuit) : ℕ → List ℕ
  | 0 => q_base
  | j + 1 => q_prof C (8 + j) :: q_St C j

def q_Step (S : List ℕ) (p : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, p = a &&& b ∨ p = a ||| b

theorem q_St_base (C : Circuit) {x : ℕ} (hx : x ∈ q_base) (j : ℕ) : x ∈ q_St C j := by
  induction j with
  | zero => exact hx
  | succ j ih => exact List.mem_cons_of_mem _ ih

theorem q_St_prof (C : Circuit) (j : ℕ) : ∀ i, i < 8 + j → q_prof C i ∈ q_St C j := by
  induction j with
  | zero =>
    intro i hi
    have e : q_prof C i = t1_bits (fun k => (q_inp k).getD i false) 18 := by
      unfold q_prof
      congr 1
      funext k
      exact val_input (q_inp_len k) (by omega)
    rw [e]
    exact q_base_ok i (by omega)
  | succ j ih =>
    intro i hi
    by_cases h : i < 8 + j
    · exact List.mem_cons_of_mem _ (ih i h)
    · have e : i = 8 + j := by omega
      subst e
      simp [q_St]

theorem q_gate_step (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) 18 ∈ S) (h0 : 0 ∈ S) (h1 : 262143 ∈ S) :
    q_Step S (t1_bits (fun k => op.eval (l.map (R k))) 18) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_true18]
      exact ⟨262143, h1, 262143, h1, Or.inl (by decide)⟩
    · have e : (fun k => GateOp.or.eval (([] : List ℕ).map (R k))) = fun _ => false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_false]
      exact ⟨0, h0, 0, h0, Or.inr (by decide)⟩
  · have ha := hR a (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a].map (R k))) = fun k => R k a && true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and, t1_bits_true18]
      exact ⟨_, ha, 262143, h1, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a].map (R k))) = fun k => R k a || false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or, t1_bits_false]
      exact ⟨_, ha, 0, h0, Or.inr rfl⟩
  · have ha := hR a (by simp)
    have hb := hR b (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a, b].map (R k))) = fun k => R k a && R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and]
      exact ⟨_, ha, _, hb, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a, b].map (R k))) = fun k => R k a || R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or]
      exact ⟨_, ha, _, hb, Or.inr rfl⟩
  · simp only [List.length_cons] at hl
    omega

-- dependence pairs (one per needed wire) and the wire profiles, in the same order
def q_pv : List ((ℕ × ℕ) × ℕ) :=
  [((0, 17), 65551), ((4, 17), 240), ((8, 17), 3840), ((0, 16), 135441), ((1, 16), 8738), ((2, 16), 17476)]

def q_vars : List ℕ := [65551, 240, 3840, 135441, 8738, 17476]

def q_dif (q : ℕ × ℕ) (p : ℕ) : Bool := p.testBit q.1 != p.testBit q.2

def q_mono (p : ℕ) : Bool := (!p.testBit 17 || p.testBit 12) && (!p.testBit 16 || p.testBit 3)

def q_cov (C : List ℕ) : Prop := ∀ qv ∈ q_pv, ∃ c ∈ C, q_dif qv.1 c = true

theorem q_dif_op (q : ℕ × ℕ) (a b : ℕ)
    (h : q_dif q (a &&& b) = true ∨ q_dif q (a ||| b) = true) :
    q_dif q a = true ∨ q_dif q b = true := by
  simp only [q_dif, Nat.testBit_land, Nat.testBit_lor] at h ⊢
  generalize a.testBit q.1 = x1 at h ⊢
  generalize a.testBit q.2 = x2 at h ⊢
  generalize b.testBit q.1 = y1 at h ⊢
  generalize b.testBit q.2 = y2 at h ⊢
  revert h
  revert y2 y1 x2 x1
  decide

theorem q_mono_op (a b : ℕ) (ha : q_mono a = true) (hb : q_mono b = true) :
    q_mono (a &&& b) = true ∧ q_mono (a ||| b) = true := by
  simp only [q_mono, Nat.testBit_land, Nat.testBit_lor] at ha hb ⊢
  generalize a.testBit 17 = a1 at ha ⊢
  generalize a.testBit 12 = a2 at ha ⊢
  generalize a.testBit 16 = a3 at ha ⊢
  generalize a.testBit 3 = a4 at ha ⊢
  generalize b.testBit 17 = b1 at hb ⊢
  generalize b.testBit 12 = b2 at hb ⊢
  generalize b.testBit 16 = b3 at hb ⊢
  generalize b.testBit 3 = b4 at hb ⊢
  revert ha hb
  revert b4 b3 b2 b1 a4 a3 a2 a1
  decide

theorem q_base_mono : ∀ c ∈ q_base, q_mono c = true := by decide +kernel

theorem q_base_dif : ∀ qv ∈ q_pv, ∀ c ∈ q_base, q_dif qv.1 c = true → c = qv.2 := by decide +kernel

theorem q_vars_eq : q_pv.map Prod.snd = q_vars := rfl

theorem q_vars_nodup : q_vars.Nodup := by decide

theorem q_final (f : ℕ) (hm : q_mono f = true) (hf : f % 65536 = 375) : q_cov [f] := by
  have hb : ∀ i, i < 16 → f.testBit i = (375 : ℕ).testBit i := by
    intro i hi
    rw [← hf, show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.testBit_mod_two_pow]
    simp [hi]
  have e0 : f.testBit 0 = true := by rw [hb 0 (by norm_num)]; decide
  have e1 : f.testBit 1 = true := by rw [hb 1 (by norm_num)]; decide
  have e2 : f.testBit 2 = true := by rw [hb 2 (by norm_num)]; decide
  have e3 : f.testBit 3 = false := by rw [hb 3 (by norm_num)]; decide
  have e4 : f.testBit 4 = true := by rw [hb 4 (by norm_num)]; decide
  have e8 : f.testBit 8 = true := by rw [hb 8 (by norm_num)]; decide
  have e12 : f.testBit 12 = false := by rw [hb 12 (by norm_num)]; decide
  simp only [q_mono, e3, e12, Bool.or_false, Bool.and_eq_true, Bool.not_eq_true'] at hm
  obtain ⟨e17, e16⟩ := hm
  intro qv hqv
  refine ⟨f, List.mem_singleton_self f, ?_⟩
  simp only [q_pv, List.mem_cons, List.not_mem_nil, or_false] at hqv
  rcases hqv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [q_dif, e0, e1, e2, e4, e8, e16, e17]

inductive Mg : List ℕ → ℕ → ℕ → Prop
  | base (C : List ℕ) (f : ℕ) : List.Perm C [f] → Mg C 0 f
  | sand (C : List ℕ) (a b : ℕ) (D : List ℕ) (m f : ℕ) :
      List.Perm C (a :: b :: D) → Mg ((a &&& b) :: D) m f → Mg C (m + 1) f
  | sor (C : List ℕ) (a b : ℕ) (D : List ℕ) (m f : ℕ) :
      List.Perm C (a :: b :: D) → Mg ((a ||| b) :: D) m f → Mg C (m + 1) f

theorem Mg_perm {C : List ℕ} {m f : ℕ} (h : Mg C m f) {C' : List ℕ} (hp : List.Perm C C') :
    Mg C' m f := by
  cases h with
  | base _ _ h0 => exact Mg.base _ _ (hp.symm.trans h0)
  | sand _ a b D m f h0 h1 => exact Mg.sand _ a b D m f (hp.symm.trans h0) h1
  | sor _ a b D m f h0 h1 => exact Mg.sor _ a b D m f (hp.symm.trans h0) h1

def srch (T : ℕ) : ℕ → List ℕ → Bool
  | 0, L => L.all (fun x => x % 65536 != T)
  | m + 1, L => L.all (fun a => (L.erase a).all (fun b =>
      !(decide (a ≤ b)) || (srch T m ((a &&& b) :: (L.erase a).erase b) &&
        srch T m ((a ||| b) :: (L.erase a).erase b))))

theorem srch_pick (T m : ℕ) (L D : List ℕ) (x y : ℕ) (hL : List.Perm L (x :: y :: D)) (hxy : x ≤ y)
    (hs : srch T (m + 1) L = true) :
    ∃ D', List.Perm D' D ∧ srch T m ((x &&& y) :: D') = true ∧ srch T m ((x ||| y) :: D') = true := by
  have hx : x ∈ L := hL.symm.subset (by simp)
  have h1 : List.Perm (L.erase x) (y :: D) := by
    have := hL.erase x
    simpa using this
  have hy : y ∈ L.erase x := h1.symm.subset (by simp)
  have h2 : List.Perm ((L.erase x).erase y) D := by
    have := h1.erase y
    simpa using this
  simp only [srch, List.all_eq_true] at hs
  have h3 := hs x hx y hy
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true] at h3
  rcases h3 with h | h
  · exact absurd hxy h
  · exact ⟨_, h2, h.1, h.2⟩

theorem srch_sound (T : ℕ) : ∀ (C : List ℕ) (m f : ℕ), Mg C m f →
    ∀ L, List.Perm C L → srch T m L = true → f % 65536 ≠ T := by
  intro C m f h
  induction h with
  | base C f h0 =>
    intro L hCL hs
    have hL : L = [f] := List.perm_singleton.mp (hCL.symm.trans h0)
    subst hL
    simp only [srch, List.all_cons, List.all_nil, Bool.and_true, bne_iff_ne, ne_eq] at hs
    exact hs
  | sand C a b D m f h0 _ ih =>
    intro L hCL hs
    have hL : List.Perm L (a :: b :: D) := hCL.symm.trans h0
    rcases le_total a b with hab | hab
    · obtain ⟨D', hD', s1, _⟩ := srch_pick T m L D a b hL hab hs
      exact ih _ (List.Perm.cons _ hD'.symm) s1
    · obtain ⟨D', hD', s1, _⟩ := srch_pick T m L D b a (hL.trans (List.Perm.swap b a D)) hab hs
      rw [Nat.land_comm b a] at s1
      exact ih _ (List.Perm.cons _ hD'.symm) s1
  | sor C a b D m f h0 _ ih =>
    intro L hCL hs
    have hL : List.Perm L (a :: b :: D) := hCL.symm.trans h0
    rcases le_total a b with hab | hab
    · obtain ⟨D', hD', _, s2⟩ := srch_pick T m L D a b hL hab hs
      exact ih _ (List.Perm.cons _ hD'.symm) s2
    · obtain ⟨D', hD', _, s2⟩ := srch_pick T m L D b a (hL.trans (List.Perm.swap b a D)) hab hs
      rw [Nat.lor_comm b a] at s2
      exact ih _ (List.Perm.cons _ hD'.symm) s2

theorem q_srch : srch 375 5 q_vars = true := by decide +kernel

theorem length_insert_le (a : ℕ) (l : List ℕ) : (List.insert a l).length ≤ l.length + 1 := by
  by_cases h : a ∈ l
  · rw [List.insert_of_mem h]; omega
  · rw [List.insert_of_not_mem h]; simp

theorem q_back (St : ℕ → List ℕ) (len f : ℕ)
    (hst : ∀ j, j < len → ∃ a ∈ St j, ∃ b ∈ St j,
      St (j + 1) = (a &&& b) :: St j ∨ St (j + 1) = (a ||| b) :: St j)
    (hf : f ∈ St len) (hcf : q_cov [f]) :
    ∀ d, d ≤ len → ∃ C : List ℕ, (∀ c ∈ C, c ∈ St (len - d)) ∧ C.Nodup ∧ q_cov C ∧
      ∃ m, m ≤ d ∧ C.length ≤ m + 1 ∧ (C.length = m + 1 → Mg C m f) := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨[f], ?_, List.nodup_singleton f, hcf, 0, le_refl 0, by simp, fun _ => ?_⟩
    · intro c hc
      rw [List.mem_singleton.mp hc]
      simpa using hf
    · exact Mg.base _ _ (List.Perm.refl _)
  | succ d ih =>
    intro hd
    obtain ⟨C, hCS, hCn, hCc, m, hm, hCl, hCM⟩ := ih (by omega)
    have ej : len - d = (len - (d + 1)) + 1 := by omega
    obtain ⟨a, ha, b, hb, hS⟩ := hst (len - (d + 1)) (by omega)
    rw [ej] at hCS
    obtain ⟨e, he, hSe⟩ : ∃ e, (e = a &&& b ∨ e = a ||| b) ∧
        St (len - (d + 1) + 1) = e :: St (len - (d + 1)) := by
      rcases hS with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    rw [hSe] at hCS
    by_cases heC : e ∈ C
    · -- expand e into a and b
      have hDn : (C.erase e).Nodup := hCn.erase e
      have hDS : ∀ c ∈ C.erase e, c ∈ St (len - (d + 1)) := by
        intro c hc
        have hc2 := (hCn.mem_erase_iff).mp hc
        rcases List.mem_cons.mp (hCS c hc2.2) with h | h
        · exact absurd h hc2.1
        · exact h
      have hDl : (C.erase e).length + 1 = C.length := by
        rw [List.length_erase_of_mem heC]
        have := List.length_pos_of_mem heC
        omega
      have h1 := length_insert_le a (List.insert b (C.erase e))
      have h2 := length_insert_le b (C.erase e)
      refine ⟨List.insert a (List.insert b (C.erase e)), ?_, ?_, ?_, m + 1, by omega, by omega, ?_⟩
      · intro c hc
        rw [List.mem_insert_iff, List.mem_insert_iff] at hc
        rcases hc with rfl | rfl | hc
        · exact ha
        · exact hb
        · exact hDS c hc
      · exact (hDn.insert).insert
      · intro qv hqv
        obtain ⟨c, hc, hdc⟩ := hCc qv hqv
        by_cases hce : c = e
        · subst hce
          have h2 : q_dif qv.1 (a &&& b) = true ∨ q_dif qv.1 (a ||| b) = true := by
            rcases he with rfl | rfl
            · exact Or.inl hdc
            · exact Or.inr hdc
          rcases q_dif_op qv.1 a b h2 with h | h
          · exact ⟨a, List.mem_insert_iff.mpr (Or.inl rfl), h⟩
          · exact ⟨b, List.mem_insert_iff.mpr (Or.inr (List.mem_insert_iff.mpr (Or.inl rfl))), h⟩
        · have hcD : c ∈ C.erase e := (hCn.mem_erase_iff).mpr ⟨hce, hc⟩
          exact ⟨c, List.mem_insert_iff.mpr (Or.inr (List.mem_insert_iff.mpr (Or.inr hcD))), hdc⟩
      · intro hlen
        have hbD : b ∉ C.erase e := by
          intro hbD
          have h3 := length_insert_le a (C.erase e)
          rw [List.insert_of_mem hbD] at hlen
          omega
        have haD : a ∉ List.insert b (C.erase e) := by
          intro haD
          rw [List.insert_of_mem haD] at hlen
          omega
        have hC'eq : List.insert a (List.insert b (C.erase e)) = a :: b :: C.erase e := by
          rw [List.insert_of_not_mem haD, List.insert_of_not_mem hbD]
        have hMC : Mg C m f := hCM (by omega)
        have hMe : Mg (e :: C.erase e) m f := Mg_perm hMC (List.perm_cons_erase heC)
        rw [hC'eq]
        rcases he with rfl | rfl
        · exact Mg.sand _ a b _ m f (List.Perm.refl _) hMe
        · exact Mg.sor _ a b _ m f (List.Perm.refl _) hMe
    · -- e is not used: keep C
      refine ⟨C, ?_, hCn, hCc, m, by omega, hCl, hCM⟩
      intro c hc
      rcases List.mem_cons.mp (hCS c hc) with h | h
      · subst h; exact absurd hc heC
      · exact h

theorem q_mono_all (St : ℕ → List ℕ) (len : ℕ) (h0 : St 0 = q_base)
    (hst : ∀ j, j < len → ∃ a ∈ St j, ∃ b ∈ St j,
      St (j + 1) = (a &&& b) :: St j ∨ St (j + 1) = (a ||| b) :: St j) :
    ∀ j, j ≤ len → ∀ c ∈ St j, q_mono c = true := by
  intro j
  induction j with
  | zero => intro _ c hc; rw [h0] at hc; exact q_base_mono c hc
  | succ j ih =>
    intro hj c hc
    obtain ⟨a, ha, b, hb, hS⟩ := hst j (by omega)
    have hma := ih (by omega) a ha
    have hmb := ih (by omega) b hb
    rcases hS with h | h <;> rw [h] at hc <;> rcases List.mem_cons.mp hc with rfl | hc
    · exact (q_mono_op a b hma hmb).1
    · exact ih (by omega) c hc
    · exact (q_mono_op a b hma hmb).2
    · exact ih (by omega) c hc

theorem q_chain (St : ℕ → List ℕ) (len f : ℕ) (h0 : St 0 = q_base) (hlen : len ≤ 5)
    (hst : ∀ j, j < len → ∃ a ∈ St j, ∃ b ∈ St j,
      St (j + 1) = (a &&& b) :: St j ∨ St (j + 1) = (a ||| b) :: St j)
    (hf : f ∈ St len) (hT : f % 65536 = 375) : False := by
  have hmf := q_mono_all St len h0 hst len (le_refl _) f hf
  obtain ⟨C, hCS, hCn, hCc, m, hm, hCl, hCM⟩ :=
    q_back St len f hst hf (q_final f hmf hT) len (le_refl _)
  rw [Nat.sub_self, h0] at hCS
  have hsub : q_vars ⊆ C := by
    intro v hv
    rw [← q_vars_eq, List.mem_map] at hv
    obtain ⟨qv, hqv, rfl⟩ := hv
    obtain ⟨c, hc, hdc⟩ := hCc qv hqv
    have := q_base_dif qv hqv c (hCS c hc) hdc
    rw [← this]
    exact hc
  have hsp : List.Subperm q_vars C := List.subperm_of_subset q_vars_nodup hsub
  have h6 : q_vars.length ≤ C.length := hsp.length_le
  have hq6 : q_vars.length = 6 := rfl
  have hMC : Mg C m f := hCM (by omega)
  have hperm : List.Perm q_vars C := hsp.perm_of_length_le (by omega)
  have hm5 : m = 5 := by omega
  subst hm5
  exact srch_sound 375 C 5 f hMC q_vars hperm.symm q_srch hT

theorem q_lower :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  rintro ⟨C, hm, hs, hr⟩
  have hlen : C.gates.length ≤ 5 := hs
  have h0 : (0 : ℕ) ∈ q_base := by decide
  have h1 : (262143 : ℕ) ∈ q_base := by decide
  have hstep : ∀ j, j < C.gates.length → ∃ a ∈ q_St C j, ∃ b ∈ q_St C j,
      q_St C (j + 1) = (a &&& b) :: q_St C j ∨ q_St C (j + 1) = (a ||| b) :: q_St C j := by
    intro j hj
    have hg := hm _ (gateAt_mem hj)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by simpa using hg.1
    have e : q_prof C (8 + j) = t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map
        (fun i => if i < 8 + j then val C (q_inp k) i else false))) 18 := by
      unfold q_prof
      congr 1
      funext k
      exact val_gate (q_inp_len k) hj
    have hst : q_Step (q_St C j) (q_prof C (8 + j)) := by
      rw [e]
      apply q_gate_step _ (fun k i => if i < 8 + j then val C (q_inp k) i else false) _ _ hop hg.2
      · intro i _
        by_cases hi : i < 8 + j
        · simp only [hi, ↓reduceIte]
          exact q_St_prof C j i hi
        · simp only [hi, ↓reduceIte]
          rw [t1_bits_false]
          exact q_St_base C h0 j
      · exact q_St_base C h0 j
      · exact q_St_base C h1 j
    obtain ⟨a, ha, b, hb, hp⟩ := hst
    refine ⟨a, ha, b, hb, ?_⟩
    show q_prof C (8 + j) :: q_St C j = _ ∨ q_prof C (8 + j) :: q_St C j = _
    rcases hp with hp | hp
    · left; rw [hp]
    · right; rw [hp]
  have hout : q_prof C C.output ∈ q_St C C.gates.length := by
    by_cases ho : C.output < 8 + C.gates.length
    · exact q_St_prof C _ _ ho
    · have e : (fun k => val C (q_inp k) C.output) = fun _ => false :=
        funext fun k => val_ge (q_inp_len k) (by omega)
      have e2 : q_prof C C.output = 0 := by
        unfold q_prof; rw [e, t1_bits_false]
      rw [e2]
      exact q_St_base C h0 _
  have htarget : q_prof C C.output % 65536 = 375 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.testBit_mod_two_pow]
    unfold q_prof
    rw [t1_bits_testBit]
    by_cases hi : i < 16
    · have e : q_inp i = PEqualNP.Represents.oneEach (n := 4) (m := 4)
          ⟨i / 4 % 4, by omega⟩ ⟨i % 4, by omega⟩ := by
        unfold q_inp
        rw [if_neg (by omega), if_neg (by omega)]
      have h : C.eval (q_inp i) = (375 : ℕ).testBit (4 * (i / 4 % 4) + i % 4) := by
        rw [e]
        exact hr ⟨i / 4 % 4, by omega⟩ ⟨i % 4, by omega⟩
      have e2 : 4 * (i / 4 % 4) + i % 4 = i := by omega
      rw [e2] at h
      have hi18 : i < 18 := by omega
      simp only [hi, hi18, decide_true, Bool.true_and]
      exact h
    · simp only [hi, decide_false, Bool.false_and]
      symm
      apply Nat.testBit_eq_false_of_lt
      calc (375 : ℕ) < 2 ^ 16 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact q_chain (q_St C) C.gates.length _ rfl hlen hstep hout htarget

def t1_okop : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => false
  | GateOp.mod _ => false
  | GateOp.maj => false

theorem t1_mono2 (C : Circuit)
    (h : C.gates.all (fun g => t1_okop g.op && decide (g.inputs.length ≤ 2)) = true) :
    Monotone2 C := by
  intro g hg
  have h2 := List.all_eq_true.mp h g hg
  rcases g with ⟨op, ins⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨?_, h2.2⟩
  have h3 := h2.1
  cases op <;> simp [t1_okop] at h3 ⊢


def qw : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [9, 6]⟩,
  ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem qw_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) qw := by
  decide

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨⟨qw, t1_mono2 qw (by decide), by decide, qw_rep⟩, q_lower⟩

end PEqualNP.Outside.L_meta_5535

theorem PEqualNP.Outside.L_meta_5535 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  PEqualNP.Outside.L_meta_5535.main_aux
