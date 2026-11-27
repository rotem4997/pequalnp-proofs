import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4742

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

-- FRAGMENT orreach    DEPENDS: fold mono
-- OR closures (PEqualNP.CleanedNonEdge.orStep / orSets / OrReaches), PEqualNP.TopForm.orIn, and the
-- value facts: a true gate makes every wire OR-reaching it true.
-- Exports (CNE = PEqualNP.CleanedNonEdge, TF = PEqualNP.TopForm):
--   wireVal_eq_val : CNE.wireVal n C w x = val C (List.ofFn x) w   (rfl)
--   gateVal_eq_val : PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j)   (rfl)
--   readVal_eq : CNE.readVal n C a w x = if w < n + a then val C (List.ofFn x) w else false   (rfl)
--   orSets_len gs cs : (gs.foldl (CNE.orStep n) cs).length = cs.length + gs.length
--   orSets_length : (CNE.orSets n C).length = C.gates.length
--   orSets_char gs : i in (gs.foldl (orStep n) []).getD j [] iff j < gs.length and (i = j or
--       (gs.getD j (OR of nothing)).op = or and exists w in its inputs, n <= w, w < n + j, i in (fold).getD (w - n) [])
--   orSets_mem_iff (hk : k < C.gates.length) : x in (orSets n C).getD k [] iff x = k or
--       ((gateAt C k).op = or and exists w in (gateAt C k).inputs, n <= w and w < n + k and x in (orSets n C).getD (w - n) [])
--   orReaches_iff : CNE.OrReaches n C (n + k) g iff k < C.gates.length and (g = k or
--       ((gateAt C k).op = or and exists i in (gateAt C k).inputs, i < n + k and OrReaches n C i g))
--   orReaches_self (hj : j < C.gates.length) : OrReaches n C (n + j) j
--   orReaches_step (j an OR gate, i in its inputs, i < n + j, OrReaches n C i g) : OrReaches n C (n + j) g
--   orReaches_bound : OrReaches n C w g -> n + g <= w and w < n + C.gates.length
--   orReaches_trans : OrReaches n C w (k) -> OrReaches n C (n + k) g -> OrReaches n C w g
--   reach_up (hx : x.length = n) (val C x (n + j) = true) : for all b, OrReaches n C b j -> val C x b = true
--   reach_up_wire : CNE.wireVal n C (n + j) x = true -> OrReaches n C b j -> CNE.wireVal n C b x = true
--   orIn_mem_filter : membership in Finset.filter with an arbitrary decidability proof
--   mem_orIn : i in TF.orIn n C w iff (i = w or exists k < C.gates.length, OrReaches n C w k and
--       (gateAt C k).op = or and i in (gateAt C k).inputs)
--   orIn_self (i : Fin n) : i in TF.orIn n C i
--   orIn_up (j an OR gate, i in its inputs, i < n + j) : a in orIn n C i -> a in orIn n C (n + j)
--   orIn_reach : OrReaches n C b k -> a in orIn n C (n + k) -> a in orIn n C b
--   orIn_val (hx : x.length = n) : a in orIn n C b -> val C x a = true -> val C x b = true
-- Use: orReaches_iff to unfold one level, reach_up / orIn_val to push truth up OR chains.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem wireVal_eq_val (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = val C (List.ofFn x) w := rfl

theorem gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

theorem readVal_eq (n : ℕ) (C : Circuit) (a w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.readVal n C a w x =
      if w < n + a then val C (List.ofFn x) w else false := rfl

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
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

theorem orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

theorem orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

theorem orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

theorem orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

theorem reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

theorem reach_up_wire (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j b : ℕ)
    (hv : PEqualNP.CleanedNonEdge.wireVal n C (n + j) x = true)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b j) :
    PEqualNP.CleanedNonEdge.wireVal n C b x = true :=
  reach_up n C (List.ofFn x) (by simp) j hv b hr

theorem orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

theorem mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

theorem orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

theorem orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

theorem orIn_reach (n : ℕ) (C : Circuit) (b k : ℕ) (a : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b k)
    (h : a ∈ PEqualNP.TopForm.orIn n C (n + k)) : a ∈ PEqualNP.TopForm.orIn n C b := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨m, hm, hrm, hopm, hin⟩
  · exfalso; have := a.isLt; omega
  · exact ⟨m, hm, orReaches_trans n C k m hrm b hr, hopm, hin⟩

theorem orIn_val (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (a : Fin n) (b : ℕ)
    (h : a ∈ PEqualNP.TopForm.orIn n C b) (hv : val C x a = true) : val C x b = true := by
  rw [mem_orIn] at h
  rcases h with hw | ⟨k, hk, hr, hop, hin⟩
  · rw [← hw]; exact hv
  · refine reach_up n C x hx k ?_ b hr
    refine (val_or hx hk hop).mpr ⟨a.val, hin, ?_, hv⟩
    have := a.isLt
    omega

-- FRAGMENT erase    DEPENDS: fold mono
-- Semantics of eraseGate, eraseRedirect and liftAt (namespace PEqualNP.CircuitMoves is opened here).
-- Abbreviations in this header: E = eraseGate n C m p, L = liftAt n C m p h, r = eraseRedirect n m p, hm : m < C.gates.length.
-- Exports:
--   def erase_rg (r : ℕ → ℕ) (g : Gate) : Gate := gate g with every input renamed by r
--   erase_redirect_lt n m p i (i < n + m) : r i = i ;  erase_redirect_self n m p : r (n + m) = p
--   erase_redirect_gt n m p i (n + m < i) : r i = i - 1 ;  erase_redirect_succ n m p k (n + m <= k) : r (k + 1) = k
--   erase_eq hm : E = Circuit.mk (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg r)) (r C.output)
--   erase_gates hm, erase_output hm : the two fields of erase_eq ;  erase_of_ge (C.gates.length <= m) : E = C
--   erase_length hm : E.gates.length + 1 = C.gates.length ;  erase_size hm : E.size + 1 = C.size
--   erase_getD : (l.take m ++ (l.drop (m + 1)).map f).getD j d = if j < m then l.getD j d else f (l.getD (j + 1) d)
--   erase_gateAt hm (j + 1 < C.gates.length) : gateAt E j = if j < m then gateAt C j else erase_rg r (gateAt C (j + 1))
--   erase_gateAt_lt hm (j < m) : gateAt E j = gateAt C j
--   erase_gateAt_ge hm (m <= j) (j + 1 < C.gates.length) : gateAt E j = erase_rg r (gateAt C (j + 1))
--   erase_monotone2 hm : Monotone2 C -> Monotone2 E ;  erase_andOrOnly hm : AndOrOnly C -> AndOrOnly E
--   erase_readsBack hm (p < n + m) : ReadsBack n C -> ReadsBack n E
--   erase_output_lt hm (p < n + m) (C.output < n + C.gates.length) : E.output < n + E.gates.length
--   erase_val_lt hm (x.length = n) (i < n + m) : val E x i = val C x i
--   erase_val_rel Q rel (rel refl) hm (p < n + m) (rel-transfer for ops with Q) (Q on gates after m) hx
--       (rel (val C x (n + m)) (val C x p)) : for all i, rel (val C x i) (val E x (r i))
--   erase_val hm (p < n + m) hx (val C x p = val C x (n + m)) : for all i, val E x (r i) = val C x i
--   erase_val_pre (same) : val E x k = val C x (if k < n + m then k else k + 1)
--   erase_eval (same) : E.eval x = C.eval x
--   erase_val_imp hm (p < n + m) (AndOrOnly C) hx (val C x (n + m) = true -> val C x p = true) :
--       for all i, val C x i = true -> val E x (r i) = true
--   erase_eval_imp (same) : C.eval x = true -> E.eval x = true
--   erase_and_below hm (gateAt C m).op = and, p in its inputs, hx : val C x (n + m) = true -> val C x p = true
--   erase_eval_and hm (AndOrOnly C) (op = and) (p in inputs) (p < n + m) hx : C.eval x = true -> E.eval x = true
--   erase_main (Monotone2 C) (ReadsBack n C) hm (p < n + m) : Monotone2 E, ReadsBack n E, E.size + 1 = C.size,
--       and for x of length n, val C x p = val C x (n + m) -> E.eval x = C.eval x   (row L-meta-2859)
--   generic tools: erase_hop_eq, erase_hop_le, erase_snoc_eq, erase_snoc_gt, erase_step_rel, erase_W_rel, erase_sem
--   lift_gates : L.gates = E.gates ++ [OR (E.output, h)] (rfl) ;  lift_output : L.output = n + E.gates.length (rfl)
--   lift_length hm : L.gates.length = C.gates.length ;  lift_size hm : L.size = C.size
--   lift_gateAt_lt (j < E.gates.length) : gateAt L j = gateAt E j ;  lift_gateAt_last : gateAt L E.gates.length = OR (E.output, h)
--   lift_monotone2 hm : Monotone2 C -> Monotone2 L
--   lift_readsBack : ReadsBack n E -> E.output < n + E.gates.length -> h < n + E.gates.length -> ReadsBack n L
--   lift_val_lt hx (k < n + E.gates.length) : val L x k = val E x k
--   lift_or_eval2 f a b : (OR gate on a, b) evaluated with f = (f a || f b)
--   lift_eval_or hx : L.eval x = (E.eval x || val E x h)
--   lift_eval hm (p < n + m) (h < n + m) (gateAt C m = OR p h or OR h p) hx (val C x h = true -> C.eval x = true) : L.eval x = C.eval x
--   lift_main (Monotone2 C) (ReadsBack n C) (C.output < n + C.gates.length) hm (p, h < n + m) (C.gates[m]? = OR p h or OR h p)
--       (WireBelowOutput n C h) : Monotone2 L, ReadsBack n L, L.size = C.size, L.eval (ofFn x) = C.eval (ofFn x)
--   lift_of_Lift : Monotone2 C -> ReadsBack n C -> C.output < n + C.gates.length -> Lift n C C' -> the same four facts for C'
-- Use: shape via erase_gates / erase_gateAt / lift_gateAt_*, semantics via erase_val (wire i of C is wire r i of E
-- when the erased gate equals p on x) or erase_val_imp with erase_and_below (AND gate erased onto an operand);
-- for liftAt use lift_eval_or then erase_val.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

def erase_rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem erase_redirect_lt (n m p i : ℕ) (h : i < n + m) : eraseRedirect n m p i = i := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_neg (by omega)]

theorem erase_redirect_self (n m p : ℕ) : eraseRedirect n m p (n + m) = p := by
  unfold eraseRedirect
  rw [if_pos rfl]

theorem erase_redirect_gt (n m p i : ℕ) (h : n + m < i) : eraseRedirect n m p i = i - 1 := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_pos h]

theorem erase_redirect_succ (n m p k : ℕ) (h : n + m ≤ k) : eraseRedirect n m p (k + 1) = k := by
  rw [erase_redirect_gt n m p (k + 1) (by omega), Nat.add_sub_cancel]

theorem erase_hop_eq (r : ℕ → ℕ) (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool)
    (h : ∀ i, f i = f' (r i)) :
    op.eval (l.map f) = op.eval ((l.map r).map f') := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h i

theorem erase_hop_le (r : ℕ → ℕ) (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) (h : ∀ i, f i = true → f' (r i) = true) :
    op.eval (l.map f) = true → op.eval ((l.map r).map f') = true := by
  rcases hop with rfl | rfl
  · intro hall
    have h1 : (l.map f).all id = true := hall
    show ((l.map r).map f').all id = true
    rw [List.all_eq_true] at h1 ⊢
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    exact h i (h1 (f i) (List.mem_map.2 ⟨i, hi, rfl⟩))
  · intro hany
    have h1 : (l.map f).any id = true := hany
    show ((l.map r).map f').any id = true
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨b, hb, hbt⟩ := h1
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact ⟨f' (r i), List.mem_map.2 ⟨r i, List.mem_map.2 ⟨i, hi, rfl⟩, rfl⟩, h i hbt⟩

theorem erase_snoc_eq (a : List Bool) (v : Bool) (i : ℕ) (h : i = a.length) :
    (a ++ [v]).getD i false = v := by
  subst h
  exact getD_app_len a v

theorem erase_snoc_gt (a : List Bool) (v : Bool) (i : ℕ) (h : a.length < i) :
    (a ++ [v]).getD i false = false :=
  getD_ge _ _ (by rw [List.length_append, List.length_singleton]; omega)

theorem erase_step_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ)
    (hp : p < n + m) (a b : List Bool) (va vb : Bool) (hl : a.length = b.length + 1)
    (hn : n + m < a.length)
    (h : ∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) (hv : rel va vb) :
    ∀ i, rel ((a ++ [va]).getD i false) ((b ++ [vb]).getD (eraseRedirect n m p i) false) := by
  intro i
  by_cases hi : i < a.length
  · have hri : eraseRedirect n m p i < b.length := by
      unfold eraseRedirect
      split_ifs <;> omega
    rw [getD_app_lt a [va] i hi, getD_app_lt b [vb] _ hri]
    exact h i
  · rw [erase_redirect_gt n m p i (by omega)]
    by_cases hi2 : i = a.length
    · rw [erase_snoc_eq a va i hi2, erase_snoc_eq b vb (i - 1) (by omega)]
      exact hv
    · rw [erase_snoc_gt a va i (by omega), erase_snoc_gt b vb (i - 1) (by omega)]
      exact h00

theorem erase_W_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (h00 : rel false false)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (gs : List Gate) : ∀ (a b : List Bool), (∀ g ∈ gs, Q g.op) →
      a.length = b.length + 1 → n + m < a.length →
      (∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) →
      ∀ i, rel ((W gs a).getD i false)
        ((W (gs.map (erase_rg (eraseRedirect n m p))) b).getD (eraseRedirect n m p i) false) := by
  induction gs with
  | nil => intro a b _ _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hg hl hn h i
    rw [List.map_cons, W_cons, W_cons]
    refine ih (step a g) (step b (erase_rg (eraseRedirect n m p) g)) ?_ ?_ ?_ ?_ i
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · rw [step_len, step_len, hl]
    · rw [step_len]
      omega
    · exact erase_step_rel rel h00 n m p hp a b
        (g.op.eval (g.inputs.map fun i => a.getD i false))
        (g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => b.getD i false))
        hl hn h
        (hop g.op g.inputs (fun i => a.getD i false) (fun i => b.getD i false)
          (hg g (by simp)) h)

theorem erase_sem (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (pre post : List Gate) (gm : Gate) (x : List Bool) (hx : x.length = n)
    (hpre : pre.length = m)
    (hpost : ∀ g ∈ post, Q g.op)
    (hbase : rel (gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false))
      ((W pre x).getD p false)) :
    ∀ i, rel ((W (pre ++ gm :: post) x).getD i false)
      ((W (pre ++ post.map (erase_rg (eraseRedirect n m p))) x).getD
        (eraseRedirect n m p i) false) := by
  have hA : (W pre x).length = n + m := by rw [W_length, hx, hpre]
  rw [W_append, W_append, W_cons]
  refine erase_W_rel Q rel (hrefl false) n m p hp hop post (step (W pre x) gm) (W pre x)
    hpost ?_ ?_ ?_
  · exact step_len _ _
  · rw [step_len, hA]
    omega
  · intro i
    show rel ((W pre x ++ [gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false)]).getD i
      false) ((W pre x).getD (eraseRedirect n m p i) false)
    by_cases hi : i < n + m
    · rw [erase_redirect_lt n m p i hi, getD_app_lt (W pre x) _ i (by omega)]
      exact hrefl _
    · by_cases hi2 : i = n + m
      · rw [hi2, erase_redirect_self n m p, erase_snoc_eq (W pre x) _ (n + m) hA.symm]
        exact hbase
      · rw [erase_redirect_gt n m p i (by omega), erase_snoc_gt (W pre x) _ i (by omega),
          getD_ge (W pre x) (i - 1) (by omega)]
        exact hrefl false

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p = Circuit.mk
      (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (eraseRedirect n m p C.output) := if_pos hm

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates
      = C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)) :=
  congrArg Circuit.gates (erase_eq n C m p hm)

theorem erase_output (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output :=
  congrArg Circuit.output (erase_eq n C m p hm)

theorem erase_of_ge (n : ℕ) (C : Circuit) (m p : ℕ) (hm : C.gates.length ≤ m) :
    eraseGate n C m p = C := if_neg (Nat.not_lt.mpr hm)

theorem erase_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length + 1 = C.gates.length := by
  rw [erase_gates n C m p hm, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  show (eraseGate n C m p).gates.length + 1 = C.gates.length
  exact erase_length n C m p hm

theorem erase_getD (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
    (hj : j + 1 < l.length) :
    (l.take m ++ (l.drop (m + 1)).map f).getD j d
      = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
  have hlt : (l.take m).length = m := by
    rw [List.length_take]
    omega
  by_cases h : j < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
      List.getElem_take]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hlt]
    have e : m + 1 + (j - m) = j + 1 := by omega
    rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
        (by rw [List.length_map, List.length_drop]; omega),
      List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
    simp only [e]

theorem erase_gateAt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j
      = if j < m then gateAt C j else erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  have h0 : gateAt (eraseGate n C m p) j
      = (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))).getD j
        (Gate.mk GateOp.or []) :=
    congrArg (fun gs : List Gate => gs.getD j (Gate.mk GateOp.or [])) (erase_gates n C m p hm)
  rw [h0]
  exact erase_getD C.gates (erase_rg (eraseRedirect n m p)) (Gate.mk GateOp.or []) m j hm hj

theorem erase_gateAt_lt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : j < m) : gateAt (eraseGate n C m p) j = gateAt C j := by
  rw [erase_gateAt n C m p j hm (by omega), if_pos hj]

theorem erase_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : m ≤ j) (hj1 : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j = erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  rw [erase_gateAt n C m p j hm hj1, if_neg (Nat.not_lt.mpr hj)]

theorem erase_monotone2 (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hM : Monotone2 C) : Monotone2 (eraseGate n C m p) := by
  intro g hg
  rw [erase_gates n C m p hm] at hg
  rcases List.mem_append.1 hg with h | h
  · exact hM g (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    have h0 := hM g0 (List.mem_of_mem_drop hg0)
    refine ⟨h0.1, ?_⟩
    show (g0.inputs.map (eraseRedirect n m p)).length ≤ 2
    rw [List.length_map]
    exact h0.2

theorem erase_andOrOnly (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hA : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (eraseGate n C m p) := by
  intro g hg
  rw [erase_gates n C m p hm] at hg
  rcases List.mem_append.1 hg with h | h
  · exact hA g (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    exact hA g0 (List.mem_of_mem_drop hg0)

theorem erase_readsBack (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hR : ReadsBack n C) : ReadsBack n (eraseGate n C m p) := by
  have hElen := erase_length n C m p hm
  intro j hj i hi
  rw [erase_gateAt n C m p j hm (by omega)] at hi
  by_cases hjm : j < m
  · rw [if_pos hjm] at hi
    exact hR j (by omega) i hi
  · rw [if_neg hjm] at hi
    have hi' : i ∈ (gateAt C (j + 1)).inputs.map (eraseRedirect n m p) := hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
    have h2 := hR (j + 1) (by omega) i0 hi0
    unfold eraseRedirect
    split_ifs <;> omega

theorem erase_output_lt (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hout : C.output < n + C.gates.length) :
    (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length := by
  have hE := erase_length n C m p hm
  rw [erase_output n C m p hm]
  unfold eraseRedirect
  split_ifs <;> omega

theorem erase_val_lt {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
    {x : List Bool} (hx : x.length = n) {i : ℕ} (hi : i < n + m) :
    val (eraseGate n C m p) x i = val C x i := by
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  have e2 : val C x i = (W (C.gates.take m ++ C.gates.drop m) x).getD i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (List.take_append_drop m C.gates).symm
  rw [e1, e2, W_append, W_append,
    W_prefix ((C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (W (C.gates.take m) x) i (by omega),
    W_prefix (C.gates.drop m) (W (C.gates.take m) x) i (by omega)]

theorem erase_val_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (hQ : ∀ g ∈ C.gates.drop (m + 1), Q g.op)
    {x : List Bool} (hx : x.length = n) (hv : rel (val C x (n + m)) (val C x p)) :
    ∀ i, rel (val C x i) (val (eraseGate n C m p) x (eraseRedirect n m p i)) := by
  have hsplit : C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1) = C.gates := by
    rw [gateAt_eq hm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val C x (n + m) = (gateAt C m).op.eval
      ((gateAt C m).inputs.map fun i => (W (C.gates.take m) x).getD i false) := by
    have h1 := W_gate_pre C.gates (C.gates.take m) (C.gates.drop (m + 1)) (gateAt C m) x
      hsplit.symm
    rw [hx, hpre] at h1
    exact h1
  have e2 : val C x p = (W (C.gates.take m) x).getD p false := by
    show (W C.gates x).getD p false = _
    rw [W_split C.gates x m]
    exact W_prefix _ _ _ (by omega)
  rw [e1, e2] at hv
  have key := erase_sem Q rel hrefl n m p hp hop (C.gates.take m) (C.gates.drop (m + 1))
    (gateAt C m) x hx hpre hQ hv
  have hW : ∀ i, val C x i
      = (W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x).getD i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) hsplit.symm
  have hWD : ∀ i, val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  intro i
  rw [hW i, hWD (eraseRedirect n m p i)]
  exact key i

theorem erase_val {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    {x : List Bool} (hx : x.length = n) (hv : val C x p = val C x (n + m)) :
    ∀ i, val (eraseGate n C m p) x (eraseRedirect n m p i) = val C x i := by
  intro i
  exact (erase_val_rel (fun _ => True) (@Eq Bool) (fun _ => rfl) hm hp
    (fun op l f f' _ h => erase_hop_eq (eraseRedirect n m p) op l f f' h)
    (fun _ _ => trivial) hx hv.symm i).symm

theorem erase_val_pre {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    {x : List Bool} (hx : x.length = n) (hv : val C x p = val C x (n + m)) (k : ℕ) :
    val (eraseGate n C m p) x k = val C x (if k < n + m then k else k + 1) := by
  by_cases hk : k < n + m
  · rw [if_pos hk]
    exact erase_val_lt hm hx hk
  · rw [if_neg hk]
    have h1 := erase_val hm hp hx hv (k + 1)
    rw [erase_redirect_succ n m p k (by omega)] at h1
    exact h1

theorem erase_eval {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    {x : List Bool} (hx : x.length = n) (hv : val C x p = val C x (n + m)) :
    (eraseGate n C m p).eval x = C.eval x := by
  show val (eraseGate n C m p) x (eraseGate n C m p).output = val C x C.output
  rw [erase_output n C m p hm]
  exact erase_val hm hp hx hv C.output

theorem erase_val_imp {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) {x : List Bool} (hx : x.length = n)
    (hv : val C x (n + m) = true → val C x p = true) :
    ∀ i, val C x i = true → val (eraseGate n C m p) x (eraseRedirect n m p i) = true :=
  erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or) (fun a b => a = true → b = true)
    (fun _ h => h) hm hp (erase_hop_le (eraseRedirect n m p))
    (fun g hg => hAO g (List.mem_of_mem_drop hg)) hx hv

theorem erase_eval_imp {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) {x : List Bool} (hx : x.length = n)
    (hv : val C x (n + m) = true → val C x p = true) :
    C.eval x = true → (eraseGate n C m p).eval x = true := by
  intro hC
  show val (eraseGate n C m p) x (eraseGate n C m p).output = true
  rw [erase_output n C m p hm]
  exact erase_val_imp hm hp hAO hx hv C.output hC

theorem erase_and_below {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.and) (hpi : p ∈ (gateAt C m).inputs)
    {x : List Bool} (hx : x.length = n) : val C x (n + m) = true → val C x p = true := by
  rw [val_and hx hm hop]
  intro h
  exact (h p hpi).2

theorem erase_eval_and {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hop : (gateAt C m).op = GateOp.and)
    (hpi : p ∈ (gateAt C m).inputs) (hp : p < n + m) {x : List Bool} (hx : x.length = n) :
    C.eval x = true → (eraseGate n C m p).eval x = true :=
  erase_eval_imp hm hp hAO hx (erase_and_below hm hop hpi hx)

theorem erase_main (n : ℕ) (C : Circuit) (m p : ℕ) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hm : m < C.gates.length) (hp : p < n + m) :
    Monotone2 (eraseGate n C m p) ∧ ReadsBack n (eraseGate n C m p) ∧
    (eraseGate n C m p).size + 1 = C.size ∧ ∀ x : List Bool, x.length = n →
      (val C x p = val C x (n + m) → (eraseGate n C m p).eval x = C.eval x) :=
  ⟨erase_monotone2 n C m p hm hM, erase_readsBack n C m p hm hp hR, erase_size n C m p hm,
    fun _ hx hv => erase_eval hm hp hx hv⟩

theorem lift_gates (n : ℕ) (C : Circuit) (m p h : ℕ) :
    (liftAt n C m p h).gates = (eraseGate n C m p).gates ++
      [Gate.mk GateOp.or [(eraseGate n C m p).output, h]] := rfl

theorem lift_output (n : ℕ) (C : Circuit) (m p h : ℕ) :
    (liftAt n C m p h).output = n + (eraseGate n C m p).gates.length := rfl

theorem lift_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates.length = C.gates.length := by
  rw [lift_gates, List.length_append, List.length_singleton]
  exact erase_length n C m p hm

theorem lift_size (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).size = C.size := lift_length n C m p h hm

theorem lift_gateAt_lt (n : ℕ) (C : Circuit) (m p h j : ℕ)
    (hj : j < (eraseGate n C m p).gates.length) :
    gateAt (liftAt n C m p h) j = gateAt (eraseGate n C m p) j := by
  unfold gateAt
  rw [lift_gates]
  exact List.getD_append _ _ _ _ hj

theorem lift_gateAt_last (n : ℕ) (C : Circuit) (m p h : ℕ) :
    gateAt (liftAt n C m p h) (eraseGate n C m p).gates.length
      = Gate.mk GateOp.or [(eraseGate n C m p).output, h] := by
  unfold gateAt
  rw [lift_gates, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem lift_monotone2 (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
    (hM : Monotone2 C) : Monotone2 (liftAt n C m p h) := by
  intro g hg
  rw [lift_gates] at hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact erase_monotone2 n C m p hm hM g h1
  · rw [List.mem_singleton] at h1
    subst h1
    exact ⟨by simp, by simp⟩

theorem lift_readsBack (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hRE : ReadsBack n (eraseGate n C m p))
    (hEout : (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length)
    (hh : h < n + (eraseGate n C m p).gates.length) : ReadsBack n (liftAt n C m p h) := by
  intro j hj i hi
  have hj' : j < (eraseGate n C m p).gates.length + 1 := by
    rw [lift_gates, List.length_append, List.length_singleton] at hj
    exact hj
  by_cases hjl : j < (eraseGate n C m p).gates.length
  · rw [lift_gateAt_lt n C m p h j hjl] at hi
    exact hRE j hjl i hi
  · have hjE : j = (eraseGate n C m p).gates.length := by omega
    subst hjE
    rw [lift_gateAt_last] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> subst hi <;> omega

theorem lift_val_lt {n : ℕ} {C : Circuit} {m p h : ℕ} {x : List Bool} (hx : x.length = n)
    {k : ℕ} (hk : k < n + (eraseGate n C m p).gates.length) :
    val (liftAt n C m p h) x k = val (eraseGate n C m p) x k := by
  show (W (liftAt n C m p h).gates x).getD k false = (W (eraseGate n C m p).gates x).getD k false
  rw [lift_gates, W_append]
  exact W_prefix _ _ _ (by rw [W_length]; omega)

theorem lift_or_eval2 (f : ℕ → Bool) (a b : ℕ) :
    GateOp.eval (Gate.mk GateOp.or [a, b]).op ((Gate.mk GateOp.or [a, b]).inputs.map f)
      = (f a || f b) := by
  show (f a || (f b || false)) = (f a || f b)
  cases f a <;> cases f b <;> rfl

theorem lift_eval_or {n : ℕ} {C : Circuit} {m p h : ℕ} {x : List Bool} (hx : x.length = n) :
    (liftAt n C m p h).eval x = ((eraseGate n C m p).eval x || val (eraseGate n C m p) x h) := by
  have hEl : (W (eraseGate n C m p).gates x).length = n + (eraseGate n C m p).gates.length := by
    rw [W_length, hx]
  show (W ((eraseGate n C m p).gates ++
    [Gate.mk GateOp.or [(eraseGate n C m p).output, h]]) x).getD
      (n + (eraseGate n C m p).gates.length) false = _
  rw [W_snoc, step_last _ _ _ hEl.symm]
  exact lift_or_eval2 _ _ _

theorem lift_eval {n : ℕ} {C : Circuit} {m p h : ℕ} (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hg : gateAt C m = Gate.mk GateOp.or [p, h] ∨ gateAt C m = Gate.mk GateOp.or [h, p])
    {x : List Bool} (hx : x.length = n) (hb : val C x h = true → C.eval x = true) :
    (liftAt n C m p h).eval x = C.eval x := by
  have cM : val C x (n + m) = (val C x p || val C x h) := by
    rcases hg with e | e
    · rw [val_gate hx hm, e, lift_or_eval2, if_pos hp, if_pos hh]
    · rw [val_gate hx hm, e, lift_or_eval2, if_pos hp, if_pos hh, Bool.or_comm]
  have cH : val (eraseGate n C m p) x h = val C x h := erase_val_lt hm hx hh
  rw [lift_eval_or hx, cH]
  cases hAh : val C x h
  · rw [Bool.or_false]
    apply erase_eval hm hp hx
    rw [cM, hAh, Bool.or_false]
  · rw [Bool.or_true]
    exact (hb hAh).symm

theorem lift_main (n : ℕ) (C : Circuit) (m p h : ℕ) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hout : C.output < n + C.gates.length) (hm : m < C.gates.length) (hp : p < n + m)
    (hh : h < n + m)
    (hg : C.gates[m]? = some (Gate.mk GateOp.or [p, h]) ∨
      C.gates[m]? = some (Gate.mk GateOp.or [h, p]))
    (hb : WireBelowOutput n C h) :
    Monotone2 (liftAt n C m p h) ∧ ReadsBack n (liftAt n C m p h) ∧
    (liftAt n C m p h).size = C.size ∧
    ∀ x : Fin n → Bool, (liftAt n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hE := erase_length n C m p hm
  have hg' : gateAt C m = Gate.mk GateOp.or [p, h] ∨ gateAt C m = Gate.mk GateOp.or [h, p] := by
    rcases hg with e | e
    · exact Or.inl (getElem?_gateAt e).1
    · exact Or.inr (getElem?_gateAt e).1
  refine ⟨lift_monotone2 n C m p h hm hM,
    lift_readsBack n C m p h (erase_readsBack n C m p hm hp hR)
      (erase_output_lt n C m p hm hp hout) (by omega),
    lift_size n C m p h hm, ?_⟩
  intro x
  exact lift_eval hm hp hh hg' List.length_ofFn (hb x)

theorem lift_of_Lift (n : ℕ) (C C' : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hout : C.output < n + C.gates.length) (hL : Lift n C C') :
    Monotone2 C' ∧ ReadsBack n C' ∧ C'.size = C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨m, hm, p, hp, h, hh, _, hg, hb, rfl⟩ := hL
  exact lift_main n C m p h hM hR hout hm hp hh hg hb

theorem p47_mem2 (l : List ℕ) (h : l.length = 2) (t : ℕ) (ht : t < 2) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem l 0 (by omega : t < l.length)]
  apply List.getElem_mem

theorem p47_map_getD (l : List ℕ) (r : ℕ → ℕ) (t : ℕ) (ht : t < l.length) :
    (l.map r).getD t 0 = r (l.getD t 0) := by
  have h2 : t < (l.map r).length := by rw [List.length_map]; exact ht
  rw [List.getD_eq_getElem (l.map r) 0 h2, List.getD_eq_getElem l 0 ht, List.getElem_map]

theorem p47_pair_val {n : ℕ} (C : Circuit) (u z : Fin n) (w : ℕ) (hw : w < n) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) w = decide (w = u.val ∨ w = z.val) := by
  rw [val_ofFn_lt C _ w hw]
  simp [PEqualNP.EdgeOwnership.pairInput, Fin.ext_iff]

theorem p47_unit_val {n : ℕ} (C : Circuit) (u : Fin n) (w : ℕ) (hw : w < n) :
    val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) w = decide (w = u.val) := by
  rw [val_ofFn_lt C _ w hw]
  simp [PEqualNP.SplitCount.unitInput, Fin.ext_iff]

theorem p47_isAO2_erase (n : ℕ) (C : Circuit) (g v : ℕ) (hg : g < C.gates.length) (hv : v < n + g)
    (hAO : PEqualNP.TopForm.IsAO2 n C) : PEqualNP.TopForm.IsAO2 n (eraseGate n C g v) := by
  refine ⟨erase_andOrOnly n C g v hg hAO.1, erase_readsBack n C g v hg hv hAO.2.1, ?_⟩
  intro gt hgt
  rw [erase_gates n C g v hg] at hgt
  rcases List.mem_append.1 hgt with h | h
  · exact hAO.2.2 _ (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    show (g0.inputs.map _).length = 2
    rw [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_drop hg0)

theorem p47_rec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k) :
    ∀ w : ℕ, (¬ ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true) →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) w = true →
      val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) w = true ∨
      val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) w = true ∨
      PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  unfold PEqualNP.Core.IsLiftFixedPoint PEqualNP.Core.LiftApplies PEqualNP.Core.LiftAt
    PEqualNP.Core.IsImpWire at hLF
  unfold PEqualNP.TopForm.BelowF at hbelow
  have hx : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnb hv
    by_cases hwn : w < n
    · rw [p47_pair_val C u z w hwn, decide_eq_true_eq] at hv
      rcases hv with h | h
      · left
        rw [p47_unit_val C u w hwn, decide_eq_true_eq]
        exact h
      · right; left
        rw [p47_unit_val C z w hwn, decide_eq_true_eq]
        exact h
    · by_cases hwl : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
        rcases hAO.1 _ (gateAt_mem hj) with hop | hop
        · by_cases hjg : j = g
          · subst hjg
            exact Or.inr (Or.inr (orReaches_self n C j hj))
          · exact absurd (fun x hx' => hbelow j hj hop hjg x hx') hnb
        · have key : ∀ t : ℕ, t < 2 →
              val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z))
                ((gateAt C j).inputs.getD t 0) = true →
              val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) (n + j) = true ∨
              val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) (n + j) = true ∨
              PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g := by
            intro t ht hvt
            have hmem := p47_mem2 _ hlen t ht
            have hlt := isAO2_rb hAO hj hmem
            have hnbt : ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) ((gateAt C j).inputs.getD t 0) = true →
                graphFun G ∅ x = true := by
              intro hb
              apply hLF
              exact ⟨j, hj, ⟨t, ht⟩, hcone j hj, hop, fun hb2 => hnb (fun x hx' => hb2 x hx'), hb,
                PEqualNP.EdgeOwnership.pairInput u z, hvt⟩
            have hup : ∀ y : Fin n → Bool, val C (List.ofFn y) ((gateAt C j).inputs.getD t 0) = true →
                val C (List.ofFn y) (n + j) = true := by
              intro y hy
              rw [or_val n C hAO _ (hx y) j hj hop]
              rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
              · rw [hy, Bool.true_or]
              · rw [hy, Bool.or_true]
            rcases ih _ hlt hnbt hvt with h | h | h
            · exact Or.inl (hup _ h)
            · exact Or.inr (Or.inl (hup _ h))
            · exact Or.inr (Or.inr (orReaches_step n C j _ g hj hop hmem hlt h))
          rw [or_val n C hAO _ (hx _) j hj hop, Bool.or_eq_true] at hv
          rcases hv with h | h
          · exact key 0 (by omega) h
          · exact key 1 (by omega) h
      · rw [val_ge (C := C) (hx _) (by omega)] at hv
        exact absurd hv (by simp)

theorem p47_both {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g j : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g)
    (h1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g) : False := by
  unfold PEqualNP.TopForm.BelowF at hbelow hgnb
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hjg : j ≠ g := by
    intro hjg
    subst hjg
    have b1 := (orReaches_bound n C j _ h0).1
    have b2 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
    omega
  apply hgnb
  intro x hx
  apply hbelow j hj hop hjg x
  show val C (List.ofFn x) (n + j) = true
  have hx' : val C (List.ofFn x) (n + g) = true := hx
  rw [and_val n C hAO _ (by simp) j hj hop, reach_up n C _ (by simp) g hx' _ h0,
    reach_up n C _ (by simp) g hx' _ h1]
  rfl


theorem p42_rec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (x : Fin n → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k) :
    ∀ w : ℕ, (¬ ∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true) →
      val C (List.ofFn x) w = true →
      (∃ i : Fin n, x i = true ∧ val C (List.ofFn (PEqualNP.SplitCount.unitInput i)) w = true) ∨
      PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  unfold PEqualNP.Core.IsLiftFixedPoint PEqualNP.Core.LiftApplies PEqualNP.Core.LiftAt
    PEqualNP.Core.IsImpWire at hLF
  unfold PEqualNP.TopForm.BelowF at hbelow
  have hx : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnb hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [val_ofFn_lt C x w hwn] at hv
        exact hv
      · rw [p47_unit_val C _ w hwn]
        simp
    · by_cases hwl : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
        rcases hAO.1 _ (gateAt_mem hj) with hop | hop
        · by_cases hjg : j = g
          · subst hjg
            exact Or.inr (orReaches_self n C j hj)
          · exact absurd (fun y hy' => hbelow j hj hop hjg y hy') hnb
        · have key : ∀ t : ℕ, t < 2 →
              val C (List.ofFn x) ((gateAt C j).inputs.getD t 0) = true →
              (∃ i : Fin n, x i = true ∧
                val C (List.ofFn (PEqualNP.SplitCount.unitInput i)) (n + j) = true) ∨
              PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g := by
            intro t ht hvt
            have hmem := p47_mem2 _ hlen t ht
            have hlt := isAO2_rb hAO hj hmem
            have hnbt : ¬ ∀ y : Fin n → Bool, val C (List.ofFn y) ((gateAt C j).inputs.getD t 0) = true →
                graphFun G ∅ y = true := by
              intro hb
              apply hLF
              exact ⟨j, hj, ⟨t, ht⟩, hcone j hj, hop, fun hb2 => hnb (fun y hy' => hb2 y hy'), hb,
                x, hvt⟩
            have hup : ∀ y : Fin n → Bool, val C (List.ofFn y) ((gateAt C j).inputs.getD t 0) = true →
                val C (List.ofFn y) (n + j) = true := by
              intro y hy
              rw [or_val n C hAO _ (hx y) j hj hop]
              rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
              · rw [hy, Bool.true_or]
              · rw [hy, Bool.or_true]
            rcases ih _ hlt hnbt hvt with ⟨i, hi1, hi2⟩ | h
            · exact Or.inl ⟨i, hi1, hup _ hi2⟩
            · exact Or.inr (orReaches_step n C j _ g hj hop hmem hlt h)
          rw [or_val n C hAO _ (hx _) j hj hop, Bool.or_eq_true] at hv
          rcases hv with h | h
          · exact key 0 (by omega) h
          · exact key 1 (by omega) h
      · rw [val_ge (C := C) (hx _) (by omega)] at hv
        exact absurd hv (by simp)

theorem p42_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (m : Fin n) (x : Fin n → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hg : g < C.gates.length)
    (hFx : graphFun G ∅ x = false)
    (p : ℕ) (hpm : p ∈ (gateAt C g).inputs)
    (hpnb : ¬ ∀ y : Fin n → Bool, val C (List.ofFn y) p = true → graphFun G ∅ y = true)
    (hN : ∀ y : Fin n, val C (List.ofFn (PEqualNP.SplitCount.unitInput y)) p = true → G.Adj y m)
    (hpx : val C (List.ofFn x) p = true)
    (d : ℕ) (hdnb : ¬ ∀ y : Fin n → Bool, val C (List.ofFn y) d = true → graphFun G ∅ y = true)
    (hdg : ¬ PEqualNP.CleanedNonEdge.OrReaches n C d g)
    (hk : ∀ z : Fin n, val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) d = true → z = m) :
    val C (List.ofFn x) d = false := by
  cases hd : val C (List.ofFn x) d
  · rfl
  exfalso
  rcases p42_rec G C g x hAO hLF hcone hbelow d hdnb hd with ⟨i, hi1, hi2⟩ | h
  · have him := hk i hi2
    subst him
    rcases p42_rec G C g x hAO hLF hcone hbelow p hpnb hpx with ⟨j, hj1, hj2⟩ | h2
    · have hadj := hN j hj2
      have hF : graphFun G ∅ x = true := by
        unfold graphFun
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        right
        exact ⟨j, i, hadj, hj1, hi1⟩
      rw [hFx] at hF
      exact absurd hF (by simp)
    · have b1 := (orReaches_bound n C g _ h2).1
      have b2 := isAO2_rb hAO hg hpm
      omega
  · exact hdg h

theorem p42_agree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (m : Fin n) (x : Fin n → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hg : g < C.gates.length)
    (hNB : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (hgop : (gateAt C g).op = GateOp.and)
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hpart : ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m)
    (hFx : graphFun G ∅ x = false)
    (p : ℕ) (hpm : p ∈ (gateAt C g).inputs)
    (hN : ∀ y : Fin n, val C (List.ofFn (PEqualNP.SplitCount.unitInput y)) p = true → G.Adj y m)
    (hpx : val C (List.ofFn x) p = true) :
    ∀ i, ¬ PEqualNP.CleanedNonEdge.OrReaches n C i g →
      val (eraseGate n C g p) (List.ofFn x) (eraseRedirect n g p i) = val C (List.ofFn x) i := by
  have hx : (List.ofFn x).length = n := by simp
  have hpg : p < n + g := isAO2_rb hAO hg hpm
  have hpnb := hNB g hg hgop p hpm
  have hAOE : PEqualNP.TopForm.IsAO2 n (eraseGate n C g p) := p47_isAO2_erase n C g p hg hpg hAO
  have hElen := erase_length n C g p hg
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n + g
    · rw [erase_redirect_lt n g p i h1]
      exact erase_val_lt hg hx h1
    by_cases h2 : i = n + g
    · subst h2
      exact absurd (orReaches_self n C g hg) hi
    by_cases h3 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j + 1 := ⟨i - n - 1, by omega⟩
      have hj1 : j + 1 < C.gates.length := by omega
      have hgj : g ≤ j := by omega
      rw [erase_redirect_succ n g p (n + j) (by omega)]
      have hjE : j < (eraseGate n C g p).gates.length := by omega
      have hgE : gateAt (eraseGate n C g p) j = erase_rg (eraseRedirect n g p) (gateAt C (j + 1)) :=
        erase_gateAt_ge n C g p j hg hgj hj1
      have hlen : (gateAt C (j + 1)).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj1)
      have e0 : (gateAt (eraseGate n C g p) j).inputs.getD 0 0 =
          eraseRedirect n g p ((gateAt C (j + 1)).inputs.getD 0 0) := by
        rw [hgE]; exact p47_map_getD _ _ 0 (by omega)
      have e1 : (gateAt (eraseGate n C g p) j).inputs.getD 1 0 =
          eraseRedirect n g p ((gateAt C (j + 1)).inputs.getD 1 0) := by
        rw [hgE]; exact p47_map_getD _ _ 1 (by omega)
      have eop : (gateAt (eraseGate n C g p) j).op = (gateAt C (j + 1)).op := by rw [hgE]; rfl
      have m0 := p47_mem2 _ hlen 0 (by omega)
      have m1 := p47_mem2 _ hlen 1 (by omega)
      have l0 := isAO2_rb hAO hj1 m0
      have l1 := isAO2_rb hAO hj1 m1
      have hCi : n + j + 1 = n + (j + 1) := by omega
      rw [hCi]
      rcases hAO.1 _ (gateAt_mem hj1) with hop | hop
      · rw [and_val n C hAO _ hx (j + 1) hj1 hop,
          and_val n _ hAOE _ hx j hjE (by rw [eop]; exact hop), e0, e1]
        by_cases r0 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C (j + 1)).inputs.getD 0 0) g
        · by_cases r1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C (j + 1)).inputs.getD 1 0) g
          · exact (p47_both G C g (j + 1) hAO hbelow hgnb hj1 hop r0 r1).elim
          · have hf := p42_other G C g m x hAO hLF hcone hbelow hg hFx p hpm hpnb hN hpx
              ((gateAt C (j + 1)).inputs.getD 1 0) (hNB (j + 1) hj1 hop _ m1) r1
              (fun z' hz' => hpart (j + 1) hj1 hop z' (Or.inl ⟨r0, hz'⟩))
            rw [ih _ (by omega) r1, hf]
            simp
        · by_cases r1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C (j + 1)).inputs.getD 1 0) g
          · have hf := p42_other G C g m x hAO hLF hcone hbelow hg hFx p hpm hpnb hN hpx
              ((gateAt C (j + 1)).inputs.getD 0 0) (hNB (j + 1) hj1 hop _ m0) r0
              (fun z' hz' => hpart (j + 1) hj1 hop z' (Or.inr ⟨r1, hz'⟩))
            rw [ih _ (by omega) r0, hf]
            simp
          · rw [ih _ (by omega) r0, ih _ (by omega) r1]
      · rw [or_val n C hAO _ hx (j + 1) hj1 hop,
          or_val n _ hAOE _ hx j hjE (by rw [eop]; exact hop), e0, e1]
        have r0 : ¬ PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C (j + 1)).inputs.getD 0 0) g :=
          fun h => hi (orReaches_step n C (j + 1) _ g hj1 hop m0 l0 h)
        have r1 : ¬ PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C (j + 1)).inputs.getD 1 0) g :=
          fun h => hi (orReaches_step n C (j + 1) _ g hj1 hop m1 l1 h)
        rw [ih _ (by omega) r0, ih _ (by omega) r1]
    · rw [val_ge (C := C) hx (by omega), erase_redirect_gt n g p i (by omega)]
      exact val_ge (C := eraseGate n C g p) hx (by omega)

theorem p42_core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (m : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hNB : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hg : g < C.gates.length)
    (hgop : (gateAt C g).op = GateOp.and)
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hpart : ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m)
    (t : ℕ) (ht : t < 2)
    (hN : ∀ y : Fin n, val C (List.ofFn (PEqualNP.SplitCount.unitInput y))
      ((gateAt C g).inputs.getD t 0) = true → G.Adj y m) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  have hlen : (gateAt C g).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hg)
  have hpm := p47_mem2 _ hlen t ht
  have hpg := isAO2_rb hAO hg hpm
  have hxl : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  have hgp : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + g) = true →
      val C (List.ofFn x) ((gateAt C g).inputs.getD t 0) = true := by
    intro x hx
    rw [and_val n C hAO _ (hxl x) g hg hgop, Bool.and_eq_true] at hx
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · exact hx.1
    · exact hx.2
  refine ⟨eraseGate n C g ((gateAt C g).inputs.getD t 0),
    p47_isAO2_erase n C g _ hg hpg hAO, by have := erase_size n C g ((gateAt C g).inputs.getD t 0) hg; omega, ?_⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    by_contra hFx
    rw [Bool.not_eq_true] at hFx
    by_cases hsame : val C (List.ofFn x) ((gateAt C g).inputs.getD t 0) = val C (List.ofFn x) (n + g)
    · have e := erase_eval hg hpg (hxl x) hsame
      have h2 : circuitFun n C x = true := by
        show C.eval (List.ofFn x) = true
        rw [← e]
        exact h
      rw [hF, hFx] at h2
      exact absurd h2 (by simp)
    · have hpx : val C (List.ofFn x) ((gateAt C g).inputs.getD t 0) = true := by
        cases h1 : val C (List.ofFn x) ((gateAt C g).inputs.getD t 0)
        · cases h2 : val C (List.ofFn x) (n + g)
          · exact absurd (h1.trans h2.symm) hsame
          · have h3 := hgp x h2
            rw [h1] at h3
            exact h3
        · rfl
      have hout : ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
        intro hr
        apply hgnb
        unfold PEqualNP.TopForm.BelowF
        intro y hy
        rw [← hF]
        exact reach_up n C _ (by simp) g hy _ hr
      have hag := p42_agree G C g m x hAO hLF hcone hbelow hg hNB hgop hgnb hpart hFx _ hpm hN hpx
        C.output hout
      have h2 : val (eraseGate n C g ((gateAt C g).inputs.getD t 0)) (List.ofFn x)
          (eraseGate n C g ((gateAt C g).inputs.getD t 0)).output = true := h
      rw [erase_output n C g _ hg, hag] at h2
      have h3 : circuitFun n C x = true := h2
      rw [hF, hFx] at h3
      exact absurd h3 (by simp)
  · intro h
    rw [← hF] at h
    have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
      (fun a b => a = true → b = true) (fun b hb => hb) hg hpg
      (fun op l f f' hq h => erase_hop_le _ op l f f' hq h)
      (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x) (hgp x) C.output h
    show val (eraseGate n C g ((gateAt C g).inputs.getD t 0)) (List.ofFn x)
      (eraseGate n C g ((gateAt C g).inputs.getD t 0)).output = true
    rw [erase_output n C g _ hg]
    exact hrel

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (m : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m) → ((∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m) ∨ (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g m hbip h4c hAO hF hLF hNB hcone hg hgop hgnb hbelow hpart hN
  rcases hN with hN | hN
  · exact p42_core G C g m hAO hF hLF hNB hcone hg hgop hgnb hbelow hpart 0 (by omega) hN
  · exact p42_core G C g m hAO hF hLF hNB hcone hg hgop hgnb hbelow hpart 1 (by omega) hN

end PEqualNP.Outside.L_meta_4742

theorem PEqualNP.Outside.L_meta_4742 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (m : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m) → ((∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m) ∨ (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ :=
  PEqualNP.Outside.L_meta_4742.main_aux
