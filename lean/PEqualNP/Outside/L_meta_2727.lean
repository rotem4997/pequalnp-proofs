import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2727

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem split_at (gs : List Gate) : ∀ (j : ℕ) (g g2 : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g g2 h; simp at h
  | cons a gs ih =>
    intro j g g2 h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g g2 h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) e2

theorem core2 (P : List Bool) (post : List Gate) (u t : ℕ) (hu : u < P.length) (ht : t < P.length)
    (himp : (W post (step P ⟨GateOp.and, [u, t]⟩)).getD u false = true →
      (W post (step P ⟨GateOp.and, [u, t]⟩)).getD t false = true) :
    W post (step P ⟨GateOp.or, [u]⟩) = W post (step P ⟨GateOp.and, [u, t]⟩) := by
  have hu2 : (W post (step P ⟨GateOp.and, [u, t]⟩)).getD u false = P.getD u false := by
    rw [W_prefix _ _ _ (by rw [step_len]; omega)]
    exact getD_app_lt P _ u hu
  have ht2 : (W post (step P ⟨GateOp.and, [u, t]⟩)).getD t false = P.getD t false := by
    rw [W_prefix _ _ _ (by rw [step_len]; omega)]
    exact getD_app_lt P _ t ht
  rw [hu2, ht2] at himp
  have e1 : GateOp.or.eval ([u].map fun i => P.getD i false) = P.getD u false := by
    simp [GateOp.eval]
  have e2 : GateOp.and.eval ([u, t].map fun i => P.getD i false)
      = (P.getD u false && P.getD t false) := by
    simp [GateOp.eval]
  have hstep : step P ⟨GateOp.or, [u]⟩ = step P ⟨GateOp.and, [u, t]⟩ := by
    show P ++ [GateOp.or.eval ([u].map fun i => P.getD i false)]
      = P ++ [GateOp.and.eval ([u, t].map fun i => P.getD i false)]
    rw [e1, e2]
    cases hpu : P.getD u false
    · rfl
    · rw [himp hpu]
      rfl
  rw [hstep]

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
  u < n + j → t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
      (C.wires (List.ofFn x)).getD t false = true) →
  ∀ x : Fin n → Bool,
    ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
       output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
    C.wires (List.ofFn x) := by
  intro n C j u t _ hg hu ht himp x
  obtain ⟨pre, post, hlen, h1, h2⟩ :=
    split_at C.gates j ⟨GateOp.and, [u, t]⟩ ⟨GateOp.or, [u]⟩ hg
  have hP : (W pre (List.ofFn x)).length = n + j := by
    rw [W_length, List.length_ofFn, hlen]
  have hWo : W C.gates (List.ofFn x)
      = W post (step (W pre (List.ofFn x)) ⟨GateOp.and, [u, t]⟩) := by
    rw [h1, W_append, W_cons]
  have hWn : W (C.gates.set j ⟨GateOp.or, [u]⟩) (List.ofFn x)
      = W post (step (W pre (List.ofFn x)) ⟨GateOp.or, [u]⟩) := by
    rw [h2, W_append, W_cons]
  have hi : (W C.gates (List.ofFn x)).getD u false = true →
      (W C.gates (List.ofFn x)).getD t false = true := himp x
  show W (C.gates.set j ⟨GateOp.or, [u]⟩) (List.ofFn x) = W C.gates (List.ofFn x)
  rw [hWn, hWo]
  rw [hWo] at hi
  exact core2 (W pre (List.ofFn x)) post u t (by rw [hP]; exact hu) (by rw [hP]; exact ht) hi

end PEqualNP.Outside.L_meta_2727

theorem PEqualNP.Outside.L_meta_2727 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
  u < n + j → t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
      (C.wires (List.ofFn x)).getD t false = true) →
  ∀ x : Fin n → Bool,
    ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
       output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
    C.wires (List.ofFn x) :=
  PEqualNP.Outside.L_meta_2727.main_aux
