import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919

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

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp),
  (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  C.gates[j]? = some { op := op, inputs := [a, b] } →
  a < n + j →
  (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = PEqualNP.CircuitLowerBounds.GateOp.eval op [] →
      PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j { op := op, inputs := [] }, output := C.output } x =
        PEqualNP.MetaComplexity.circuitFun n C x) →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] }).length =
    C.gates.length := by
  intro n C j a b op hop hg ha hforce
  obtain ⟨pre, post, hlen, h1, h2⟩ := split2 C.gates j ⟨op, [a, b]⟩ hg
  refine ⟨?_, List.length_set⟩
  funext x
  have hP : (W pre (List.ofFn x)).length = n + j := by
    rw [W_length, List.length_ofFn, hlen]
  have hWo : W C.gates (List.ofFn x)
      = W post (step (W pre (List.ofFn x)) ⟨op, [a, b]⟩) := by
    rw [h1, W_append, W_cons]
  have hWn : ∀ g2 : Gate, W (C.gates.set j g2) (List.ofFn x)
      = W post (step (W pre (List.ofFn x)) g2) := by
    intro g2
    rw [h2 g2, W_append, W_cons]
  have haP : (W C.gates (List.ofFn x)).getD a false = (W pre (List.ofFn x)).getD a false := by
    rw [hWo, W_prefix _ _ _ (by rw [step_len]; omega)]
    exact getD_app_lt _ _ a (by rw [hP]; exact ha)
  have hF := hforce x
  have ecopy : GateOp.or.eval ([a].map fun i => (W pre (List.ofFn x)).getD i false)
      = (W pre (List.ofFn x)).getD a false := by
    simp [GateOp.eval]
  show (W (C.gates.set j ⟨GateOp.or, [a]⟩) (List.ofFn x)).getD C.output false
    = (W C.gates (List.ofFn x)).getD C.output false
  change (C.wires (List.ofFn x)).getD a false = op.eval [] →
    (W (C.gates.set j ⟨op, []⟩) (List.ofFn x)).getD C.output false
      = (W C.gates (List.ofFn x)).getD C.output false at hF
  change (W C.gates (List.ofFn x)).getD a false = op.eval [] → _ at hF
  rw [haP] at hF
  rw [hWn]
  rw [hWn] at hF
  rcases hop with rfl | rfl
  · cases hv : (W pre (List.ofFn x)).getD a false
    · rw [hWo]
      congr 1
      apply congrArg
      apply step_congr
      rw [ecopy, hv]
      simp only [List.map_cons, List.map_nil, hv]
      simp [GateOp.eval]
    · rw [← hF (by rw [hv]; rfl)]
      congr 1
      apply congrArg
      apply step_congr
      rw [ecopy, hv]
      rfl
  · cases hv : (W pre (List.ofFn x)).getD a false
    · rw [← hF (by rw [hv]; rfl)]
      congr 1
      apply congrArg
      apply step_congr
      rw [ecopy, hv]
      rfl
    · rw [hWo]
      congr 1
      apply congrArg
      apply step_congr
      rw [ecopy, hv]
      simp only [List.map_cons, List.map_nil, hv]
      simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2919

theorem PEqualNP.Outside.L_meta_2919 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp),
  (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  C.gates[j]? = some { op := op, inputs := [a, b] } →
  a < n + j →
  (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = PEqualNP.CircuitLowerBounds.GateOp.eval op [] →
      PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j { op := op, inputs := [] }, output := C.output } x =
        PEqualNP.MetaComplexity.circuitFun n C x) →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] }).length =
    C.gates.length :=
  PEqualNP.Outside.L_meta_2919.main_aux
