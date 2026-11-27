import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def effRead (g : Gate) (k : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some k) ∨ (g.op ≠ GateOp.not ∧ k ∈ g.inputs)

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]; omega

private lemma getD_append_left_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact getD_append_left_lt w _ i false hi

private lemma gate_eval_eq_of_not_effRead (g : Gate) (k : ℕ) (hno : ¬ effRead g k)
    (w₁ w₂ : List Bool) (hagree : ∀ i, i ≠ k → w₁.getD i false = w₂.getD i false) :
    g.op.eval (g.inputs.map fun i => w₁.getD i false) =
    g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
  by_cases hnot : g.op = GateOp.not
  · have hhead : g.inputs.head? ≠ some k := fun h => hno (Or.inl ⟨hnot, h⟩)
    rw [hnot]
    cases hi : g.inputs with
    | nil => rfl
    | cons a as =>
      have hak : a ≠ k := fun h => hhead (by simp [hi, h])
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      rw [hagree a hak]
  · have hmem : k ∉ g.inputs := fun h => hno (Or.inr ⟨hnot, h⟩)
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hagree i (fun h => hmem (h ▸ hi))

private lemma foldl_agree_ne (gs : List Gate) (k : ℕ) (hno : ∀ g ∈ gs, ¬ effRead g k)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length) (hk : k < w₁.length)
    (hagree : ∀ i, i ≠ k → w₁.getD i false = w₂.getD i false) :
    ∀ i, i ≠ k → (gs.foldl step w₁).getD i false = (gs.foldl step w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hagree
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))
      (step w₁ g) (step w₂ g) (by simp [step, hlen]) (by simp [step]; omega)
    intro i hik
    rcases lt_trichotomy i w₁.length with hlt | rfl | hgt
    · rw [step, getD_append_left_lt _ _ _ _ hlt, step, getD_append_left_lt _ _ _ _ (by omega)]
      exact hagree i hik
    · rw [step, getD_snoc_eq, step, hlen, getD_snoc_eq]
      exact gate_eval_eq_of_not_effRead g k (hno g List.mem_cons_self) w₁ w₂ hagree
    · rw [List.getD_eq_default _ _ (by simp [step]; omega),
          List.getD_eq_default _ _ (by simp [step]; omega)]

private def p9 (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

private lemma ofFn_getD_lt (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]

private lemma wires_getD_input (C : Circuit) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  change (C.gates.foldl step (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [foldl_getD_lt C.gates (List.ofFn x) i (by simp; exact hi)]
  exact ofFn_getD_lt x i hi

private lemma step_one_agree (C : Circuit) (g0 : Gate) (rest : List Gate)
    (hgates : C.gates = g0 :: rest)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (x y : Fin 9 → Bool) (k : ℕ) (_hk : k < 9)
    (hxy : ∀ j : Fin 9, (j : ℕ) ≠ k → x j = y j)
    (h9eq : (x 0 || x 2) = (y 0 || y 2)) :
    ∀ i, i ≠ k → (step (List.ofFn x) g0).getD i false = (step (List.ofFn y) g0).getD i false := by
  have hlenx : (step (List.ofFn x) g0).length = 10 := by simp [step]
  have hleny : (step (List.ofFn y) g0).length = 10 := by simp [step]
  have h9x : (step (List.ofFn x) g0).getD 9 false = (x 0 || x 2) := by
    have := h9 x
    change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at this
    rw [hgates, List.foldl_cons, foldl_getD_lt rest _ 9 (by omega)] at this
    exact this
  have h9y : (step (List.ofFn y) g0).getD 9 false = (y 0 || y 2) := by
    have := h9 y
    change (C.gates.foldl step (List.ofFn y)).getD 9 false = _ at this
    rw [hgates, List.foldl_cons, foldl_getD_lt rest _ 9 (by omega)] at this
    exact this
  intro i hik
  by_cases hi9 : i < 9
  · rw [step, getD_append_left_lt _ _ _ _ (by simp; exact hi9),
        step, getD_append_left_lt _ _ _ _ (by simp; exact hi9),
        ofFn_getD_lt x i hi9, ofFn_getD_lt y i hi9]
    exact hxy ⟨i, hi9⟩ hik
  · by_cases hieq : i = 9
    · subst hieq; rw [h9x, h9y, h9eq]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem main (C : Circuit)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hFun : circuitFun 9 C = p9)
    (k : ℕ) (hk02 : k = 0 ∨ k = 2) :
    ∃ g ∈ C.gates.drop 1, effRead g k := by
  cases hgates : C.gates with
  | nil =>
    have := h9 (fun i => decide (i = 0))
    have hnil : (C.wires (List.ofFn (fun i : Fin 9 => decide (i = 0)))).getD 9 false = false := by
      change (C.gates.foldl step _).getD 9 false = false
      rw [hgates, List.foldl_nil, List.getD_eq_default _ _ (by simp)]
    rw [hnil] at this
    simp at this
  | cons g0 rest =>
    dsimp only [List.drop]
    by_contra hno
    push Not at hno
    have hout_ne : C.output ≠ k := by
      intro heq
      rcases hk02 with rfl | rfl
      · have h1 := congrFun hFun (fun i : Fin 9 => decide (i = 0))
        change (C.wires (List.ofFn (fun i : Fin 9 => decide (i = 0)))).getD C.output false = _ at h1
        rw [heq, wires_getD_input C _ 0 (by omega)] at h1
        simp [p9] at h1
      · have h1 := congrFun hFun (fun i : Fin 9 => decide (i = 2))
        change (C.wires (List.ofFn (fun i : Fin 9 => decide (i = 2)))).getD C.output false = _ at h1
        rw [heq, wires_getD_input C _ 2 (by omega)] at h1
        simp [p9] at h1
    rcases hk02 with rfl | rfl
    · let xa : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 4)
      let xb : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 4)
      have h1 := step_one_agree C g0 rest hgates h9 xa xb 0 (by omega)
        (fun j hj => by fin_cases j <;> simp_all [xa, xb])
        (by decide)
      have h2 := foldl_agree_ne rest 0 hno (step (List.ofFn xa) g0) (step (List.ofFn xb) g0)
        (by simp [step]) (by simp [step]) h1 C.output hout_ne
      have hca := congrFun hFun xa
      have hcb := congrFun hFun xb
      change (C.gates.foldl step (List.ofFn xa)).getD C.output false = p9 xa at hca
      change (C.gates.foldl step (List.ofFn xb)).getD C.output false = p9 xb at hcb
      rw [hgates, List.foldl_cons] at hca hcb
      have heq : p9 xa = p9 xb := hca.symm.trans (h2.trans hcb)
      revert heq; decide
    · let xa : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 3)
      let xb : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 3)
      have h1 := step_one_agree C g0 rest hgates h9 xa xb 2 (by omega)
        (fun j hj => by fin_cases j <;> simp_all [xa, xb])
        (by decide)
      have h2 := foldl_agree_ne rest 2 hno (step (List.ofFn xa) g0) (step (List.ofFn xb) g0)
        (by simp [step]) (by simp [step]) h1 C.output hout_ne
      have hca := congrFun hFun xa
      have hcb := congrFun hFun xb
      change (C.gates.foldl step (List.ofFn xa)).getD C.output false = p9 xa at hca
      change (C.gates.foldl step (List.ofFn xb)).getD C.output false = p9 xb at hcb
      rw [hgates, List.foldl_cons] at hca hcb
      have heq : p9 xa = p9 xb := hca.symm.trans (h2.trans hcb)
      revert heq; decide

end PEqualNP.Outside.L_meta_3081_aux

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 :=
  PEqualNP.Outside.L_meta_3081_aux.main
