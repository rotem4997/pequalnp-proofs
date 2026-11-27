import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace L589

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private lemma fold_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

private lemma fold_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [step_len]; omega)]
    exact step_lt w g i hi

end L589

theorem PEqualNP.Outside.L_meta_589 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (i : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x i false) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x i true)) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 4) := by
  intro n s F i h
  obtain ⟨C, hfan, hsz, o1, o2, hw⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hF : ∀ x : Fin n → Bool, F x = ((x i && F (Function.update x i true)) ||
      (!(x i) && F (Function.update x i false))) := by
    intro x
    cases hxi : x i
    · have hup : Function.update x i false = x := by
        rw [← hxi]
        exact Function.update_eq_self i x
      rw [hup]
      simp
    · have hup : Function.update x i true = x := by
        rw [← hxi]
        exact Function.update_eq_self i x
      rw [hup]
      simp
  have hW : ∀ x : Fin n → Bool, ∃ W : List Bool, W = C.gates.foldl L589.step (List.ofFn x) ∧
      W.length = n + C.gates.length ∧ W.getD (i : ℕ) false = x i ∧
      W.getD o1 false = F (Function.update x i false) ∧
      W.getD o2 false = F (Function.update x i true) := by
    intro x
    refine ⟨_, rfl, ?_, ?_, (hw x).1, (hw x).2⟩
    · rw [L589.fold_length]
      simp
    · rw [L589.fold_lt _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
  by_cases h1 : o1 < n + C.gates.length
  · refine ⟨⟨C.gates ++ [⟨GateOp.and, [(i : ℕ), o2]⟩, ⟨GateOp.not, [(i : ℕ)]⟩,
      ⟨GateOp.and, [n + C.gates.length + 1, o1]⟩,
      ⟨GateOp.or, [n + C.gates.length, n + C.gates.length + 2]⟩], n + C.gates.length + 3⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hfan g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr (Or.inr rfl), by simp⟩
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · show (C.gates ++ [(⟨GateOp.and, [(i : ℕ), o2]⟩ : Gate), ⟨GateOp.not, [(i : ℕ)]⟩,
        ⟨GateOp.and, [n + C.gates.length + 1, o1]⟩,
        ⟨GateOp.or, [n + C.gates.length, n + C.gates.length + 2]⟩]).length ≤ s + 4
      rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    · intro x
      obtain ⟨W, hWdef, hWlen, hWi, hW1, hW2⟩ := hW x
      obtain ⟨W1, hW1def⟩ : ∃ W1, W1 = L589.step W ⟨GateOp.and, [(i : ℕ), o2]⟩ := ⟨_, rfl⟩
      obtain ⟨W2, hW2def⟩ : ∃ W2, W2 = L589.step W1 ⟨GateOp.not, [(i : ℕ)]⟩ := ⟨_, rfl⟩
      obtain ⟨W3, hW3def⟩ : ∃ W3, W3 = L589.step W2 ⟨GateOp.and, [n + C.gates.length + 1, o1]⟩ :=
        ⟨_, rfl⟩
      obtain ⟨W4, hW4def⟩ : ∃ W4, W4 = L589.step W3
        ⟨GateOp.or, [n + C.gates.length, n + C.gates.length + 2]⟩ := ⟨_, rfl⟩
      have hfold : (C.gates ++ [(⟨GateOp.and, [(i : ℕ), o2]⟩ : Gate), ⟨GateOp.not, [(i : ℕ)]⟩,
          ⟨GateOp.and, [n + C.gates.length + 1, o1]⟩,
          ⟨GateOp.or, [n + C.gates.length, n + C.gates.length + 2]⟩]).foldl L589.step
          (List.ofFn x) = W4 := by
        rw [hW4def, hW3def, hW2def, hW1def, hWdef, List.foldl_append]
        rfl
      show ((C.gates ++ [(⟨GateOp.and, [(i : ℕ), o2]⟩ : Gate), ⟨GateOp.not, [(i : ℕ)]⟩,
          ⟨GateOp.and, [n + C.gates.length + 1, o1]⟩,
          ⟨GateOp.or, [n + C.gates.length, n + C.gates.length + 2]⟩]).foldl L589.step
          (List.ofFn x)).getD (n + C.gates.length + 3) false = F x
      rw [hfold]
      have hi : (i : ℕ) < n := i.isLt
      have l1 : W1.length = n + C.gates.length + 1 := by rw [hW1def, L589.step_len, hWlen]
      have l2 : W2.length = n + C.gates.length + 2 := by rw [hW2def, L589.step_len, l1]
      have l3 : W3.length = n + C.gates.length + 3 := by rw [hW3def, L589.step_len, l2]
      have ea : W1.getD (n + C.gates.length) false = (x i && F (Function.update x i true)) := by
        rw [hW1def, L589.step_last _ _ _ hWlen.symm]
        show GateOp.and.eval [W.getD (i : ℕ) false, W.getD o2 false] = _
        rw [hWi, hW2]
        simp [GateOp.eval]
      have eb : W2.getD (n + C.gates.length + 1) false = !(x i) := by
        rw [hW2def, L589.step_last _ _ _ l1.symm]
        have h0 : W1.getD (i : ℕ) false = x i := by
          rw [hW1def, L589.step_lt _ _ _ (by omega), hWi]
        show GateOp.not.eval [W1.getD (i : ℕ) false] = _
        rw [h0]
        simp [GateOp.eval]
      have ec : W3.getD (n + C.gates.length + 2) false =
          (!(x i) && F (Function.update x i false)) := by
        rw [hW3def, L589.step_last _ _ _ l2.symm]
        have h0 : W2.getD o1 false = F (Function.update x i false) := by
          rw [hW2def, L589.step_lt _ _ _ (by omega), hW1def, L589.step_lt _ _ _ (by omega), hW1]
        show GateOp.and.eval [W2.getD (n + C.gates.length + 1) false, W2.getD o1 false] = _
        rw [eb, h0]
        simp [GateOp.eval]
      have ed : W4.getD (n + C.gates.length + 3) false =
          ((x i && F (Function.update x i true)) || (!(x i) && F (Function.update x i false))) := by
        rw [hW4def, L589.step_last _ _ _ l3.symm]
        have h0 : W3.getD (n + C.gates.length) false = (x i && F (Function.update x i true)) := by
          rw [hW3def, L589.step_lt _ _ _ (by omega), hW2def, L589.step_lt _ _ _ (by omega), ea]
        show GateOp.or.eval [W3.getD (n + C.gates.length) false,
          W3.getD (n + C.gates.length + 2) false] = _
        rw [h0, ec]
        simp [GateOp.eval]
      rw [ed, ← hF x]
  · have hF0 : ∀ x : Fin n → Bool, F (Function.update x i false) = false := by
      intro x
      obtain ⟨W, hWdef, hWlen, hWi, hW1, hW2⟩ := hW x
      rw [← hW1]
      exact List.getD_eq_default _ _ (by omega)
    refine ⟨⟨C.gates ++ [⟨GateOp.and, [(i : ℕ), o2]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hfan g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rw [hg]
        exact ⟨Or.inl rfl, by simp⟩
    · show (C.gates ++ [(⟨GateOp.and, [(i : ℕ), o2]⟩ : Gate)]).length ≤ s + 4
      rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    · intro x
      obtain ⟨W, hWdef, hWlen, hWi, hW1, hW2⟩ := hW x
      have hfold : (C.gates ++ [(⟨GateOp.and, [(i : ℕ), o2]⟩ : Gate)]).foldl L589.step
          (List.ofFn x) = L589.step W ⟨GateOp.and, [(i : ℕ), o2]⟩ := by
        rw [hWdef, List.foldl_append]
        rfl
      show ((C.gates ++ [(⟨GateOp.and, [(i : ℕ), o2]⟩ : Gate)]).foldl L589.step
          (List.ofFn x)).getD (n + C.gates.length) false = F x
      rw [hfold, L589.step_last _ _ _ hWlen.symm, hF x, hF0 x]
      show GateOp.and.eval [W.getD (i : ℕ) false, W.getD o2 false] = _
      rw [hWi, hW2]
      simp [GateOp.eval]
