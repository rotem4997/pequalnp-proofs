import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2210_1 :
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
      (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      D.size = 14 →
      (∀ i ∈ ([0, 2, 9] : List ℕ), ∃ h : PEqualNP.CircuitLowerBounds.Gate,
        h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        D.gates.filter (fun g => decide (i ∈ g.inputs)) = [h]) →
      (D.gates.filter (fun g => decide (0 ∈ g.inputs ∨ 2 ∈ g.inputs ∨ 9 ∈ g.inputs))).length = 3 →
      (∀ i ∈ ([4, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2) →
      (∃ i : ℕ, i < 14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ j : ℕ, j < 14 → (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = i) →
      ¬ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 2]) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
      (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      D.size = 14 →
      (∀ i ∈ ([0, 2, 9] : List ℕ), ∃ h : PEqualNP.CircuitLowerBounds.Gate,
        h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        D.gates.filter (fun g => decide (i ∈ g.inputs)) = [h]) →
      (D.gates.filter (fun g => decide (0 ∈ g.inputs ∨ 2 ∈ g.inputs ∨ 9 ∈ g.inputs))).length = 3 →
      (∀ i ∈ ([4, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2) →
      (∃ i j : ℕ, i < j ∧ j < 14 ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ¬ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 2]) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))) →
    ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
      (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      D.size = 14 →
      (∃ h : PEqualNP.CircuitLowerBounds.Gate, h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        D.gates.filter (fun g => decide (9 ∈ g.inputs)) = [h]) →
      (∀ i ∈ ([0, 2] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length = 1) →
      (∀ i ∈ ([4, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2) →
      (∀ i : Fin 9, (D.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3) →
      ¬ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 2]) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) := by
  classical
  intro hDel4 hDel0 hOneNot hMultiNot D hDfan hDrb hDclean hDsz h9ex h02len h467 _ hDev
  let F9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let F8d4 : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let F8d0 : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have list_le2 : ∀ l : List ℕ, l.length ≤ 2 → l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
    intro l hl
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨a, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
    · simp at hl
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro w; simp
    | append_singleton gs g ih =>
      intro w
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl stepW w) ++ [_]).length = w.length + (gs ++ [g]).length
      simp only [List.length_append, List.length_cons, List.length_nil, ih]
      omega
  have getD_snoc_lt : ∀ {α : Type} (l : List α) (a d : α) (i : ℕ), i < l.length →
      (l ++ [a]).getD i d = l.getD i d := by
    intro α l a d i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ {α : Type} (l : List α) (a d : α),
      (l ++ [a]).getD l.length d = a := by
    intro α l a d
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length)]
    simp
  have getD_ge : ∀ {α : Type} (l : List α) (d : α) (i : ℕ), l.length ≤ i →
      l.getD i d = d := by
    intro α l d i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro _ _ _; rfl
    | append_singleton gs g ih =>
      intro w i hi
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlt : i < (gs.foldl stepW w).length := by rw [foldl_len]; omega
      change ((gs.foldl stepW w) ++ [_]).getD i false = w.getD i false
      rw [getD_snoc_lt _ _ _ i hlt]
      exact ih w i hi
  have wire_agree : ∀ (gs : List Gate) (w1 w2 : List Bool) (bad : ℕ → Prop),
      w1.length = w2.length →
      (∀ i < w1.length, ¬ bad i → w1.getD i false = w2.getD i false) →
      (∀ j < gs.length, ∀ g, gs[j]? = some g → ¬ bad (w1.length + j) → ∀ i ∈ g.inputs, ¬ bad i) →
      ∀ k < (gs.foldl stepW w1).length, ¬ bad k →
        (gs.foldl stepW w1).getD k false = (gs.foldl stepW w2).getD k false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro w1 w2 bad _ hbase _ k hk hnb
      simp only [List.foldl_nil] at hk ⊢; exact hbase k hk hnb
    | append_singleton gs g ih =>
      intro w1 w2 bad hlen hbase hstep k hk hnb
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hk ⊢
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hl1 : (gs.foldl stepW w1).length = w1.length + gs.length := foldl_len gs w1
      have hl2 : (gs.foldl stepW w2).length = w1.length + gs.length := by rw [foldl_len, ← hlen]
      have hprev_eq : ∀ u < w1.length + gs.length, ¬ bad u →
          (gs.foldl stepW w1).getD u false = (gs.foldl stepW w2).getD u false := by
        intro u hu hnu
        apply ih w1 w2 bad hlen hbase (by
          intro j hj g' hgj hnb'
          apply hstep j (by simp; omega) g' (by rw [List.getElem?_append_left hj]; exact hgj) hnb') u (by omega) hnu
      change k < ((gs.foldl stepW w1) ++ [_]).length at hk
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      by_cases hlt : k < w1.length + gs.length
      · change ((gs.foldl stepW w1) ++ [_]).getD k false = ((gs.foldl stepW w2) ++ [_]).getD k false
        rw [getD_snoc_lt _ _ _ k (by omega), getD_snoc_lt _ _ _ k (by omega)]
        exact hprev_eq k hlt hnb
      · have hkeq : k = w1.length + gs.length := by omega
        subst hkeq
        change ((gs.foldl stepW w1) ++ [_]).getD (w1.length + gs.length) false =
          ((gs.foldl stepW w2) ++ [_]).getD (w1.length + gs.length) false
        rw [← hl1, getD_snoc_eq, hl1, ← hl2, getD_snoc_eq]
        congr 1
        apply List.map_congr_left
        intro a ha
        have hna : ¬ bad a := hstep gs.length (by simp) g
          (by rw [List.getElem?_append_right (le_refl gs.length)]; simp) hnb a ha
        by_cases halt : a < w1.length + gs.length
        · exact hprev_eq a halt hna
        · rw [getD_ge _ false a (by omega), getD_ge _ false a (by omega)]
  -- Constant-propagation simplifier with dropped-gate and constant-output accounting
  have simplify : ∀ (m n_in n_out : ℕ)
      (w_in w_out : (Fin m → Bool) → List Bool)
      (init : List (ℕ ⊕ Bool)) (gs : List Gate),
      (∀ y, (w_in y).length = n_in) →
      (∀ y, (w_out y).length = n_out) →
      init.length = n_in →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i < n_in, ∀ y : Fin m → Bool,
        Sum.elim (fun w => (w_out y).getD w false) id (init.getD i (Sum.inr false)) = (w_in y).getD i false) →
      (∀ i < n_in, ∀ w, init.getD i (Sum.inr false) = Sum.inl w → w < n_out) →
      ∃ (gs' : List Gate) (env : List (ℕ ⊕ Bool)) (dropped : Finset ℕ),
        env.length = n_in + gs.length ∧
        (∀ i < n_in, env.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
        (∀ j ∈ dropped, j < gs.length) ∧
        gs'.length + dropped.card ≤ gs.length ∧
        (∀ j < gs.length, ∀ g : Gate, gs[j]? = some g →
          ((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
           ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a ∈ g.inputs, a < n_in + j ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b)) →
          j ∈ dropped) ∧
        (∀ j < gs.length, ∀ g : Gate, gs[j]? = some g →
          ((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
           (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a < n_in + j ∧ env.getD a (Sum.inr false) = Sum.inr false) ∨
           (g.op = GateOp.or ∧ ∃ a b, g.inputs = [a, b] ∧ a < n_in + j ∧ b < n_in + j ∧
             (∃ ba, env.getD a (Sum.inr false) = Sum.inr ba) ∧
             (∃ bb, env.getD b (Sum.inr false) = Sum.inr bb))) →
          ∃ b, env.getD (n_in + j) (Sum.inr false) = Sum.inr b) ∧
        (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        (∀ j < gs'.length, ∀ i ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
        (∀ g ∈ gs', (g.op = GateOp.not → g.inputs.length = 1) ∧
          (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
        (∀ k < env.length, ∀ w, env.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs'.length) ∧
        (∀ k < env.length, ∀ y : Fin m → Bool,
          Sum.elim (fun w => (gs'.foldl stepW (w_out y)).getD w false) id (env.getD k (Sum.inr false)) =
            (gs.foldl stepW (w_in y)).getD k false) := by
    intro m n_in n_out w_in w_out init gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ _ hlen _ heval hbd
      refine ⟨[], init, ∅, by simp [hlen], fun _ _ => rfl, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ hj; simp at hj
      · intro _ hj; simp at hj
      · intro _ hj; simp at hj
      · intro _ hg; simp at hg
      · intro _ hj; simp at hj
      · intro _ hg; simp at hg
      · intro k hk w hw; rw [hlen] at hk; simpa using hbd k hk w hw
      · intro k hk y; rw [hlen] at hk; simpa using heval k hk y
    | append_singleton gs g ih =>
      intro hwin hwout hlen hfan heval hbd
      have hfan_gs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
        fun h hh => hfan h (List.mem_append_left _ hh)
      have hfan_g : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
        hfan g (List.mem_append_right _ (List.mem_singleton_self g))
      obtain ⟨gs', env, dropped, henv_len, hinit_eq, hdrop_lt, hsz, hdrop_c, hprop_c,
        hgs'_fan, hgs'_rb, hgs'_clean, hgs'_bd, hgs'_ev⟩ :=
        ih hwin hwout hlen hfan_gs heval hbd
      let lookup : ℕ → ℕ ⊕ Bool := fun i =>
        if i < env.length then env.getD i (Sum.inr false) else Sum.inr false
      have lookup_bd : ∀ i w, lookup i = Sum.inl w → w < n_out + gs'.length := by
        intro i w hw
        dsimp [lookup] at hw
        by_cases hi : i < env.length
        · simp only [hi, ↓reduceIte] at hw; exact hgs'_bd i hi w hw
        · simp only [hi, ↓reduceIte] at hw; cases hw
      have lookup_ev : ∀ i (y : Fin m → Bool),
          Sum.elim (fun w => (gs'.foldl stepW (w_out y)).getD w false) id (lookup i) =
            (gs.foldl stepW (w_in y)).getD i false := by
        intro i y
        dsimp [lookup]
        by_cases hi : i < env.length
        · simp only [hi, ↓reduceIte]; exact hgs'_ev i hi y
        · simp only [hi, ↓reduceIte]
          have hglen : (gs.foldl stepW (w_in y)).length = env.length := by
            rw [foldl_len, hwin y, henv_len]
          symm; exact getD_ge _ false i (by omega)
      have finish_no_add : ∀ (v_out : ℕ ⊕ Bool),
          (((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + gs.length ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
            (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a < n_in + gs.length ∧ env.getD a (Sum.inr false) = Sum.inr false) ∨
            (g.op = GateOp.or ∧ ∃ a b, g.inputs = [a, b] ∧ a < n_in + gs.length ∧ b < n_in + gs.length ∧
              (∃ ba, env.getD a (Sum.inr false) = Sum.inr ba) ∧
              (∃ bb, env.getD b (Sum.inr false) = Sum.inr bb))) →
            ∃ b, v_out = Sum.inr b) →
          (∀ w, v_out = Sum.inl w → w < n_out + gs'.length) →
          (∀ y : Fin m → Bool,
            Sum.elim (fun w => (gs'.foldl stepW (w_out y)).getD w false) id v_out =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepW (w_in y)).getD i false)) →
          ∃ (gs1 : List Gate) (env1 : List (ℕ ⊕ Bool)) (drop1 : Finset ℕ),
            env1.length = n_in + (gs ++ [g]).length ∧
            (∀ i < n_in, env1.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
            (∀ j ∈ drop1, j < (gs ++ [g]).length) ∧
            gs1.length + drop1.card ≤ (gs ++ [g]).length ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b)) →
              j ∈ drop1) ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               (h.op = GateOp.and ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ env1.getD a (Sum.inr false) = Sum.inr false) ∨
               (h.op = GateOp.or ∧ ∃ a b, h.inputs = [a, b] ∧ a < n_in + j ∧ b < n_in + j ∧
                 (∃ ba, env1.getD a (Sum.inr false) = Sum.inr ba) ∧
                 (∃ bb, env1.getD b (Sum.inr false) = Sum.inr bb))) →
              ∃ b, env1.getD (n_in + j) (Sum.inr false) = Sum.inr b) ∧
            (∀ h ∈ gs1, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
            (∀ j < gs1.length, ∀ i ∈ (gs1.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
            (∀ h ∈ gs1, (h.op = GateOp.not → h.inputs.length = 1) ∧
              (h.op ≠ GateOp.not → h.inputs.length = 2 ∧ h.inputs.Nodup)) ∧
            (∀ k < env1.length, ∀ w, env1.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs1.length) ∧
            (∀ k < env1.length, ∀ y : Fin m → Bool,
              Sum.elim (fun w => (gs1.foldl stepW (w_out y)).getD w false) id (env1.getD k (Sum.inr false)) =
                ((gs ++ [g]).foldl stepW (w_in y)).getD k false) := by
        intro v_out hv_prop hv_bd hv_ev
        refine ⟨gs', env ++ [v_out], insert gs.length dropped, ?_, ?_, ?_, ?_, ?_, ?_, hgs'_fan, hgs'_rb, hgs'_clean, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, henv_len]; omega
        · intro i hi; rw [getD_snoc_lt env v_out _ i (by omega)]; exact hinit_eq i hi
        · intro j hj
          simp only [List.length_append, List.length_cons, List.length_nil]
          rcases Finset.mem_insert.mp hj with rfl | hjd
          · omega
          · have := hdrop_lt j hjd; omega
        · have hnotmem : gs.length ∉ dropped := fun hm => by have := hdrop_lt gs.length hm; omega
          rw [Finset.card_insert_of_notMem hnotmem]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            refine Finset.mem_insert_of_mem (hdrop_c j hlt h hgj ?_)
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨hao, a, hain, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inr ⟨hao, a, hain, halt, b, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq; exact Finset.mem_insert_self _ _
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            rw [getD_snoc_lt env v_out _ (n_in + j) (by omega)]
            apply hprop_c j hlt h hgj
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩ | ⟨ho, a, b, hab, halt, hblt, ⟨ba, hba⟩, ⟨bb, hbb⟩⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inr (Or.inl ⟨ha, a, hain, halt, hb⟩)
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hba
              rw [getD_snoc_lt env v_out _ b (by omega)] at hbb
              exact Or.inr (Or.inr ⟨ho, a, b, hab, halt, hblt, ⟨ba, hba⟩, ⟨bb, hbb⟩⟩)
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            rw [← henv_len, getD_snoc_eq]
            apply hv_prop
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩ | ⟨ho, a, b, hab, halt, hblt, ⟨ba, hba⟩, ⟨bb, hbb⟩⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inr (Or.inl ⟨ha, a, hain, halt, hb⟩)
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hba
              rw [getD_snoc_lt env v_out _ b (by omega)] at hbb
              exact Or.inr (Or.inr ⟨ho, a, b, hab, halt, hblt, ⟨ba, hba⟩, ⟨bb, hbb⟩⟩)
        · intro k hk w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env v_out _ k hlt] at hw; exact hgs'_bd k hlt w hw
          · have hkeq : k = env.length := by omega
            subst hkeq; rw [getD_snoc_eq] at hw; exact hv_bd w hw
        · intro k hk y
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hglen : (gs.foldl stepW (w_in y)).length = env.length := by rw [foldl_len, hwin y, henv_len]
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env v_out _ k hlt]
            change _ = ((gs.foldl stepW (w_in y)) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega)]
            exact hgs'_ev k hlt y
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq, hv_ev y, ← hglen]
            change _ = ((gs.foldl stepW (w_in y)) ++ [_]).getD (gs.foldl stepW (w_in y)).length false
            rw [getD_snoc_eq]
      have finish_add : ∀ (g_new : Gate),
          ¬ ((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + gs.length ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
             ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a ∈ g.inputs, a < n_in + gs.length ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b)) →
          (g_new.op = GateOp.and ∨ g_new.op = GateOp.or ∨ g_new.op = GateOp.not) ∧ g_new.inputs.length ≤ 2 →
          (∀ i ∈ g_new.inputs, i < n_out + gs'.length) →
          (g_new.op = GateOp.not → g_new.inputs.length = 1) ∧
            (g_new.op ≠ GateOp.not → g_new.inputs.length = 2 ∧ g_new.inputs.Nodup) →
          (∀ y : Fin m → Bool,
            g_new.op.eval (g_new.inputs.map fun i => (gs'.foldl stepW (w_out y)).getD i false) =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepW (w_in y)).getD i false)) →
          ∃ (gs1 : List Gate) (env1 : List (ℕ ⊕ Bool)) (drop1 : Finset ℕ),
            env1.length = n_in + (gs ++ [g]).length ∧
            (∀ i < n_in, env1.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
            (∀ j ∈ drop1, j < (gs ++ [g]).length) ∧
            gs1.length + drop1.card ≤ (gs ++ [g]).length ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b)) →
              j ∈ drop1) ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               (h.op = GateOp.and ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ env1.getD a (Sum.inr false) = Sum.inr false) ∨
               (h.op = GateOp.or ∧ ∃ a b, h.inputs = [a, b] ∧ a < n_in + j ∧ b < n_in + j ∧
                 (∃ ba, env1.getD a (Sum.inr false) = Sum.inr ba) ∧
                 (∃ bb, env1.getD b (Sum.inr false) = Sum.inr bb))) →
              ∃ b, env1.getD (n_in + j) (Sum.inr false) = Sum.inr b) ∧
            (∀ h ∈ gs1, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
            (∀ j < gs1.length, ∀ i ∈ (gs1.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
            (∀ h ∈ gs1, (h.op = GateOp.not → h.inputs.length = 1) ∧
              (h.op ≠ GateOp.not → h.inputs.length = 2 ∧ h.inputs.Nodup)) ∧
            (∀ k < env1.length, ∀ w, env1.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs1.length) ∧
            (∀ k < env1.length, ∀ y : Fin m → Bool,
              Sum.elim (fun w => (gs1.foldl stepW (w_out y)).getD w false) id (env1.getD k (Sum.inr false)) =
                ((gs ++ [g]).foldl stepW (w_in y)).getD k false) := by
        intro g_new hno_c hgn_fan hgn_rb hgn_clean hgn_ev
        refine ⟨gs' ++ [g_new], env ++ [Sum.inl (n_out + gs'.length)], dropped, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, henv_len]; omega
        · intro i hi; rw [getD_snoc_lt env _ _ i (by omega)]; exact hinit_eq i hi
        · intro j hj; simp only [List.length_append, List.length_cons, List.length_nil]; have := hdrop_lt j hj; omega
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            apply hdrop_c j hlt h hgj
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨hao, a, hain, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨hao, a, hain, halt, b, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            exfalso; apply hno_c
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨hao, a, hain, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨hao, a, hain, halt, b, hb⟩
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            rw [getD_snoc_lt env _ _ (n_in + j) (by omega)]
            apply hprop_c j hlt h hgj
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩ | ⟨ho, a, b, hab, halt, hblt, ⟨ba, hba⟩, ⟨bb, hbb⟩⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr (Or.inl ⟨ha, a, hain, halt, hb⟩)
            · rw [getD_snoc_lt env _ _ a (by omega)] at hba
              rw [getD_snoc_lt env _ _ b (by omega)] at hbb
              exact Or.inr (Or.inr ⟨ho, a, b, hab, halt, hblt, ⟨ba, hba⟩, ⟨bb, hbb⟩⟩)
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            exfalso; apply hno_c
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩ | ⟨ho, a, b, hab, halt, _, ⟨ba, hba⟩, _⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨Or.inl ha, a, hain, halt, false, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hba
              exact Or.inr ⟨Or.inr ho, a, by rw [hab]; simp, halt, ba, hba⟩
        · intro h hh
          rcases List.mem_append.mp hh with h1 | h2
          · exact hgs'_fan h h1
          · rw [List.mem_singleton.mp h2]; exact hgn_fan
        · intro j hj i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs'.length
          · rw [getD_snoc_lt gs' g_new _ j hlt] at hi; exact hgs'_rb j hlt i hi
          · have hjeq : j = gs'.length := by omega
            subst hjeq; rw [getD_snoc_eq] at hi; exact hgn_rb i hi
        · intro h hh
          rcases List.mem_append.mp hh with h1 | h2
          · exact hgs'_clean h h1
          · rw [List.mem_singleton.mp h2]; exact hgn_clean
        · intro k hk w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hk ⊢
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env _ _ k hlt] at hw; have := hgs'_bd k hlt w hw; omega
          · have hkeq : k = env.length := by omega
            subst hkeq; rw [getD_snoc_eq] at hw; injection hw with hw'; omega
        · intro k hk y
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hglen : (gs.foldl stepW (w_in y)).length = env.length := by rw [foldl_len, hwin y, henv_len]
          have hglen' : (gs'.foldl stepW (w_out y)).length = n_out + gs'.length := by rw [foldl_len, hwout y]
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env _ _ k hlt]
            change _ = ((gs.foldl stepW (w_in y)) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega)]
            have hprev := hgs'_ev k hlt y
            rcases hval : env.getD k (Sum.inr false) with w | b
            · rw [hval] at hprev
              dsimp only [Sum.elim_inl] at hprev ⊢
              have hwlt : w < (gs'.foldl stepW (w_out y)).length := by
                have := hgs'_bd k hlt w hval; omega
              change ((gs'.foldl stepW (w_out y)) ++ [_]).getD w false = _
              rw [getD_snoc_lt _ _ _ w hwlt]
              exact hprev
            · rw [hval] at hprev; exact hprev
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq]
            dsimp only [Sum.elim_inl]
            rw [← hglen', ← hglen]
            change ((gs'.foldl stepW (w_out y)) ++ [_]).getD (gs'.foldl stepW (w_out y)).length false =
              ((gs.foldl stepW (w_in y)) ++ [_]).getD (gs.foldl stepW (w_in y)).length false
            rw [getD_snoc_eq, getD_snoc_eq]
            exact hgn_ev y
      rcases hfan_g.1 with hop | hop | hop
      · rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr true) (fun _ => ⟨true, rfl⟩) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_and]; rfl)
        · refine finish_no_add (lookup a) ?_ (lookup_bd a) (fun y => by
            rw [hop, hins, eval_and]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact lookup_ev a y)
          intro hc
          rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩ | ⟨ho, _⟩
          · rw [hop] at hn; exact GateOp.noConfusion hn
          · rw [hins, List.mem_singleton] at hc_in; subst hc_in
            refine ⟨false, ?_⟩; dsimp [lookup]
            have hlt : c < env.length := by omega
            simp only [hlt, ↓reduceIte, hcf]
          · rw [hop] at ho; exact GateOp.noConfusion ho
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                refine finish_no_add (Sum.inl w1) ?_
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl] at ha hb ⊢
                    rw [← ha, ← hb, Bool.and_self])
                intro hc; exfalso
                rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩ | ⟨ho, _⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hins] at hc_in
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                  have hlt : c < env.length := by omega
                  rcases hc_in with rfl | rfl
                  · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                  · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hcf] at hub; cases hub
                · rw [hop] at ho; exact GateOp.noConfusion ho
              · have hno_c : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
                    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc)) := by
                  intro hc
                  rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, bc, hbc⟩
                  · rw [hop] at hn; exact GateOp.noConfusion hn
                  · rw [hins] at hc_in
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                    have hlt : c < env.length := by omega
                    rcases hc_in with rfl | rfl
                    · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbc] at hua; cases hua
                    · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hbc] at hub; cases hub
                refine finish_add ⟨GateOp.and, [w1, w2]⟩ hno_c ⟨Or.inl rfl, le_refl 2⟩ ?_ ?_ ?_
                · intro i hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with h | h
                  · rw [h]; exact lookup_bd a w1 hua
                  · rw [h]; exact lookup_bd b w2 hub
                · exact ⟨fun h => GateOp.noConfusion h, fun _ => ⟨rfl, by simp [heq]⟩⟩
                · intro y
                  rw [hop, hins]
                  simp only [eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl] at ha hb
                  rw [ha, hb]
            · cases b2
              · exact finish_no_add (Sum.inr false) (fun _ => ⟨false, rfl⟩) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_and]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.and_false])
              · refine finish_no_add (Sum.inl w1) ?_
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                    rw [← ha, ← hb, Bool.and_true])
                intro hc; exfalso
                rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩ | ⟨ho, _⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hins] at hc_in
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                  have hlt : c < env.length := by omega
                  rcases hc_in with rfl | rfl
                  · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                  · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hcf] at hub; cases hub
                · rw [hop] at ho; exact GateOp.noConfusion ho
          · cases b1
            · exact finish_no_add (Sum.inr false) (fun _ => ⟨false, rfl⟩) (fun _ h => by cases h) (fun y => by
                rw [hop, hins, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha ⊢
                rw [← ha, Bool.false_and])
            · refine finish_no_add (lookup b) ?_ (lookup_bd b) (fun y => by
                rw [hop, hins, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.true_and]
                exact lookup_ev b y)
              intro hc
              rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩ | ⟨ho, _⟩
              · rw [hop] at hn; exact GateOp.noConfusion hn
              · rw [hins] at hc_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                have hlt : c < env.length := by omega
                rcases hc_in with rfl | rfl
                · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                · refine ⟨false, ?_⟩; dsimp [lookup]; simp only [hlt, ↓reduceIte, hcf]
              · rw [hop] at ho; exact GateOp.noConfusion ho
      · rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr false) (fun _ => ⟨false, rfl⟩) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_or]; rfl)
        · refine finish_no_add (lookup a) ?_ (lookup_bd a) (fun y => by
            rw [hop, hins, eval_or]
            simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact lookup_ev a y)
          intro hc; exfalso
          rcases hc with ⟨hn, _⟩ | ⟨ha, _⟩ | ⟨_, x, z, hxz, _⟩
          · rw [hop] at hn; exact GateOp.noConfusion hn
          · rw [hop] at ha; exact GateOp.noConfusion ha
          · rw [hins] at hxz; cases hxz
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                refine finish_no_add (Sum.inl w1) ?_
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl] at ha hb ⊢
                    rw [← ha, ← hb, Bool.or_self])
                intro hc; exfalso
                rcases hc with ⟨hn, _⟩ | ⟨ha, _⟩ | ⟨_, x, z, hxz, hxlt, _, ⟨bx, hbx⟩, _⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hop] at ha; exact GateOp.noConfusion ha
                · rw [hins] at hxz; injection hxz with hxa _
                  subst hxa
                  have hlt : a < env.length := by omega
                  dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbx] at hua; cases hua
              · have hno_c : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
                    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc)) := by
                  intro hc
                  rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, bc, hbc⟩
                  · rw [hop] at hn; exact GateOp.noConfusion hn
                  · rw [hins] at hc_in
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                    have hlt : c < env.length := by omega
                    rcases hc_in with rfl | rfl
                    · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbc] at hua; cases hua
                    · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hbc] at hub; cases hub
                refine finish_add ⟨GateOp.or, [w1, w2]⟩ hno_c ⟨Or.inr (Or.inl rfl), le_refl 2⟩ ?_ ?_ ?_
                · intro i hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with h | h
                  · rw [h]; exact lookup_bd a w1 hua
                  · rw [h]; exact lookup_bd b w2 hub
                · exact ⟨fun h => GateOp.noConfusion h, fun _ => ⟨rfl, by simp [heq]⟩⟩
                · intro y
                  rw [hop, hins]
                  simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl] at ha hb
                  rw [ha, hb]
            · cases b2
              · refine finish_no_add (Sum.inl w1) ?_
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                    rw [← ha, ← hb, Bool.or_false])
                intro hc; exfalso
                rcases hc with ⟨hn, _⟩ | ⟨ha, _⟩ | ⟨_, x, z, hxz, hxlt, _, ⟨bx, hbx⟩, _⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hop] at ha; exact GateOp.noConfusion ha
                · rw [hins] at hxz; injection hxz with hxa _
                  subst hxa
                  have hlt : a < env.length := by omega
                  dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbx] at hua; cases hua
              · exact finish_no_add (Sum.inr true) (fun _ => ⟨true, rfl⟩) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.or_true])
          · cases b1
            · refine finish_no_add (lookup b) ?_ (lookup_bd b) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.false_or]
                exact lookup_ev b y)
              intro hc
              rcases hc with ⟨hn, _⟩ | ⟨ha, _⟩ | ⟨_, x, z, hxz, _, hzlt, _, ⟨bz, hbz⟩⟩
              · rw [hop] at hn; exact GateOp.noConfusion hn
              · rw [hop] at ha; exact GateOp.noConfusion ha
              · rw [hins] at hxz; injection hxz with _ hzb
                injection hzb with hzb'
                subst hzb'
                refine ⟨bz, ?_⟩; dsimp [lookup]
                have hlt : b < env.length := by omega
                simp only [hlt, ↓reduceIte, hbz]
            · exact finish_no_add (Sum.inr true) (fun _ => ⟨true, rfl⟩) (fun _ h => by cases h) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha ⊢
                rw [← ha, Bool.true_or])
      · rcases hins : g.inputs with _ | ⟨a, rest⟩
        · exact finish_no_add (Sum.inr true) (fun _ => ⟨true, rfl⟩) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_not]; rfl)
        · rcases hua : lookup a with w1 | b1
          · have hno_c : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
                ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc)) := by
              intro hc
              rcases hc with ⟨_, c, hc_hd, hc_lt, bc, hbc⟩ | ⟨hao, _⟩
              · rw [hins] at hc_hd
                simp only [List.head?_cons, Option.some.injEq] at hc_hd
                rw [hc_hd] at hua
                have hlt : c < env.length := by omega
                dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbc] at hua; cases hua
              · rcases hao with h1 | h1 <;> (rw [hop] at h1; exact GateOp.noConfusion h1)
            refine finish_add ⟨GateOp.not, [w1]⟩ hno_c ⟨Or.inr (Or.inr rfl), by simp⟩ ?_ ?_ ?_
            · intro i hi; rw [List.mem_singleton.mp hi]; exact lookup_bd a w1 hua
            · exact ⟨fun _ => rfl, fun h => False.elim (h rfl)⟩
            · intro y
              rw [hop, hins]
              simp only [eval_not, List.map_cons, List.headD_cons]
              have ha := lookup_ev a y; rw [hua] at ha
              dsimp only [Sum.elim_inl] at ha
              rw [ha]
          · exact finish_no_add (Sum.inr (!b1)) (fun _ => ⟨!b1, rfl⟩) (fun _ h => by cases h) (fun y => by
              rw [hop, hins, eval_not]
              simp only [List.map_cons, List.headD_cons]
              have ha := lookup_ev a y; rw [hua] at ha
              dsimp only [Sum.elim_inr, id_eq] at ha ⊢
              rw [← ha])
  -- Helper: Petersen automorphisms and vertex-4 / vertex-0 deletions
  let aut : Fin 9 → Fin 9 := ![1, 2, 3, 8, 6, 0, 7, 4, 5]
  have aut_inv : ∀ y : Fin 9 → Bool, F9 (y ∘ aut) = F9 y := by
    intro y; dsimp [F9, aut, Function.comp_def]; ac_rfl
  have aut_pow_inv : ∀ (k : ℕ) (y : Fin 9 → Bool), F9 (y ∘ aut^[k]) = F9 y := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y; rw [Function.iterate_succ]
      exact (aut_inv (y ∘ aut^[k])).trans (ih y)
  let ext4 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y =>
    ![y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7]
  have hF9_ext4 : ∀ y : Fin 8 → Bool, F9 (ext4 y) = F8d4 y := by
    intro y
    have h8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
        ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && false) || (false && a0) ||
         (a0 && a4) || (a1 && a5) || (a2 && a6) || (a3 && a7) ||
         (a4 && a6) || (a5 && a7) || (a7 && a4)) =
        ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a0 && a4) || (a1 && a5) ||
         (a2 && a6) || (a3 && a7) || (a4 && a6) || (a5 && a7) || (a7 && a4)) := by decide
    exact h8 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  let ext0 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y =>
    ![false, y 0, y 1, y 2, y 6, y 7, y 4, y 5, y 3]
  have hF9_ext0 : ∀ y : Fin 8 → Bool, F9 (ext0 y) = F8d0 y := by
    intro y
    have h8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
        ((false && a0) || (a0 && a1) || (a1 && a2) || (a2 && a6) || (a6 && false) ||
         (false && a7) || (a0 && a4) || (a1 && a5) || (a2 && a3) ||
         (a7 && a5) || (a4 && a3) || (a3 && a7)) =
        ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
         (a1 && a5) || (a2 && a6) || (a3 && a7) || (a5 && a7)) := by decide
    exact h8 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  let init_d4_base : List (ℕ ⊕ Bool) :=
    [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr false,
     Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7]
  let init_d0_base : List (ℕ ⊕ Bool) :=
    [Sum.inr false, Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 6,
     Sum.inl 7, Sum.inl 4, Sum.inl 5, Sum.inl 3]
  -- Step 0: Prove ¬ HasCircuitSize 9 F9 13 directly from hDel4 (L_meta_1007)
  have no_F9_13 : ∀ (gs : List Gate) (out : ℕ),
      gs.length ≤ 13 →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ gs, (g.op = GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      (∀ y : Fin 9 → Bool, (gs.foldl stepW (List.ofFn y)).getD out false = F9 y) → False := by
    intro gs out hglen hgfan hgclean hgev
    have hout_lt : out < 9 + gs.length := by
      by_contra hge
      have h1 := hgev (fun _ => true)
      rw [getD_ge _ false out (by rw [foldl_len]; simp; omega)] at h1
      exact Bool.noConfusion h1
    have hout_ne4 : out ≠ 4 := by
      intro heq
      have h := hgev (fun k => decide (k = 4))
      rw [heq, foldl_getD_lt gs _ 4 (by simp)] at h
      have hl : (List.ofFn (fun k : Fin 9 => decide (k = 4))).getD 4 false = true := by decide
      have hr : F9 (fun k => decide (k = 4)) = false := by decide
      rw [hl, hr] at h; exact Bool.noConfusion h
    have hex4 : ∃ j < gs.length, ∃ g, gs[j]? = some g ∧ 4 ∈ g.inputs := by
      by_contra hnone
      push Not at hnone
      let u1 : Fin 9 → Bool := fun k => decide (k = 3)
      let u2 : Fin 9 → Bool := fun k => decide (k = 3 ∨ k = 4)
      have heq := wire_agree gs (List.ofFn u1) (List.ofFn u2) (fun i => i = 4) (by simp)
        (by
          intro i hi hne
          have hchk : ∀ j : Fin 9, j.val ≠ 4 → (List.ofFn u1).getD j.val false = (List.ofFn u2).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne)
        (by intro j hj g hgj _ i hi he; subst he; exact hnone j hj g hgj hi)
        out (by rw [foldl_len]; simp; omega) hout_ne4
      have h1 := hgev u1; have h2 := hgev u2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
    obtain ⟨j4, hj4_lt, g4, hj4_some, h4_in⟩ := hex4
    obtain ⟨gs4, env4, drop4, henv4_len, hinit4_eq, _, hsz4, hdrop4_c, _, hgs4_fan, _, _, _, hgs4_ev⟩ :=
      simplify 8 9 8 (fun y => List.ofFn (ext4 y)) (fun y => List.ofFn y) init_d4_base gs
        (by intro y; simp) (by intro y; simp) rfl hgfan
        (by
          intro i hi y
          have hchk : ∀ j : Fin 9, Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d4_base.getD j.val (Sum.inr false)) = (List.ofFn (ext4 y)).getD j.val false := by
            intro j; fin_cases j <;> simp [init_d4_base, ext4]
          exact hchk ⟨i, hi⟩)
        (by
          intro i hi w hw
          have hchk : ∀ j : Fin 9, ∀ u, init_d4_base.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
            intro j u hu; fin_cases j <;> simp [init_d4_base] at hu <;> omega
          exact hchk ⟨i, hi⟩ w hw)
    have h4c : env4.getD 4 (Sum.inr false) = Sum.inr false := hinit4_eq 4 (by omega)
    have hj4_drop : j4 ∈ drop4 := by
      have hcl := hgclean g4 (List.mem_of_getElem? hj4_some)
      apply hdrop4_c j4 hj4_lt g4 hj4_some
      rcases (hgfan g4 (List.mem_of_getElem? hj4_some)).1 with hop | hop | hop
      · exact Or.inr ⟨Or.inl hop, 4, h4_in, by omega, false, h4c⟩
      · exact Or.inr ⟨Or.inr hop, 4, h4_in, by omega, false, h4c⟩
      · refine Or.inl ⟨hop, 4, ?_, by omega, false, h4c⟩
        have hl1 := hcl.1 hop
        rcases hins : g4.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 h4_in; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at h4_in; subst h4_in; rfl
    have hcard_pos : 1 ≤ drop4.card := Finset.card_pos.mpr ⟨j4, hj4_drop⟩
    rcases hout4 : env4.getD out (Sum.inr false) with out4 | b4
    · apply hDel4
      refine ⟨⟨gs4, out4⟩, ?_, by change gs4.length ≤ 12; omega, ?_⟩
      · intro g hg
        have h := hgs4_fan g hg
        exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
      · intro y
        have h := hgs4_ev out (by omega) y
        rw [hout4] at h; dsimp only [Sum.elim_inl] at h
        change (gs4.foldl stepW (List.ofFn y)).getD out4 false = F8d4 y
        rw [h, hgev (ext4 y), hF9_ext4]
    · have h0 := hgs4_ev out (by omega) (fun _ => false)
      have h1 := hgs4_ev out (by omega) (fun _ => true)
      rw [hout4] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
      rw [hgev] at h0; rw [hgev] at h1
      have hne : F9 (ext4 (fun _ => false)) ≠ F9 (ext4 (fun _ => true)) := by decide
      exact hne (h0.symm.trans h1)
  -- Basic facts about D
  have hDlen : D.gates.length = 14 := hDsz
  have hDfan' : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hDfan g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  have hDrb' : ∀ j < D.gates.length, ∀ g, D.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j := by
    intro j hj g hgj i hi
    have hrb := hDrb j hj i
    have hgd : gateAt D j = g := by
      change D.gates.getD j ⟨GateOp.or, []⟩ = g
      simp only [List.getD_eq_getElem?_getD, hgj, Option.getD_some]
    rw [hgd] at hrb; exact hrb hi
  have hout_lt : D.output < 10 + D.gates.length := by
    by_contra hge
    have h := hDev (fun _ => true)
    change (D.gates.foldl stepW (List.ofFn (fun _ : Fin 9 => true) ++ [true && true])).getD D.output false = F9 (fun _ => true) at h
    rw [getD_ge _ false D.output (by rw [foldl_len]; simp; omega)] at h
    exact Bool.noConfusion h
  have hout_ne0 : D.output ≠ 0 := by
    intro heq
    have h := hDev (fun k => decide (k = 0))
    change (D.gates.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 0)) ++ [true && false])).getD D.output false = F9 (fun k => decide (k = 0)) at h
    rw [heq, foldl_getD_lt D.gates _ 0 (by simp)] at h
    have hl : (List.ofFn (fun k : Fin 9 => decide (k = 0)) ++ [true && false]).getD 0 false = true := by decide
    have hr : F9 (fun k => decide (k = 0)) = false := by decide
    rw [hl, hr] at h; exact Bool.noConfusion h
  have hout_ne2 : D.output ≠ 2 := by
    intro heq
    have h := hDev (fun k => decide (k = 2))
    change (D.gates.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 2)) ++ [false && true])).getD D.output false = F9 (fun k => decide (k = 2)) at h
    rw [heq, foldl_getD_lt D.gates _ 2 (by simp)] at h
    have hl : (List.ofFn (fun k : Fin 9 => decide (k = 2)) ++ [false && true]).getD 2 false = true := by decide
    have hr : F9 (fun k => decide (k = 2)) = false := by decide
    rw [hl, hr] at h; exact Bool.noConfusion h
  have hout_ne9 : D.output ≠ 9 := by
    intro heq
    have h := hDev (fun k => decide (k = 0 ∨ k = 2))
    change (D.gates.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 0 ∨ k = 2)) ++ [true && true])).getD D.output false = F9 (fun k => decide (k = 0 ∨ k = 2)) at h
    rw [heq, foldl_getD_lt D.gates _ 9 (by simp)] at h
    have hl : (List.ofFn (fun k : Fin 9 => decide (k = 0 ∨ k = 2)) ++ [true && true]).getD 9 false = true := by decide
    have hr : F9 (fun k => decide (k = 0 ∨ k = 2)) = false := by decide
    rw [hl, hr] at h; exact Bool.noConfusion h
  -- Helper: unique reader extraction from filter = [g]
  have unique_idx : ∀ (P : Gate → Bool) (g : Gate), D.gates.filter P = [g] →
      ∃ p < D.gates.length, D.gates[p]? = some g ∧ P g = true ∧
        ∀ j < D.gates.length, ∀ g', D.gates[j]? = some g' → P g' = true → j = p := by
    intro P g hfl
    have hmem : g ∈ D.gates.filter P := by rw [hfl]; simp
    have hmem' := List.mem_filter.mp hmem
    obtain ⟨p, hp_lt, hp_eq⟩ := List.getElem_of_mem hmem'.1
    have hp_some : D.gates[p]? = some g := by rw [List.getElem?_eq_getElem hp_lt, hp_eq]
    refine ⟨p, hp_lt, hp_some, hmem'.2, ?_⟩
    intro j hj g' hgj hpg'
    by_contra hne
    have hcnt : ∀ (l : List Gate) (i1 i2 : ℕ) (a1 a2 : Gate),
        i1 < l.length → i2 < l.length → i1 ≠ i2 →
        l[i1]? = some a1 → l[i2]? = some a2 → P a1 = true → P a2 = true →
        2 ≤ (l.filter P).length := by
      intro l
      induction l with
      | nil => intro _ _ _ _ h1; simp at h1
      | cons x xs ih =>
        intro i1 i2 a1 a2 h1 h2 hne12 ha1 ha2 hp1 hp2
        rcases i1 with _ | i1 <;> rcases i2 with _ | i2
        · exact False.elim (hne12 rfl)
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at ha1; subst ha1
          simp only [List.getElem?_cons_succ] at ha2
          rw [List.filter_cons, hp1]; simp only [↓reduceIte, List.length_cons]
          have hmem2 : a2 ∈ xs.filter P := List.mem_filter.mpr ⟨List.mem_of_getElem? ha2, hp2⟩
          have := List.length_pos_of_mem hmem2; omega
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at ha2; subst ha2
          simp only [List.getElem?_cons_succ] at ha1
          rw [List.filter_cons, hp2]; simp only [↓reduceIte, List.length_cons]
          have hmem1 : a1 ∈ xs.filter P := List.mem_filter.mpr ⟨List.mem_of_getElem? ha1, hp1⟩
          have := List.length_pos_of_mem hmem1; omega
        · simp only [List.getElem?_cons_succ] at ha1 ha2
          simp only [List.length_cons] at h1 h2
          have hsub := ih i1 i2 a1 a2 (by omega) (by omega) (by omega) ha1 ha2 hp1 hp2
          rw [List.filter_cons]
          cases P x <;> simp <;> omega
    have h2 := hcnt D.gates j p g' g hj hp_lt hne hgj hp_some hpg' hmem'.2
    rw [hfl] at h2; simp at h2
  -- Extract unique readers h (of 9), g0 (of 0), g2 (of 2)
  obtain ⟨h9, hh9_or, hh9_fl⟩ := h9ex
  obtain ⟨ph, hph_lt, hph_some, hh9_9b, hph_uniq⟩ := unique_idx (fun g => decide (9 ∈ g.inputs)) h9 hh9_fl
  have hh9_9 : 9 ∈ h9.inputs := of_decide_eq_true hh9_9b
  have hfl0_ex : ∃ g0 : Gate, D.gates.filter (fun g => decide (0 ∈ g.inputs)) = [g0] := by
    have hlen := h02len 0 (by simp)
    rcases hfl : D.gates.filter (fun g => decide (0 ∈ g.inputs)) with _ | ⟨g0, rest⟩
    · rw [hfl] at hlen; simp at hlen
    · rw [hfl] at hlen; simp only [List.length_cons] at hlen
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil; exact ⟨g0, hfl⟩
  have hfl2_ex : ∃ g2 : Gate, D.gates.filter (fun g => decide (2 ∈ g.inputs)) = [g2] := by
    have hlen := h02len 2 (by simp)
    rcases hfl : D.gates.filter (fun g => decide (2 ∈ g.inputs)) with _ | ⟨g2, rest⟩
    · rw [hfl] at hlen; simp at hlen
    · rw [hfl] at hlen; simp only [List.length_cons] at hlen
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil; exact ⟨g2, hfl⟩
  obtain ⟨g0, hg0_fl⟩ := hfl0_ex
  obtain ⟨g2, hg2_fl⟩ := hfl2_ex
  obtain ⟨p0, hp0_lt, hp0_some, hg0_0b, hp0_uniq⟩ := unique_idx (fun g => decide (0 ∈ g.inputs)) g0 hg0_fl
  obtain ⟨p2, hp2_lt, hp2_some, hg2_2b, hp2_uniq⟩ := unique_idx (fun g => decide (2 ∈ g.inputs)) g2 hg2_fl
  have hg0_0 : 0 ∈ g0.inputs := of_decide_eq_true hg0_0b
  have hg2_2 : 2 ∈ g2.inputs := of_decide_eq_true hg2_2b
  -- Step 1: Replacing wire 9 by false drops h9, yielding a ≤ 13-gate circuit for F9 -> contradicts no_F9_13!
  have no_drop_wire9_14 : (∀ y : Fin 9 → Bool,
      (D.gates.foldl stepW (List.ofFn y ++ [false])).getD D.output false = F9 y) → False := by
    intro hf9
    let init_f9 : List (ℕ ⊕ Bool) := List.ofFn (fun i : Fin 9 => Sum.inl i.val) ++ [Sum.inr false]
    obtain ⟨gs_f9, env_f9, drop_f9, henv_f9_len, hinit_f9_eq, _, hsz_f9, hdrop_f9_c, _,
      hgs_f9_fan, _, hgs_f9_clean, _, hgs_f9_ev⟩ :=
      simplify 9 10 9 (fun y => List.ofFn y ++ [false]) (fun y => List.ofFn y) init_f9 D.gates
        (by intro y; simp) (by intro y; simp) (by simp [init_f9]) hDfan'
        (by
          intro i hi y
          by_cases hlt : i < 9
          · have hi1 : init_f9.getD i (Sum.inr false) = Sum.inl i := by
              dsimp only [init_f9]
              rw [getD_snoc_lt _ _ _ i (by simp; omega)]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
            rw [hi1]; dsimp only [Sum.elim_inl]
            rw [getD_snoc_lt _ _ _ i (by simp; omega)]
          · have hieq : i = 9 := by omega
            subst hieq
            have hi1 : init_f9.getD 9 (Sum.inr false) = Sum.inr false := by
              dsimp only [init_f9]
              have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => (Sum.inl i.val : ℕ ⊕ Bool))) (Sum.inr false) (Sum.inr false)
              simpa using this
            rw [hi1]; dsimp only [Sum.elim_inr, id_eq]
            have hsn := getD_snoc_eq (List.ofFn y) false false
            simpa using hsn.symm)
        (by
          intro i hi w hw
          by_cases hlt : i < 9
          · dsimp only [init_f9] at hw
            rw [getD_snoc_lt _ _ _ i (by simp; omega)] at hw
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
              Option.getD_some, Sum.inl.injEq] at hw
            omega
          · have hieq : i = 9 := by omega
            subst hieq; dsimp only [init_f9] at hw
            have hsn := getD_snoc_eq (List.ofFn (fun i : Fin 9 => (Sum.inl i.val : ℕ ⊕ Bool))) (Sum.inr false) (Sum.inr false)
            simp only [List.length_ofFn] at hsn; rw [hsn] at hw; cases hw)
    have h9c : env_f9.getD 9 (Sum.inr false) = Sum.inr false := by
      rw [hinit_f9_eq 9 (by omega)]; dsimp only [init_f9]
      have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => (Sum.inl i.val : ℕ ⊕ Bool))) (Sum.inr false) (Sum.inr false)
      simpa using this
    have hph_drop : ph ∈ drop_f9 := by
      apply hdrop_f9_c ph hph_lt h9 hph_some
      exact Or.inr ⟨Or.inr hh9_or, 9, hh9_9, by omega, false, h9c⟩
    have hcard_pos : 1 ≤ drop_f9.card := Finset.card_pos.mpr ⟨ph, hph_drop⟩
    rcases hout_f9 : env_f9.getD D.output (Sum.inr false) with out_f9 | b_f9
    · apply no_F9_13 gs_f9 out_f9 (by omega) hgs_f9_fan hgs_f9_clean
      intro y
      have h := hgs_f9_ev D.output (by omega) y
      rw [hout_f9] at h; dsimp only [Sum.elim_inl] at h
      exact h.trans (hf9 y)
    · have h0 := hgs_f9_ev D.output (by omega) (fun _ => false)
      have h1 := hgs_f9_ev D.output (by omega) (fun _ => true)
      rw [hout_f9] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
      rw [hf9] at h0 h1
      have hne : F9 (fun _ => false) ≠ F9 (fun _ => true) := by decide
      exact hne (h0.symm.trans h1)
  -- Step 2: Prove p0 ≠ ph, p2 ≠ ph, p0 ≠ p2
  have hp0_ne_ph : p0 ≠ ph := by
    intro heq
    have h09 : 0 ∈ h9.inputs := by
      rw [heq] at hp0_some; rw [hph_some] at hp0_some
      injection hp0_some with hge; rw [hge]; exact hg0_0
    have hcl := hDclean h9 (List.mem_of_getElem? hph_some)
    have hlen2 := (hcl.2 (by rw [hh9_or]; intro h; exact GateOp.noConfusion h)).1
    rcases list_le2 h9.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
    · rw [hins] at hlen2; simp at hlen2
    · rw [hins] at hlen2; simp at hlen2
    · rw [hins] at h09 hh9_9
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h09 hh9_9
      apply no_drop_wire9_14
      intro y
      have hind : ∀ (n : ℕ) (hn : n ≤ D.gates.length), ∀ k < 10 + n, k ≠ 9 →
          ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).getD k false =
          ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD k false := by
        intro n
        induction n with
        | zero =>
          intro _ k hk hne9
          simp only [List.take_zero, List.foldl_nil]
          have hlt9 : k < 9 := by omega
          rw [getD_snoc_lt _ _ _ k (by simp; omega), getD_snoc_lt _ _ _ k (by simp; omega)]
        | succ n ih =>
          intro hn k hk hne9
          have htake : D.gates.take (n + 1) = D.gates.take n ++ [D.gates[n]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
          rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hl1 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).length = 10 + n := by
            rw [foldl_len]; simp [List.length_take_of_le (by omega : n ≤ D.gates.length)]
          have hl2 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).length = 10 + n := by
            rw [foldl_len]; simp [List.length_take_of_le (by omega : n ≤ D.gates.length)]
          by_cases hlt : k < 10 + n
          · change (((D.gates.take n).foldl stepW _) ++ [_]).getD k false =
              (((D.gates.take n).foldl stepW _) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega), getD_snoc_lt _ _ _ k (by omega)]
            exact ih (by omega) k hlt hne9
          · have hkeq : k = 10 + n := by omega
            subst hkeq
            change (((D.gates.take n).foldl stepW _) ++ [_]).getD (10 + n) false =
              (((D.gates.take n).foldl stepW _) ++ [_]).getD (10 + n) false
            rw [← hl1, getD_snoc_eq, hl1, ← hl2, getD_snoc_eq]
            by_cases hnp : n = ph
            · have hgn : D.gates[n]'(by omega) = h9 := by
                cases hnp
                exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hph_some)
              rw [hgn, hh9_or, hins, eval_or]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              have hw0_1 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).getD 0 false = y 0 := by
                rw [foldl_getD_lt _ _ 0 (by simp)]; rw [getD_snoc_lt _ _ _ 0 (by simp)]; simp [List.getD_eq_getElem?_getD]
              have hw0_2 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 0 false = y 0 := by
                rw [foldl_getD_lt _ _ 0 (by simp)]; rw [getD_snoc_lt _ _ _ 0 (by simp)]; simp [List.getD_eq_getElem?_getD]
              have hw9_1 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).getD 9 false = false := by
                rw [foldl_getD_lt _ _ 9 (by simp)]
                have := getD_snoc_eq (List.ofFn y) false false; simpa using this
              have hw9_2 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 9 false = (y 0 && y 2) := by
                rw [foldl_getD_lt _ _ 9 (by simp)]
                have := getD_snoc_eq (List.ofFn y) (y 0 && y 2) false; simpa using this
              rcases h09 with rfl | rfl <;> rcases hh9_9 with h1 | h1
              · omega
              · subst h1; rw [hw0_1, hw0_2, hw9_1, hw9_2]; cases y 0 <;> cases y 2 <;> rfl
              · subst h1; rw [hw0_1, hw0_2, hw9_1, hw9_2]; cases y 0 <;> cases y 2 <;> rfl
              · omega
            · congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < 10 + n :=
                hDrb' n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) u hu
              have hu_ne9 : u ≠ 9 := by
                intro hu9; subst hu9
                exact hnp (hph_uniq n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) (decide_eq_true hu))
              exact ih (by omega) u hu_lt hu_ne9
      have hall := hind D.gates.length (le_refl _) D.output hout_lt hout_ne9
      rw [List.take_length] at hall
      exact hall.trans (hDev y)
  have hp2_ne_ph : p2 ≠ ph := by
    intro heq
    have h29 : 2 ∈ h9.inputs := by
      rw [heq] at hp2_some; rw [hph_some] at hp2_some
      injection hp2_some with hge; rw [hge]; exact hg2_2
    have hcl := hDclean h9 (List.mem_of_getElem? hph_some)
    have hlen2 := (hcl.2 (by rw [hh9_or]; intro h; exact GateOp.noConfusion h)).1
    rcases list_le2 h9.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
    · rw [hins] at hlen2; simp at hlen2
    · rw [hins] at hlen2; simp at hlen2
    · rw [hins] at h29 hh9_9
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h29 hh9_9
      apply no_drop_wire9_14
      intro y
      have hind : ∀ (n : ℕ) (hn : n ≤ D.gates.length), ∀ k < 10 + n, k ≠ 9 →
          ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).getD k false =
          ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD k false := by
        intro n
        induction n with
        | zero =>
          intro _ k hk hne9
          simp only [List.take_zero, List.foldl_nil]
          have hlt9 : k < 9 := by omega
          rw [getD_snoc_lt _ _ _ k (by simp; omega), getD_snoc_lt _ _ _ k (by simp; omega)]
        | succ n ih =>
          intro hn k hk hne9
          have htake : D.gates.take (n + 1) = D.gates.take n ++ [D.gates[n]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
          rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hl1 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).length = 10 + n := by
            rw [foldl_len]; simp [List.length_take_of_le (by omega : n ≤ D.gates.length)]
          have hl2 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).length = 10 + n := by
            rw [foldl_len]; simp [List.length_take_of_le (by omega : n ≤ D.gates.length)]
          by_cases hlt : k < 10 + n
          · change (((D.gates.take n).foldl stepW _) ++ [_]).getD k false =
              (((D.gates.take n).foldl stepW _) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega), getD_snoc_lt _ _ _ k (by omega)]
            exact ih (by omega) k hlt hne9
          · have hkeq : k = 10 + n := by omega
            subst hkeq
            change (((D.gates.take n).foldl stepW _) ++ [_]).getD (10 + n) false =
              (((D.gates.take n).foldl stepW _) ++ [_]).getD (10 + n) false
            rw [← hl1, getD_snoc_eq, hl1, ← hl2, getD_snoc_eq]
            by_cases hnp : n = ph
            · have hgn : D.gates[n]'(by omega) = h9 := by
                cases hnp
                exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hph_some)
              rw [hgn, hh9_or, hins, eval_or]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              have hw2_1 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).getD 2 false = y 2 := by
                rw [foldl_getD_lt _ _ 2 (by simp)]; rw [getD_snoc_lt _ _ _ 2 (by simp)]; simp [List.getD_eq_getElem?_getD]
              have hw2_2 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 2 false = y 2 := by
                rw [foldl_getD_lt _ _ 2 (by simp)]; rw [getD_snoc_lt _ _ _ 2 (by simp)]; simp [List.getD_eq_getElem?_getD]
              have hw9_1 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [false])).getD 9 false = false := by
                rw [foldl_getD_lt _ _ 9 (by simp)]
                have := getD_snoc_eq (List.ofFn y) false false; simpa using this
              have hw9_2 : ((D.gates.take n).foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 9 false = (y 0 && y 2) := by
                rw [foldl_getD_lt _ _ 9 (by simp)]
                have := getD_snoc_eq (List.ofFn y) (y 0 && y 2) false; simpa using this
              rcases h29 with rfl | rfl <;> rcases hh9_9 with h1 | h1
              · omega
              · subst h1; rw [hw2_1, hw2_2, hw9_1, hw9_2]; cases y 0 <;> cases y 2 <;> rfl
              · subst h1; rw [hw2_1, hw2_2, hw9_1, hw9_2]; cases y 0 <;> cases y 2 <;> rfl
              · omega
            · congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < 10 + n :=
                hDrb' n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) u hu
              have hu_ne9 : u ≠ 9 := by
                intro hu9; subst hu9
                exact hnp (hph_uniq n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) (decide_eq_true hu))
              exact ih (by omega) u hu_lt hu_ne9
      have hall := hind D.gates.length (le_refl _) D.output hout_lt hout_ne9
      rw [List.take_length] at hall
      exact hall.trans (hDev y)
  have hp0_ne_p2 : p0 ≠ p2 := by
    intro heq
    have h02 : 2 ∈ g0.inputs := by
      rw [heq] at hp0_some; rw [hp2_some] at hp0_some
      injection hp0_some with hge; rw [← hge]; exact hg2_2
    have hcl := hDclean g0 (List.mem_of_getElem? hp0_some)
    have hnot_not : g0.op ≠ GateOp.not := by
      intro hnot
      have hlen1 := hcl.1 hnot
      rcases hins : g0.inputs with _ | ⟨a, rest⟩
      · rw [hins] at hlen1; simp at hlen1
      · rw [hins] at hlen1 hg0_0 h02; simp only [List.length_cons] at hlen1
        have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil; simp only [List.mem_singleton] at hg0_0 h02; omega
    have hlen2 := (hcl.2 hnot_not).1
    rcases list_le2 g0.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
    · rw [hins] at hlen2; simp at hlen2
    · rw [hins] at hlen2; simp at hlen2
    · rw [hins] at hg0_0 h02
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg0_0 h02
      let u1 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 4)
      let u2 : Fin 9 → Bool := fun k => decide (k = 2 ∨ k = 4)
      have hind : ∀ (n : ℕ) (hn : n ≤ D.gates.length), ∀ k < 10 + n, k ≠ 0 → k ≠ 2 →
          ((D.gates.take n).foldl stepW (List.ofFn u1 ++ [u1 0 && u1 2])).getD k false =
          ((D.gates.take n).foldl stepW (List.ofFn u2 ++ [u2 0 && u2 2])).getD k false := by
        intro n
        induction n with
        | zero =>
          intro _ k hk hne0 hne2
          simp only [List.take_zero, List.foldl_nil]
          have hchk : ∀ j : Fin 10, j.val ≠ 0 → j.val ≠ 2 →
              (List.ofFn u1 ++ [u1 0 && u1 2]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 && u2 2]).getD j.val false := by decide
          exact hchk ⟨k, hk⟩ hne0 hne2
        | succ n ih =>
          intro hn k hk hne0 hne2
          have htake : D.gates.take (n + 1) = D.gates.take n ++ [D.gates[n]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
          rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hl1 : ((D.gates.take n).foldl stepW (List.ofFn u1 ++ [u1 0 && u1 2])).length = 10 + n := by
            rw [foldl_len]; simp [List.length_take_of_le (by omega : n ≤ D.gates.length)]
          have hl2 : ((D.gates.take n).foldl stepW (List.ofFn u2 ++ [u2 0 && u2 2])).length = 10 + n := by
            rw [foldl_len]; simp [List.length_take_of_le (by omega : n ≤ D.gates.length)]
          by_cases hlt : k < 10 + n
          · change (((D.gates.take n).foldl stepW _) ++ [_]).getD k false =
              (((D.gates.take n).foldl stepW _) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega), getD_snoc_lt _ _ _ k (by omega)]
            exact ih (by omega) k hlt hne0 hne2
          · have hkeq : k = 10 + n := by omega
            subst hkeq
            change (((D.gates.take n).foldl stepW _) ++ [_]).getD (10 + n) false =
              (((D.gates.take n).foldl stepW _) ++ [_]).getD (10 + n) false
            rw [← hl1, getD_snoc_eq, hl1, ← hl2, getD_snoc_eq]
            by_cases hnp : n = p0
            · have hgn : D.gates[n]'(by omega) = g0 := by
                cases hnp
                exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hp0_some)
              rw [hgn, hins]
              have hw0_1 : ((D.gates.take n).foldl stepW (List.ofFn u1 ++ [u1 0 && u1 2])).getD 0 false = true := by
                rw [foldl_getD_lt _ _ 0 (by simp)]; decide
              have hw2_1 : ((D.gates.take n).foldl stepW (List.ofFn u1 ++ [u1 0 && u1 2])).getD 2 false = false := by
                rw [foldl_getD_lt _ _ 2 (by simp)]; decide
              have hw0_2 : ((D.gates.take n).foldl stepW (List.ofFn u2 ++ [u2 0 && u2 2])).getD 0 false = false := by
                rw [foldl_getD_lt _ _ 0 (by simp)]; decide
              have hw2_2 : ((D.gates.take n).foldl stepW (List.ofFn u2 ++ [u2 0 && u2 2])).getD 2 false = true := by
                rw [foldl_getD_lt _ _ 2 (by simp)]; decide
              rcases (hDfan' g0 (List.mem_of_getElem? hp0_some)).1 with hop | hop | hop
              · rw [hop, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rcases hg0_0 with rfl | rfl <;> rcases h02 with h1 | h1
                · omega
                · subst h1; rw [hw0_1, hw2_1, hw0_2, hw2_2]; rfl
                · subst h1; rw [hw0_1, hw2_1, hw0_2, hw2_2]; rfl
                · omega
              · rw [hop, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rcases hg0_0 with rfl | rfl <;> rcases h02 with h1 | h1
                · omega
                · subst h1; rw [hw0_1, hw2_1, hw0_2, hw2_2]; rfl
                · subst h1; rw [hw0_1, hw2_1, hw0_2, hw2_2]; rfl
                · omega
              · exact False.elim (hnot_not hop)
            · congr 1
              apply List.map_congr_left
              intro u hu
              have hu_lt : u < 10 + n :=
                hDrb' n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) u hu
              have hu_ne0 : u ≠ 0 := by
                intro hu0; subst hu0
                exact hnp (hp0_uniq n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) (decide_eq_true hu))
              have hu_ne2 : u ≠ 2 := by
                intro hu2; subst hu2
                have hn2 := hp2_uniq n (by omega) (D.gates[n]'(by omega)) (List.getElem?_eq_getElem (by omega)) (decide_eq_true hu)
                omega
              exact ih (by omega) u hu_lt hu_ne0 hu_ne2
      have hall := hind D.gates.length (le_refl _) D.output hout_lt hout_ne0 hout_ne2
      rw [List.take_length] at hall
      have h1 := hDev u1; have h2 := hDev u2
      change (D.gates.foldl stepW _).getD D.output false = F9 u1 at h1
      change (D.gates.foldl stepW _).getD D.output false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (hall.trans h2))
  -- Step 3: Prove filter(0 ∨ 2 ∨ 9).length = 3
  have hfilt029_eq3 : (D.gates.filter (fun g => decide (0 ∈ g.inputs ∨ 2 ∈ g.inputs ∨ 9 ∈ g.inputs))).length = 3 := by
    have filt_disj_sum : ∀ (gs : List Gate) (P Q : Gate → Bool),
        (∀ g ∈ gs, ¬ (P g = true ∧ Q g = true)) →
        (gs.filter P).length + (gs.filter Q).length = (gs.filter (fun g => P g || Q g)).length := by
      intro gs P Q
      induction gs with
      | nil => intro _; simp
      | cons g gs ih =>
        intro hdisj
        have hsub := ih (fun h hh => hdisj h (List.mem_cons_of_mem _ hh))
        have hg := hdisj g (List.mem_cons_self ..)
        rw [List.filter_cons, List.filter_cons, List.filter_cons]
        cases hp : P g <;> cases hq : Q g
        · simp [hsub]
        · simp; omega
        · simp; omega
        · exact False.elim (hg ⟨hp, hq⟩)
    have hdisj02 : ∀ g ∈ D.gates, ¬ (decide (0 ∈ g.inputs) = true ∧ decide (2 ∈ g.inputs) = true) := by
      intro g hg hpair
      have h0 := hpair.1
      have h2 := hpair.2
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have j0 := hp0_uniq j hj D.gates[j] (List.getElem?_eq_getElem hj) h0
      have j2 := hp2_uniq j hj D.gates[j] (List.getElem?_eq_getElem hj) h2
      omega
    have hdisj02_9 : ∀ g ∈ D.gates, ¬ ((decide (0 ∈ g.inputs) || decide (2 ∈ g.inputs)) = true ∧ decide (9 ∈ g.inputs) = true) := by
      intro g hg hpair
      have h02 := hpair.1
      have h9 := hpair.2
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have j9 := hph_uniq j hj D.gates[j] (List.getElem?_eq_getElem hj) h9
      rcases Bool.or_eq_true_iff.mp h02 with h0 | h2
      · have j0 := hp0_uniq j hj D.gates[j] (List.getElem?_eq_getElem hj) h0; omega
      · have j2 := hp2_uniq j hj D.gates[j] (List.getElem?_eq_getElem hj) h2; omega
    have hs1 := filt_disj_sum D.gates (fun g => decide (0 ∈ g.inputs)) (fun g => decide (2 ∈ g.inputs)) hdisj02
    have hs2 := filt_disj_sum D.gates (fun g => decide (0 ∈ g.inputs) || decide (2 ∈ g.inputs)) (fun g => decide (9 ∈ g.inputs)) hdisj02_9
    have heq_f : D.gates.filter (fun g => decide (0 ∈ g.inputs ∨ 2 ∈ g.inputs ∨ 9 ∈ g.inputs)) =
        D.gates.filter (fun g => (decide (0 ∈ g.inputs) || decide (2 ∈ g.inputs)) || decide (9 ∈ g.inputs)) := by
      congr 1; funext g; by_cases h0 : 0 ∈ g.inputs <;> by_cases h2 : 2 ∈ g.inputs <;> by_cases h9 : 9 ∈ g.inputs <;> simp [h0, h2, h9]
    rw [heq_f, ← hs2, ← hs1, hg0_fl, hg2_fl, hh9_fl]
    rfl
  -- Step 4: Prove g0.op = GateOp.or via y 0 = false restriction (hDel0 = L_meta_1664)
  have hg0_or : g0.op = GateOp.or := by
    let init_d0 : List (ℕ ⊕ Bool) := init_d0_base ++ [Sum.inr false]
    obtain ⟨gs_d0, env_d0, drop_d0, henv_d0_len, hinit_d0_eq, _, hsz_d0, hdrop_d0_c, hprop_d0_c,
      hgs_d0_fan, _, _, _, hgs_d0_ev⟩ :=
      simplify 8 10 8 (fun y => List.ofFn (ext0 y) ++ [ext0 y 0 && ext0 y 2]) (fun y => List.ofFn y)
        init_d0 D.gates (by intro y; simp) (by intro y; simp) rfl hDfan'
        (by
          intro i hi y
          have hchk : ∀ j : Fin 10,
              Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d0.getD j.val (Sum.inr false)) =
                (List.ofFn (ext0 y) ++ [ext0 y 0 && ext0 y 2]).getD j.val false := by
            intro j; fin_cases j <;> simp [init_d0, init_d0_base, ext0]
          exact hchk ⟨i, hi⟩)
        (by
          intro i hi w hw
          have hchk : ∀ j : Fin 10, ∀ u, init_d0.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
            intro j u hu; fin_cases j <;> simp [init_d0, init_d0_base] at hu <;> omega
          exact hchk ⟨i, hi⟩ w hw)
    have hd0_ge12 : 12 ≤ gs_d0.length := by
      by_contra hle11
      rcases hout_d0 : env_d0.getD D.output (Sum.inr false) with out_d0 | b_d0
      · apply hDel0
        refine ⟨⟨gs_d0, out_d0⟩, ?_, by change gs_d0.length ≤ 11; omega, ?_⟩
        · intro g hg
          have h := hgs_d0_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_d0_ev D.output (by omega) y
          rw [hout_d0] at h; dsimp only [Sum.elim_inl] at h
          have hd := hDev (ext0 y)
          change (D.gates.foldl stepW _).getD D.output false = F9 (ext0 y) at hd
          change (gs_d0.foldl stepW (List.ofFn y)).getD out_d0 false = F8d0 y
          rw [h, hd, hF9_ext0]
      · have h0 := hgs_d0_ev D.output (by omega) (fun _ => false)
        have h1 := hgs_d0_ev D.output (by omega) (fun _ => true)
        rw [hout_d0] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hDev (ext0 (fun _ => false))
        have hd1 := hDev (ext0 (fun _ => true))
        change (D.gates.foldl stepW _).getD D.output false = F9 (ext0 (fun _ => false)) at hd0
        change (D.gates.foldl stepW _).getD D.output false = F9 (ext0 (fun _ => true)) at hd1
        rw [hd0] at h0; rw [hd1] at h1
        have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
        exact hne (h0.symm.trans h1)
    have hdrop_le2 : drop_d0.card ≤ 2 := by omega
    have h0c : env_d0.getD 0 (Sum.inr false) = Sum.inr false := hinit_d0_eq 0 (by omega)
    have h9c : env_d0.getD 9 (Sum.inr false) = Sum.inr false := hinit_d0_eq 9 (by omega)
    have hp0_drop : p0 ∈ drop_d0 := by
      have hcl := hDclean g0 (List.mem_of_getElem? hp0_some)
      apply hdrop_d0_c p0 hp0_lt g0 hp0_some
      rcases (hDfan' g0 (List.mem_of_getElem? hp0_some)).1 with hop | hop | hop
      · exact Or.inr ⟨Or.inl hop, 0, hg0_0, by omega, false, h0c⟩
      · exact Or.inr ⟨Or.inr hop, 0, hg0_0, by omega, false, h0c⟩
      · refine Or.inl ⟨hop, 0, ?_, by omega, false, h0c⟩
        have hl1 := hcl.1 hop
        rcases hins : g0.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 hg0_0; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at hg0_0; subst hg0_0; rfl
    have hph_drop : ph ∈ drop_d0 :=
      hdrop_d0_c ph hph_lt h9 hph_some (Or.inr ⟨Or.inr hh9_or, 9, hh9_9, by omega, false, h9c⟩)
    have no_third_drop : ∀ k ∈ drop_d0, k = p0 ∨ k = ph := by
      intro k hk
      by_contra hne
      push Not at hne
      have hsub : ({p0, ph, k} : Finset ℕ) ⊆ drop_d0 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hc2 : ({ph, k} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hne.2)
      have hnm : p0 ∉ ({ph, k} : Finset ℕ) := by simp [hp0_ne_ph, Ne.symm hne.1]
      have hc3 : ({p0, ph, k} : Finset ℕ).card = 3 := by rw [Finset.card_insert_of_notMem hnm, hc2]
      have := Finset.card_le_card hsub; omega
    have drop_of_const_in : ∀ (w : ℕ) (b : Bool), env_d0.getD w (Sum.inr false) = Sum.inr b →
        ∀ j < D.gates.length, ∀ g', D.gates[j]? = some g' → w ∈ g'.inputs → j ∈ drop_d0 := by
      intro w b hwb j hj g' hgj hwm
      have hw_lt : w < 10 + j := hDrb' j hj g' hgj w hwm
      have hcl := hDclean g' (List.mem_of_getElem? hgj)
      apply hdrop_d0_c j hj g' hgj
      rcases (hDfan' g' (List.mem_of_getElem? hgj)).1 with hop | hop | hop
      · exact Or.inr ⟨Or.inl hop, w, hwm, hw_lt, b, hwb⟩
      · exact Or.inr ⟨Or.inr hop, w, hwm, hw_lt, b, hwb⟩
      · refine Or.inl ⟨hop, w, ?_, hw_lt, b, hwb⟩
        have hl1 := hcl.1 hop
        rcases hins : g'.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 hwm; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at hwm; subst hwm; rfl
    have out_ne_const : ∀ (w : ℕ) (b : Bool), env_d0.getD w (Sum.inr false) = Sum.inr b → D.output ≠ w := by
      intro w b hwb heq
      have h0 := hgs_d0_ev D.output (by omega) (fun _ => false)
      have h1 := hgs_d0_ev D.output (by omega) (fun _ => true)
      rw [heq, hwb] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
      have hd0 := hDev (ext0 (fun _ => false))
      have hd1 := hDev (ext0 (fun _ => true))
      change (D.gates.foldl stepW _).getD D.output false = F9 (ext0 (fun _ => false)) at hd0
      change (D.gates.foldl stepW _).getD D.output false = F9 (ext0 (fun _ => true)) at hd1
      rw [heq] at hd0 hd1; rw [hd0] at h0; rw [hd1] at h1
      have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
      exact hne (h0.symm.trans h1)
    by_contra hne_or
    have hconst_p0 : ∃ b0, env_d0.getD (10 + p0) (Sum.inr false) = Sum.inr b0 := by
      have hcl := hDclean g0 (List.mem_of_getElem? hp0_some)
      apply hprop_d0_c p0 hp0_lt g0 hp0_some
      rcases (hDfan' g0 (List.mem_of_getElem? hp0_some)).1 with hop | hop | hop
      · exact Or.inr (Or.inl ⟨hop, 0, hg0_0, by omega, h0c⟩)
      · exact False.elim (hne_or hop)
      · refine Or.inl ⟨hop, 0, ?_, by omega, false, h0c⟩
        have hl1 := hcl.1 hop
        rcases hins : g0.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 hg0_0; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at hg0_0; subst hg0_0; rfl
    obtain ⟨b0, hb0⟩ := hconst_p0
    by_cases hread_p0 : ∃ j < D.gates.length, ∃ g', D.gates[j]? = some g' ∧ (10 + p0) ∈ g'.inputs
    · obtain ⟨j, hj_lt, g', hgj, hmem_j⟩ := hread_p0
      have hj_gt : p0 < j := by have := hDrb' j hj_lt g' hgj (10 + p0) hmem_j; omega
      have hj_drop : j ∈ drop_d0 := drop_of_const_in (10 + p0) b0 hb0 j hj_lt g' hgj hmem_j
      have hj_eq_ph : j = ph := by
        rcases no_third_drop j hj_drop with h1 | h2
        · omega
        · exact h2
      rw [hj_eq_ph] at hj_gt hgj
      have hge : g' = h9 := Option.some.inj (hgj.symm.trans hph_some)
      rw [hge] at hmem_j
      -- Now h9 is OR reading both 9 (false) and 10 + p0 (b0), so 10 + ph is also constant!
      have hclh := hDclean h9 (List.mem_of_getElem? hph_some)
      have hlen2h := (hclh.2 (by rw [hh9_or]; intro h; exact GateOp.noConfusion h)).1
      have hconst_ph : ∃ bh, env_d0.getD (10 + ph) (Sum.inr false) = Sum.inr bh := by
        rcases list_le2 h9.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · rw [hins] at hlen2h; simp at hlen2h
        · rw [hins] at hlen2h; simp at hlen2h
        · rw [hins] at hh9_9 hmem_j
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh9_9 hmem_j
          apply hprop_d0_c ph hph_lt h9 hph_some
          refine Or.inr (Or.inr ⟨hh9_or, a, b, hins, ?_, ?_, ?_, ?_⟩)
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1 <;> omega
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1 <;> omega
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1
            · omega
            · exact ⟨false, h9c⟩
            · subst h1; exact ⟨b0, hb0⟩
            · omega
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1
            · omega
            · subst h1; exact ⟨b0, hb0⟩
            · subst h1; exact ⟨false, h9c⟩
            · omega
      obtain ⟨bh, hbh⟩ := hconst_ph
      by_cases hread_ph : ∃ k < D.gates.length, ∃ g'', D.gates[k]? = some g'' ∧ (10 + ph) ∈ g''.inputs
      · obtain ⟨k, hk_lt, g'', hgk, hmem_k⟩ := hread_ph
        have hk_gt : ph < k := by have := hDrb' k hk_lt g'' hgk (10 + ph) hmem_k; omega
        have hk_drop := drop_of_const_in (10 + ph) bh hbh k hk_lt g'' hgk hmem_k
        rcases no_third_drop k hk_drop with h1 | h2 <;> omega
      · push Not at hread_ph
        have hout_ne_ph : D.output ≠ 10 + ph := out_ne_const (10 + ph) bh hbh
        apply no_drop_wire9_14
        intro y
        have heq := wire_agree D.gates (List.ofFn y ++ [false]) (List.ofFn y ++ [y 0 && y 2])
          (fun i => i = 9 ∨ i = 10 + ph) (by simp)
          (by
            intro i hi hnb
            have hlt9 : i < 9 := by have hne9 : i ≠ 9 := fun h => hnb (Or.inl h); simp at hi; omega
            rw [getD_snoc_lt _ _ _ i (by simp; omega), getD_snoc_lt _ _ _ i (by simp; omega)])
          (by
            intro j hj g'' hgj hnb i hi hibad
            rcases hibad with rfl | rfl
            · have jph := hph_uniq j hj g'' hgj (decide_eq_true hi)
              exact hnb (Or.inr (by simp [jph]))
            · exact hread_ph j hj g'' hgj hi)
          D.output (by rw [foldl_len]; simp; omega)
          (fun hb => by rcases hb with h1 | h2; exact hout_ne9 h1; exact hout_ne_ph h2)
        exact heq.trans (hDev y)
    · push Not at hread_p0
      have hout_ne_p0 : D.output ≠ 10 + p0 := out_ne_const (10 + p0) b0 hb0
      let u1 : Fin 9 → Bool := fun k => decide (k = 1)
      let u2 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 1)
      have heq := wire_agree D.gates (List.ofFn u1 ++ [u1 0 && u1 2]) (List.ofFn u2 ++ [u2 0 && u2 2])
        (fun i => i = 0 ∨ i = 10 + p0) (by simp)
        (by
          intro i hi hnb
          have hne0 : i ≠ 0 := fun h => hnb (Or.inl h)
          have hchk : ∀ j : Fin 10, j.val ≠ 0 →
              (List.ofFn u1 ++ [u1 0 && u1 2]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 && u2 2]).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne0)
        (by
          intro j hj g'' hgj hnb i hi hibad
          rcases hibad with rfl | rfl
          · have jp0 := hp0_uniq j hj g'' hgj (decide_eq_true hi)
            exact hnb (Or.inr (by simp [jp0]))
          · exact hread_p0 j hj g'' hgj hi)
        D.output (by rw [foldl_len]; simp; omega)
        (fun hb => by rcases hb with h1 | h2; exact hout_ne0 h1; exact hout_ne_p0 h2)
      have h1 := hDev u1; have h2 := hDev u2
      change (D.gates.foldl stepW _).getD D.output false = F9 u1 at h1
      change (D.gates.foldl stepW _).getD D.output false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
  -- Step 5: Prove g2.op = GateOp.or via y 2 = false restriction (hDel0 = L_meta_1664)
  have hg2_or : g2.op = GateOp.or := by
    let p2a : Fin 9 → Fin 9 := aut^[4]
    have hp2a_2 : p2a 2 = 0 := by decide
    let ext2 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y => ext0 y ∘ p2a
    let init_d2 : List (ℕ ⊕ Bool) :=
      List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2a i).val (Sum.inr false)) ++ [Sum.inr false]
    obtain ⟨gs_d2, env_d2, drop_d2, henv_d2_len, hinit_d2_eq, _, hsz_d2, hdrop_d2_c, hprop_d2_c,
      hgs_d2_fan, _, _, _, hgs_d2_ev⟩ :=
      simplify 8 10 8 (fun y => List.ofFn (ext2 y) ++ [ext2 y 0 && ext2 y 2]) (fun y => List.ofFn y)
        init_d2 D.gates (by intro y; simp) (by intro y; simp) (by simp [init_d2]) hDfan'
        (by
          intro i hi y
          by_cases hlt : i < 9
          · have hi1 : init_d2.getD i (Sum.inr false) = init_d0_base.getD (p2a ⟨i, hlt⟩).val (Sum.inr false) := by
              dsimp only [init_d2]
              rw [getD_snoc_lt _ _ _ i (by simp; omega)]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
            have hi2 : (List.ofFn (ext2 y) ++ [ext2 y 0 && ext2 y 2]).getD i false = ext0 y (p2a ⟨i, hlt⟩) := by
              rw [getD_snoc_lt _ _ _ i (by simp; omega)]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
                Option.getD_some, ext2, Function.comp_def]
            rw [hi1, hi2]
            have hchk : ∀ j : Fin 9,
                Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d0_base.getD j.val (Sum.inr false)) = ext0 y j := by
              intro j; fin_cases j <;> simp [init_d0_base, ext0]
            exact hchk (p2a ⟨i, hlt⟩)
          · have hieq : i = 9 := by omega
            subst hieq
            have hi1 : init_d2.getD 9 (Sum.inr false) = Sum.inr false := by
              dsimp only [init_d2]
              have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2a i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
              simpa using this
            rw [hi1]; dsimp only [Sum.elim_inr, id_eq]
            have hsn := getD_snoc_eq (List.ofFn (ext2 y)) (ext2 y 0 && ext2 y 2) false
            simp only [List.length_ofFn] at hsn
            rw [hsn]
            have h2f : ext2 y 2 = false := by dsimp [ext2, Function.comp_def]; rw [hp2a_2]; rfl
            rw [h2f, Bool.and_false])
        (by
          intro i hi w hw
          by_cases hlt : i < 9
          · dsimp only [init_d2] at hw
            rw [getD_snoc_lt _ _ _ i (by simp; omega)] at hw
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hw
            have hchk : ∀ j : Fin 9, ∀ u, init_d0_base.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
              intro j u hu; fin_cases j <;> simp [init_d0_base] at hu <;> omega
            exact hchk (p2a ⟨i, hlt⟩) w hw
          · have hieq : i = 9 := by omega
            subst hieq; dsimp only [init_d2] at hw
            have hsn := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2a i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
            simp only [List.length_ofFn] at hsn; rw [hsn] at hw; cases hw)
    have hd2_ge12 : 12 ≤ gs_d2.length := by
      by_contra hle11
      rcases hout_d2 : env_d2.getD D.output (Sum.inr false) with out_d2 | b_d2
      · apply hDel0
        refine ⟨⟨gs_d2, out_d2⟩, ?_, by change gs_d2.length ≤ 11; omega, ?_⟩
        · intro g hg
          have h := hgs_d2_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_d2_ev D.output (by omega) y
          rw [hout_d2] at h; dsimp only [Sum.elim_inl] at h
          have hd := hDev (ext2 y)
          change (D.gates.foldl stepW _).getD D.output false = F9 (ext2 y) at hd
          change (gs_d2.foldl stepW (List.ofFn y)).getD out_d2 false = F8d0 y
          rw [h, hd]; dsimp only [ext2]; rw [aut_pow_inv 4, hF9_ext0]
      · have h0 := hgs_d2_ev D.output (by omega) (fun _ => false)
        have h1 := hgs_d2_ev D.output (by omega) (fun _ => true)
        rw [hout_d2] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hDev (ext2 (fun _ => false))
        have hd1 := hDev (ext2 (fun _ => true))
        change (D.gates.foldl stepW _).getD D.output false = F9 (ext2 (fun _ => false)) at hd0
        change (D.gates.foldl stepW _).getD D.output false = F9 (ext2 (fun _ => true)) at hd1
        rw [hd0] at h0; rw [hd1] at h1
        dsimp only [ext2] at h0 h1; rw [aut_pow_inv 4] at h0; rw [aut_pow_inv 4] at h1
        have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
        exact hne (h0.symm.trans h1)
    have hdrop_le2 : drop_d2.card ≤ 2 := by omega
    have h2c : env_d2.getD 2 (Sum.inr false) = Sum.inr false := by
      rw [hinit_d2_eq 2 (by omega)]
      dsimp only [init_d2]
      rw [getD_snoc_lt _ _ _ 2 (by simp)]
      have hlt2 : 2 < 9 := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2, ↓reduceDIte, Option.getD_some]
      change init_d0_base.getD (p2a 2).val (Sum.inr false) = Sum.inr false
      rw [hp2a_2]; rfl
    have h9c : env_d2.getD 9 (Sum.inr false) = Sum.inr false := by
      rw [hinit_d2_eq 9 (by omega)]; dsimp only [init_d2]
      have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2a i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
      simpa using this
    have hp2_drop : p2 ∈ drop_d2 := by
      have hcl := hDclean g2 (List.mem_of_getElem? hp2_some)
      apply hdrop_d2_c p2 hp2_lt g2 hp2_some
      rcases (hDfan' g2 (List.mem_of_getElem? hp2_some)).1 with hop | hop | hop
      · exact Or.inr ⟨Or.inl hop, 2, hg2_2, by omega, false, h2c⟩
      · exact Or.inr ⟨Or.inr hop, 2, hg2_2, by omega, false, h2c⟩
      · refine Or.inl ⟨hop, 2, ?_, by omega, false, h2c⟩
        have hl1 := hcl.1 hop
        rcases hins : g2.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 hg2_2; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at hg2_2; subst hg2_2; rfl
    have hph_drop : ph ∈ drop_d2 :=
      hdrop_d2_c ph hph_lt h9 hph_some (Or.inr ⟨Or.inr hh9_or, 9, hh9_9, by omega, false, h9c⟩)
    have no_third_drop : ∀ k ∈ drop_d2, k = p2 ∨ k = ph := by
      intro k hk
      by_contra hne
      push Not at hne
      have hsub : ({p2, ph, k} : Finset ℕ) ⊆ drop_d2 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hc2 : ({ph, k} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hne.2)
      have hnm : p2 ∉ ({ph, k} : Finset ℕ) := by simp [hp2_ne_ph, Ne.symm hne.1]
      have hc3 : ({p2, ph, k} : Finset ℕ).card = 3 := by rw [Finset.card_insert_of_notMem hnm, hc2]
      have := Finset.card_le_card hsub; omega
    have drop_of_const_in : ∀ (w : ℕ) (b : Bool), env_d2.getD w (Sum.inr false) = Sum.inr b →
        ∀ j < D.gates.length, ∀ g', D.gates[j]? = some g' → w ∈ g'.inputs → j ∈ drop_d2 := by
      intro w b hwb j hj g' hgj hwm
      have hw_lt : w < 10 + j := hDrb' j hj g' hgj w hwm
      have hcl := hDclean g' (List.mem_of_getElem? hgj)
      apply hdrop_d2_c j hj g' hgj
      rcases (hDfan' g' (List.mem_of_getElem? hgj)).1 with hop | hop | hop
      · exact Or.inr ⟨Or.inl hop, w, hwm, hw_lt, b, hwb⟩
      · exact Or.inr ⟨Or.inr hop, w, hwm, hw_lt, b, hwb⟩
      · refine Or.inl ⟨hop, w, ?_, hw_lt, b, hwb⟩
        have hl1 := hcl.1 hop
        rcases hins : g'.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 hwm; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at hwm; subst hwm; rfl
    have out_ne_const : ∀ (w : ℕ) (b : Bool), env_d2.getD w (Sum.inr false) = Sum.inr b → D.output ≠ w := by
      intro w b hwb heq
      have h0 := hgs_d2_ev D.output (by omega) (fun _ => false)
      have h1 := hgs_d2_ev D.output (by omega) (fun _ => true)
      rw [heq, hwb] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
      have hd0 := hDev (ext2 (fun _ => false))
      have hd1 := hDev (ext2 (fun _ => true))
      change (D.gates.foldl stepW _).getD D.output false = F9 (ext2 (fun _ => false)) at hd0
      change (D.gates.foldl stepW _).getD D.output false = F9 (ext2 (fun _ => true)) at hd1
      rw [heq] at hd0 hd1; rw [hd0] at h0; rw [hd1] at h1
      dsimp only [ext2] at h0 h1; rw [aut_pow_inv 4] at h0; rw [aut_pow_inv 4] at h1
      have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
      exact hne (h0.symm.trans h1)
    by_contra hne_or
    have hconst_p2 : ∃ b2, env_d2.getD (10 + p2) (Sum.inr false) = Sum.inr b2 := by
      have hcl := hDclean g2 (List.mem_of_getElem? hp2_some)
      apply hprop_d2_c p2 hp2_lt g2 hp2_some
      rcases (hDfan' g2 (List.mem_of_getElem? hp2_some)).1 with hop | hop | hop
      · exact Or.inr (Or.inl ⟨hop, 2, hg2_2, by omega, h2c⟩)
      · exact False.elim (hne_or hop)
      · refine Or.inl ⟨hop, 2, ?_, by omega, false, h2c⟩
        have hl1 := hcl.1 hop
        rcases hins : g2.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 hg2_2; simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at hg2_2; subst hg2_2; rfl
    obtain ⟨b2, hb2⟩ := hconst_p2
    by_cases hread_p2 : ∃ j < D.gates.length, ∃ g', D.gates[j]? = some g' ∧ (10 + p2) ∈ g'.inputs
    · obtain ⟨j, hj_lt, g', hgj, hmem_j⟩ := hread_p2
      have hj_gt : p2 < j := by have := hDrb' j hj_lt g' hgj (10 + p2) hmem_j; omega
      have hj_drop : j ∈ drop_d2 := drop_of_const_in (10 + p2) b2 hb2 j hj_lt g' hgj hmem_j
      have hj_eq_ph : j = ph := by
        rcases no_third_drop j hj_drop with h1 | h2
        · omega
        · exact h2
      rw [hj_eq_ph] at hj_gt hgj
      have hge : g' = h9 := Option.some.inj (hgj.symm.trans hph_some)
      rw [hge] at hmem_j
      have hclh := hDclean h9 (List.mem_of_getElem? hph_some)
      have hlen2h := (hclh.2 (by rw [hh9_or]; intro h; exact GateOp.noConfusion h)).1
      have hconst_ph : ∃ bh, env_d2.getD (10 + ph) (Sum.inr false) = Sum.inr bh := by
        rcases list_le2 h9.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · rw [hins] at hlen2h; simp at hlen2h
        · rw [hins] at hlen2h; simp at hlen2h
        · rw [hins] at hh9_9 hmem_j
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh9_9 hmem_j
          apply hprop_d2_c ph hph_lt h9 hph_some
          refine Or.inr (Or.inr ⟨hh9_or, a, b, hins, ?_, ?_, ?_, ?_⟩)
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1 <;> omega
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1 <;> omega
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1
            · omega
            · exact ⟨false, h9c⟩
            · subst h1; exact ⟨b2, hb2⟩
            · omega
          · rcases hh9_9 with rfl | rfl <;> rcases hmem_j with h1 | h1
            · omega
            · subst h1; exact ⟨b2, hb2⟩
            · subst h1; exact ⟨false, h9c⟩
            · omega
      obtain ⟨bh, hbh⟩ := hconst_ph
      by_cases hread_ph : ∃ k < D.gates.length, ∃ g'', D.gates[k]? = some g'' ∧ (10 + ph) ∈ g''.inputs
      · obtain ⟨k, hk_lt, g'', hgk, hmem_k⟩ := hread_ph
        have hk_gt : ph < k := by have := hDrb' k hk_lt g'' hgk (10 + ph) hmem_k; omega
        have hk_drop := drop_of_const_in (10 + ph) bh hbh k hk_lt g'' hgk hmem_k
        rcases no_third_drop k hk_drop with h1 | h2 <;> omega
      · push Not at hread_ph
        have hout_ne_ph : D.output ≠ 10 + ph := out_ne_const (10 + ph) bh hbh
        apply no_drop_wire9_14
        intro y
        have heq := wire_agree D.gates (List.ofFn y ++ [false]) (List.ofFn y ++ [y 0 && y 2])
          (fun i => i = 9 ∨ i = 10 + ph) (by simp)
          (by
            intro i hi hnb
            have hlt9 : i < 9 := by have hne9 : i ≠ 9 := fun h => hnb (Or.inl h); simp at hi; omega
            rw [getD_snoc_lt _ _ _ i (by simp; omega), getD_snoc_lt _ _ _ i (by simp; omega)])
          (by
            intro j hj g'' hgj hnb i hi hibad
            rcases hibad with rfl | rfl
            · have jph := hph_uniq j hj g'' hgj (decide_eq_true hi)
              exact hnb (Or.inr (by simp [jph]))
            · exact hread_ph j hj g'' hgj hi)
          D.output (by rw [foldl_len]; simp; omega)
          (fun hb => by rcases hb with h1 | h2; exact hout_ne9 h1; exact hout_ne_ph h2)
        exact heq.trans (hDev y)
    · push Not at hread_p2
      have hout_ne_p2 : D.output ≠ 10 + p2 := out_ne_const (10 + p2) b2 hb2
      let u1 : Fin 9 → Bool := fun k => decide (k = 1)
      let u2 : Fin 9 → Bool := fun k => decide (k = 1 ∨ k = 2)
      have heq := wire_agree D.gates (List.ofFn u1 ++ [u1 0 && u1 2]) (List.ofFn u2 ++ [u2 0 && u2 2])
        (fun i => i = 2 ∨ i = 10 + p2) (by simp)
        (by
          intro i hi hnb
          have hne2 : i ≠ 2 := fun h => hnb (Or.inl h)
          have hchk : ∀ j : Fin 10, j.val ≠ 2 →
              (List.ofFn u1 ++ [u1 0 && u1 2]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 && u2 2]).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne2)
        (by
          intro j hj g'' hgj hnb i hi hibad
          rcases hibad with rfl | rfl
          · have jp2 := hp2_uniq j hj g'' hgj (decide_eq_true hi)
            exact hnb (Or.inr (by simp [jp2]))
          · exact hread_p2 j hj g'' hgj hi)
        D.output (by rw [foldl_len]; simp; omega)
        (fun hb => by rcases hb with h1 | h2; exact hout_ne2 h1; exact hout_ne_p2 h2)
      have h1 := hDev u1; have h2 := hDev u2
      change (D.gates.foldl stepW _).getD D.output false = F9 u1 at h1
      change (D.gates.foldl stepW _).getD D.output false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
  -- Step 6: Eliminate monotone (0-NOT) circuits via monotonicity + no_drop_wire9_14
  have hnot_pos : 1 ≤ (D.gates.filter (fun g => decide (g.op = GateOp.not))).length := by
    by_contra h0
    have hmono : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have hne : g.op ≠ GateOp.not := by
        intro hnot
        have hm : g ∈ D.gates.filter (fun g => decide (g.op = GateOp.not)) :=
          List.mem_filter.mpr ⟨hg, decide_eq_true hnot⟩
        have := List.length_pos_of_mem hm; omega
      rcases (hDfan' g hg).1 with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact False.elim (hne h3)
    have wires_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ (w1 w2 : List Bool), w1.length = w2.length →
          (∀ i, w1.getD i false = true → w2.getD i false = true) →
          ∀ k, (gs.foldl stepW w1).getD k false = true → (gs.foldl stepW w2).getD k false = true := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro _ w1 w2 _ hle k hk; exact hle k hk
      | append_singleton gs g ih =>
        intro hm w1 w2 hlen hle k hk
        have hm_gs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
          fun h hh => hm h (List.mem_append_left _ hh)
        have hm_g : g.op = GateOp.and ∨ g.op = GateOp.or :=
          hm g (List.mem_append_right _ (List.mem_singleton_self g))
        have hprev := ih hm_gs w1 w2 hlen hle
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hk ⊢
        have hl1 : (gs.foldl stepW w1).length = w1.length + gs.length := foldl_len gs w1
        have hl2 : (gs.foldl stepW w2).length = w1.length + gs.length := by rw [foldl_len, ← hlen]
        by_cases hlt : k < w1.length + gs.length
        · change ((gs.foldl stepW w1) ++ [_]).getD k false = true at hk
          change ((gs.foldl stepW w2) ++ [_]).getD k false = true
          rw [getD_snoc_lt _ _ _ k (by omega)] at hk
          rw [getD_snoc_lt _ _ _ k (by omega)]
          exact hprev k hk
        · by_cases heq : k = w1.length + gs.length
          · subst heq
            change ((gs.foldl stepW w1) ++ [_]).getD (w1.length + gs.length) false = true at hk
            change ((gs.foldl stepW w2) ++ [_]).getD (w1.length + gs.length) false = true
            rw [← hl1, getD_snoc_eq] at hk
            rw [← hl2, getD_snoc_eq]
            rcases hm_g with hand | hor
            · rw [hand, eval_and] at hk ⊢
              rw [List.all_eq_true] at hk ⊢
              intro x hx
              rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
              exact hprev a (hk _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
            · rw [hor, eval_or] at hk ⊢
              rw [List.any_eq_true] at hk ⊢
              rcases hk with ⟨x, hx, hxt⟩
              rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
              exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, hprev a hxt⟩
          · change ((gs.foldl stepW w1) ++ [_]).getD k false = true at hk
            rw [getD_ge _ false k (by simp [hl1]; omega)] at hk
            exact Bool.noConfusion hk
    apply no_drop_wire9_14
    intro y
    have hle_fwd : (D.gates.foldl stepW (List.ofFn y ++ [false])).getD D.output false = true → F9 y = true := by
      intro h1
      have h2 := wires_mono D.gates hmono (List.ofFn y ++ [false]) (List.ofFn y ++ [y 0 && y 2]) (by simp)
        (by
          intro i hi
          by_cases hlt : i < 9
          · rw [getD_snoc_lt _ _ _ i (by simp; omega)] at hi ⊢; exact hi
          · by_cases heq : i = 9
            · subst heq
              have hsn := getD_snoc_eq (List.ofFn y) false false
              simp only [List.length_ofFn] at hsn; rw [hsn] at hi; exact Bool.noConfusion hi
            · rw [getD_ge _ false i (by simp; omega)] at hi; exact Bool.noConfusion hi)
        D.output h1
      have hev := hDev y
      change (D.gates.foldl stepW _).getD D.output false = F9 y at hev
      exact hev.symm.trans h2
    have hle_bwd : F9 y = true → (D.gates.foldl stepW (List.ofFn y ++ [false])).getD D.output false = true := by
      intro hfy
      have hedge : ∃ a b : Fin 9, y a = true ∧ y b = true ∧ F9 (fun k => decide (k = a ∨ k = b)) = true ∧
          (decide (0 = a ∨ 0 = b) && decide (2 = a ∨ 2 = b)) = false := by
        dsimp [F9] at hfy
        rcases Bool.or_eq_true_iff.mp hfy with h1 | h12
        · rcases Bool.or_eq_true_iff.mp h1 with h1 | h11
          · rcases Bool.or_eq_true_iff.mp h1 with h1 | h10
            · rcases Bool.or_eq_true_iff.mp h1 with h1 | h9
              · rcases Bool.or_eq_true_iff.mp h1 with h1 | h8
                · rcases Bool.or_eq_true_iff.mp h1 with h1 | h7
                  · rcases Bool.or_eq_true_iff.mp h1 with h1 | h6
                    · rcases Bool.or_eq_true_iff.mp h1 with h1 | h5
                      · rcases Bool.or_eq_true_iff.mp h1 with h1 | h4
                        · rcases Bool.or_eq_true_iff.mp h1 with h1 | h3
                          · rcases Bool.or_eq_true_iff.mp h1 with h1 | h2
                            · rcases Bool.and_eq_true_iff.mp h1 with ⟨ha, hb⟩; exact ⟨0, 1, ha, hb, by decide, by decide⟩
                            · rcases Bool.and_eq_true_iff.mp h2 with ⟨ha, hb⟩; exact ⟨1, 2, ha, hb, by decide, by decide⟩
                          · rcases Bool.and_eq_true_iff.mp h3 with ⟨ha, hb⟩; exact ⟨2, 3, ha, hb, by decide, by decide⟩
                        · rcases Bool.and_eq_true_iff.mp h4 with ⟨ha, hb⟩; exact ⟨3, 4, ha, hb, by decide, by decide⟩
                      · rcases Bool.and_eq_true_iff.mp h5 with ⟨ha, hb⟩; exact ⟨4, 0, ha, hb, by decide, by decide⟩
                    · rcases Bool.and_eq_true_iff.mp h6 with ⟨ha, hb⟩; exact ⟨0, 5, ha, hb, by decide, by decide⟩
                  · rcases Bool.and_eq_true_iff.mp h7 with ⟨ha, hb⟩; exact ⟨1, 6, ha, hb, by decide, by decide⟩
                · rcases Bool.and_eq_true_iff.mp h8 with ⟨ha, hb⟩; exact ⟨2, 7, ha, hb, by decide, by decide⟩
              · rcases Bool.and_eq_true_iff.mp h9 with ⟨ha, hb⟩; exact ⟨3, 8, ha, hb, by decide, by decide⟩
            · rcases Bool.and_eq_true_iff.mp h10 with ⟨ha, hb⟩; exact ⟨5, 7, ha, hb, by decide, by decide⟩
          · rcases Bool.and_eq_true_iff.mp h11 with ⟨ha, hb⟩; exact ⟨6, 8, ha, hb, by decide, by decide⟩
        · rcases Bool.and_eq_true_iff.mp h12 with ⟨ha, hb⟩; exact ⟨8, 5, ha, hb, by decide, by decide⟩
      obtain ⟨a, b, hya, hyb, hfz, hz02⟩ := hedge
      let z : Fin 9 → Bool := fun k => decide (k = a ∨ k = b)
      have hdz : (D.gates.foldl stepW (List.ofFn z ++ [false])).getD D.output false = true := by
        have h := hDev z
        change (D.gates.foldl stepW (List.ofFn z ++ [z 0 && z 2])).getD D.output false = F9 z at h
        have hz9 : (z 0 && z 2) = false := hz02
        rw [hz9, hfz] at h; exact h
      exact wires_mono D.gates hmono (List.ofFn z ++ [false]) (List.ofFn y ++ [false]) (by simp)
        (by
          intro i hi
          by_cases hlt : i < 9
          · rw [getD_snoc_lt _ _ _ i (by simp; omega)] at hi ⊢
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
            dsimp [z] at hi
            rcases of_decide_eq_true hi with heq | heq <;> rw [heq]
            · exact hya
            · exact hyb
          · by_cases heq : i = 9
            · subst heq
              have hsn := getD_snoc_eq (List.ofFn z) false false
              simp only [List.length_ofFn] at hsn; rw [hsn] at hi; exact Bool.noConfusion hi
            · rw [getD_ge _ false i (by simp; omega)] at hi; exact Bool.noConfusion hi)
        D.output hdz
    cases hlhs : (D.gates.foldl stepW (List.ofFn y ++ [false])).getD D.output false <;> cases hrhs : F9 y
    · rfl
    · have := hle_bwd hrhs; rw [hlhs] at this; exact Bool.noConfusion this
    · have := hle_fwd hlhs; rw [hrhs] at this; exact Bool.noConfusion this
    · rfl
  -- Step 7: Assemble normal form and dispatch to hOneNot (notCount = 1) or hMultiNot (2 ≤ notCount)
  have hor029 : ∀ i ∈ ([0, 2, 9] : List ℕ), ∃ h : Gate,
      h.op = GateOp.or ∧ D.gates.filter (fun g => decide (i ∈ g.inputs)) = [h] := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨g0, hg0_or, hg0_fl⟩
    · exact ⟨g2, hg2_or, hg2_fl⟩
    · exact ⟨h9, hh9_or, hh9_fl⟩
  have hex_not : ∃ i : ℕ, i < 14 ∧ (gateAt D i).op = GateOp.not := by
    have hne : D.gates.filter (fun g => decide (g.op = GateOp.not)) ≠ [] := by
      intro hnil; rw [hnil] at hnot_pos; simp at hnot_pos
    rcases List.exists_mem_of_ne_nil _ hne with ⟨g, hg⟩
    have hg' := List.mem_filter.mp hg
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hg'.1
    refine ⟨i, by omega, ?_⟩
    have hgd : gateAt D i = g := by
      change D.gates.getD i ⟨GateOp.or, []⟩ = g
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt, hi_eq, Option.getD_some]
    rw [hgd]; exact of_decide_eq_true hg'.2
  obtain ⟨i0, hi0_lt, hi0_not⟩ := hex_not
  by_cases htwo : ∃ j : ℕ, j < 14 ∧ j ≠ i0 ∧ (gateAt D j).op = GateOp.not
  · obtain ⟨j0, hj0_lt, hj0_ne, hj0_not⟩ := htwo
    have hpair : ∃ i j : ℕ, i < j ∧ j < 14 ∧ (gateAt D i).op = GateOp.not ∧ (gateAt D j).op = GateOp.not := by
      by_cases hlt : i0 < j0
      · exact ⟨i0, j0, hlt, hj0_lt, hi0_not, hj0_not⟩
      · exact ⟨j0, i0, by omega, hi0_lt, hj0_not, hi0_not⟩
    exact hMultiNot D hDfan hDrb hDclean hDsz hor029 hfilt029_eq3 h467 hpair hDev
  · push Not at htwo
    have huniq : ∃ i : ℕ, i < 14 ∧ (gateAt D i).op = GateOp.not ∧
        ∀ j : ℕ, j < 14 → (gateAt D j).op = GateOp.not → j = i := by
      refine ⟨i0, hi0_lt, hi0_not, ?_⟩
      intro j hj hjnot
      by_contra hne
      exact htwo j hj hne hjnot
    exact hOneNot D hDfan hDrb hDclean hDsz hor029 hfilt029_eq3 h467 huniq hDev
