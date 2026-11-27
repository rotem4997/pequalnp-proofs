import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1668_3 :
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11) →
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
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
      ¬ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 2]) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  classical
  intro hDel4 hDel0 hNo14 hSuff14 C hCfan hFirst hCfun
  by_contra hlt16
  have hCsz : C.size ≤ 15 := by omega
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
  have hCev : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = F9 y := fun y => congrFun hCfun y
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
  have filter_le_card : ∀ (gs : List Gate) (P : Gate → Bool) (S : Finset ℕ),
      (∀ j < gs.length, ∀ g, gs[j]? = some g → P g = true → j ∈ S) →
      (gs.filter P).length ≤ S.card := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro _ _ _; simp
    | append_singleton gs g ih =>
      intro P S hS
      rw [List.filter_append]
      cases hp : P g
      · have hnil : [g].filter P = [] := by simp [hp]
        rw [hnil, List.append_nil]
        apply ih P S
        intro j hj g' hgj hpg'
        apply hS j (by simp; omega) g'
        · rw [List.getElem?_append_left hj]; exact hgj
        · exact hpg'
      · have hsn : [g].filter P = [g] := by simp [hp]
        rw [hsn, List.length_append, List.length_singleton]
        have hmem : gs.length ∈ S := by
          apply hS gs.length (by simp) g
          · rw [List.getElem?_append_right (le_refl gs.length)]; simp
          · exact hp
        have hsub := ih P (S.erase gs.length) (by
          intro j hj g' hgj hpg'
          refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
          apply hS j (by simp; omega) g'
          · rw [List.getElem?_append_left hj]; exact hgj
          · exact hpg')
        have hcard : (S.erase gs.length).card + 1 = S.card := Finset.card_erase_add_one hmem
        omega
  -- General circuit simplifier & constant-propagation pass with dropped-gate accounting
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
           (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a < n_in + j ∧ env.getD a (Sum.inr false) = Sum.inr false)) →
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
            (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a < n_in + gs.length ∧ env.getD a (Sum.inr false) = Sum.inr false)) →
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
               (h.op = GateOp.and ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ env1.getD a (Sum.inr false) = Sum.inr false)) →
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
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inr ⟨ha, a, hain, halt, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            rw [← henv_len, getD_snoc_eq]
            apply hv_prop
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb; exact Or.inr ⟨ha, a, hain, halt, hb⟩
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
               (h.op = GateOp.and ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ env1.getD a (Sum.inr false) = Sum.inr false)) →
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
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨ha, a, hain, halt, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            exfalso; apply hno_c
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨Or.inl ha, a, hain, halt, false, hb⟩
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
          rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
          · rw [hop] at hn; exact GateOp.noConfusion hn
          · rw [hins, List.mem_singleton] at hc_in; subst hc_in
            refine ⟨false, ?_⟩; dsimp [lookup]
            have hlt : c < env.length := by omega
            simp only [hlt, ↓reduceIte, hcf]
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
                rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hins] at hc_in
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                  have hlt : c < env.length := by omega
                  rcases hc_in with rfl | rfl
                  · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                  · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hcf] at hub; cases hub
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
                rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hins] at hc_in
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                  have hlt : c < env.length := by omega
                  rcases hc_in with rfl | rfl
                  · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                  · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hcf] at hub; cases hub
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
              rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
              · rw [hop] at hn; exact GateOp.noConfusion hn
              · rw [hins] at hc_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                have hlt : c < env.length := by omega
                rcases hc_in with rfl | rfl
                · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                · refine ⟨false, ?_⟩; dsimp [lookup]; simp only [hlt, ↓reduceIte, hcf]
      · have hor_vac : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
            (g.op = GateOp.and ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ env.getD c (Sum.inr false) = Sum.inr false)) := by
          intro hc
          rcases hc with ⟨hn, _⟩ | ⟨ha, _⟩ <;> (rw [hop] at *; exact GateOp.noConfusion (by assumption))
        rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr false) (fun hc => False.elim (hor_vac hc)) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_or]; rfl)
        · exact finish_no_add (lookup a) (fun hc => False.elim (hor_vac hc)) (lookup_bd a) (fun y => by
            rw [hop, hins, eval_or]
            simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact lookup_ev a y)
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                exact finish_no_add (Sum.inl w1) (fun hc => False.elim (hor_vac hc))
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl] at ha hb ⊢
                    rw [← ha, ← hb, Bool.or_self])
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
              · exact finish_no_add (Sum.inl w1) (fun hc => False.elim (hor_vac hc))
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                    rw [← ha, ← hb, Bool.or_false])
              · exact finish_no_add (Sum.inr true) (fun hc => False.elim (hor_vac hc)) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.or_true])
          · cases b1
            · exact finish_no_add (lookup b) (fun hc => False.elim (hor_vac hc)) (lookup_bd b) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.false_or]
                exact lookup_ev b y)
            · exact finish_no_add (Sum.inr true) (fun hc => False.elim (hor_vac hc)) (fun _ h => by cases h) (fun y => by
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
  -- Step 1: Peel first gate of C (wire 9 = y 0 && y 2) and pick a MINIMUM-length suffix computing F9
  rcases hCg : C.gates with _ | ⟨g0, tail⟩
  · have hbad := hFirst (fun _ => true)
    change (C.gates.foldl stepW (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = true at hbad
    rw [hCg, List.foldl_nil, getD_ge _ false 9 (by simp)] at hbad
    exact Bool.noConfusion hbad
  have hstep0 : ∀ y : Fin 9 → Bool,
      stepW (List.ofFn y) g0 = List.ofFn y ++ [y 0 && y 2] := by
    intro y
    have h := hFirst y
    change (C.gates.foldl stepW (List.ofFn y)).getD 9 false = (y 0 && y 2) at h
    rw [hCg, List.foldl_cons] at h
    have hlen0 : (stepW (List.ofFn y) g0).length = 10 := by
      change ((List.ofFn y) ++ [_]).length = 10
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    rw [foldl_getD_lt tail _ 9 (by omega)] at h
    have hval : g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) = (y 0 && y 2) := by
      have h9 := getD_snoc_eq (List.ofFn y) (g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)) false
      rw [List.length_ofFn] at h9
      exact h9.symm.trans h
    change List.ofFn y ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)] = _
    rw [hval]
  let IsSuffix : ℕ → Prop := fun m =>
    ∃ (gs : List Gate) (out : ℕ), gs.length = m ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
      ∀ y : Fin 9 → Bool, (gs.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD out false = F9 y
  have hex_suf : ∃ m, IsSuffix m := by
    refine ⟨tail.length, tail, C.output, rfl, ?_, ?_⟩
    · intro g hg
      have h := hCfan g (by rw [hCg]; exact List.mem_cons_of_mem _ hg)
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
    · intro y
      have hc := hCev y
      change (C.gates.foldl stepW (List.ofFn y)).getD C.output false = F9 y at hc
      rw [hCg, List.foldl_cons, hstep0 y] at hc
      exact hc
  let m0 := Nat.find hex_suf
  have hm0_le : m0 ≤ 14 := by
    have hle : m0 ≤ tail.length := Nat.find_min' hex_suf (by
      refine ⟨tail, C.output, rfl, ?_, ?_⟩
      · intro g hg
        have h := hCfan g (by rw [hCg]; exact List.mem_cons_of_mem _ hg)
        exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
      · intro y
        have hc := hCev y
        change (C.gates.foldl stepW (List.ofFn y)).getD C.output false = F9 y at hc
        rw [hCg, List.foldl_cons, hstep0 y] at hc
        exact hc)
    change C.gates.length ≤ 15 at hCsz
    rw [hCg, List.length_cons] at hCsz
    omega
  obtain ⟨gs0, out0, hgs0_len, hgs0_fan, hgs0_ev⟩ := Nat.find_spec hex_suf
  -- Clean gs0 via simplify; by minimality gs1.length = m0
  let init10 : List (ℕ ⊕ Bool) := List.ofFn (fun i : Fin 10 => Sum.inl i.val)
  obtain ⟨gs1, env1, _, henv1_len, _, _, hsz1, _, _, hgs1_fan, hgs1_rb, hgs1_clean, _, hgs1_ev⟩ :=
    simplify 9 10 10 (fun y => List.ofFn y ++ [y 0 && y 2]) (fun y => List.ofFn y ++ [y 0 && y 2])
      init10 gs0 (by intro y; simp) (by intro y; simp) (by simp [init10]) hgs0_fan
      (by
        intro i hi y
        simp only [init10, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.elim_inl])
      (by
        intro i hi w hw
        simp only [init10, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.inl.injEq] at hw
        omega)
  have hout0_lt : out0 < env1.length := by
    by_contra hge
    have h1 := hgs0_ev (fun _ => true)
    have hge' : (gs0.foldl stepW (List.ofFn (fun _ : Fin 9 => true) ++ [true && true])).length ≤ out0 := by
      rw [foldl_len]; simp; omega
    have hval := getD_ge _ false out0 hge'
    rw [hval] at h1
    exact Bool.noConfusion h1
  rcases hout1 : env1.getD out0 (Sum.inr false) with out1 | b_const
  · let D : Circuit := ⟨gs1, out1⟩
    have hD_ev : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 && y 2]) = F9 y := by
      intro y
      have h := hgs1_ev out0 hout0_lt y
      rw [hout1] at h
      dsimp only [Sum.elim_inl] at h
      change (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD out1 false = F9 y
      exact h.trans (hgs0_ev y)
    have hgs1_min : ∀ (gs' : List Gate) (o' : ℕ),
        (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
        (∀ y : Fin 9 → Bool, (gs'.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD o' false = F9 y) →
        gs1.length ≤ gs'.length := by
      intro gs' o' hf' he'
      have hge : m0 ≤ gs'.length := Nat.find_min' hex_suf ⟨gs', o', rfl, hf', he'⟩
      omega
    have hgs1_le14 : gs1.length ≤ 14 := by omega
    have hout1_lt10 : out1 < 10 + gs1.length := by
      by_contra hge
      have h := hD_ev (fun _ => true)
      change (gs1.foldl stepW (List.ofFn (fun _ : Fin 9 => true) ++ [true && true])).getD out1 false = _ at h
      rw [getD_ge _ false out1 (by rw [foldl_len]; simp; omega)] at h
      exact Bool.noConfusion h
    -- Helper: if gate at `pos` equals an earlier wire `repl < 10 + pos` on all inputs, contradicts minimality!
    have no_equiv_gate : ∀ (pos : ℕ) (g : Gate) (repl : ℕ),
        pos < gs1.length → gs1[pos]? = some g → repl < 10 + pos →
        (∀ y : Fin 9 → Bool,
          (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD (10 + pos) false =
          (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD repl false) → False := by
      intro pos g repl hpos hgs_pos hrepl heq_w
      let pre := gs1.take pos
      let suf := gs1.drop (pos + 1)
      have hsplit : gs1 = pre ++ [g] ++ suf := by
        have h1 : gs1 = gs1.take pos ++ gs1.drop pos := (List.take_append_drop pos gs1).symm
        have hdrop : gs1.drop pos = g :: gs1.drop (pos + 1) := by
          have hget : gs1[pos] = g := by
            have := List.getElem?_eq_getElem hpos
            rw [this] at hgs_pos; injection hgs_pos
          rw [← hget]
          exact List.drop_eq_getElem_cons hpos
        rw [h1, hdrop]; simp [pre, suf]
      have hpre_len : pre.length = pos := List.length_take_of_le (by omega)
      have hpre_fan : ∀ h ∈ pre, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
        fun h hh => hgs1_fan h (by rw [hsplit]; exact List.mem_append_left _ (List.mem_append_left _ hh))
      have hsuf_fan : ∀ h ∈ suf, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
        fun h hh => hgs1_fan h (by rw [hsplit]; exact List.mem_append_right _ hh)
      let w_pre : (Fin 9 → Bool) → List Bool := fun y => pre.foldl stepW (List.ofFn y ++ [y 0 && y 2])
      let w_mid : (Fin 9 → Bool) → List Bool := fun y => (pre ++ [g]).foldl stepW (List.ofFn y ++ [y 0 && y 2])
      have hw_pre_len : ∀ y, (w_pre y).length = 10 + pos := by
        intro y; dsimp [w_pre]; rw [foldl_len]; simp [hpre_len]
      have hw_mid_len : ∀ y, (w_mid y).length = 10 + pos + 1 := by
        intro y; dsimp [w_mid]; rw [foldl_len]; simp [hpre_len]; omega
      let init_r : List (ℕ ⊕ Bool) := List.ofFn (fun i : Fin (10 + pos) => Sum.inl i.val) ++ [Sum.inl repl]
      obtain ⟨suf', env_r, _, henv_r_len, _, _, hsz_r, _, _, hsuf'_fan, _, _, _, hsuf'_ev⟩ :=
        simplify 9 (10 + pos + 1) (10 + pos) w_mid w_pre init_r suf hw_mid_len hw_pre_len
          (by simp [init_r]) hsuf_fan
          (by
            intro i hi y
            by_cases hlt : i < 10 + pos
            · have hi1 : init_r.getD i (Sum.inr false) = Sum.inl i := by
                dsimp only [init_r]
                rw [getD_snoc_lt _ _ _ i (by simp; omega)]
                simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
              rw [hi1]; dsimp only [Sum.elim_inl, w_mid, w_pre]
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              change _ = ((pre.foldl stepW _) ++ [_]).getD i false
              rw [getD_snoc_lt _ _ _ i (by rw [foldl_len]; simp [hpre_len]; omega)]
            · have hieq : i = 10 + pos := by omega
              subst hieq
              have hi1 : init_r.getD (10 + pos) (Sum.inr false) = Sum.inl repl := by
                dsimp only [init_r]
                have := getD_snoc_eq (List.ofFn (fun i : Fin (10 + pos) => (Sum.inl i.val : ℕ ⊕ Bool))) (Sum.inl repl) (Sum.inr false)
                simpa using this
              rw [hi1]; dsimp only [Sum.elim_inl]
              have h1 := heq_w y
              rw [hsplit, List.foldl_append] at h1
              have hlt1 : 10 + pos < (w_mid y).length := by rw [hw_mid_len]; omega
              have hlt2 : repl < (w_mid y).length := by rw [hw_mid_len]; omega
              rw [foldl_getD_lt suf (w_mid y) (10 + pos) hlt1, foldl_getD_lt suf (w_mid y) repl hlt2] at h1
              rw [h1]; dsimp only [w_mid, w_pre]
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              change _ = ((pre.foldl stepW _) ++ [_]).getD repl false
              rw [getD_snoc_lt _ _ _ repl (by rw [foldl_len]; simp [hpre_len]; omega)])
          (by
            intro i hi w hw
            by_cases hlt : i < 10 + pos
            · dsimp only [init_r] at hw
              rw [getD_snoc_lt _ _ _ i (by simp; omega)] at hw
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
                Option.getD_some, Sum.inl.injEq] at hw
              omega
            · have hieq : i = 10 + pos := by omega
              subst hieq; dsimp only [init_r] at hw
              have hsn := getD_snoc_eq (List.ofFn (fun i : Fin (10 + pos) => (Sum.inl i.val : ℕ ⊕ Bool))) (Sum.inl repl) (Sum.inr false)
              simp only [List.length_ofFn] at hsn
              rw [hsn] at hw; injection hw with hw'; omega)
      have hlen_split : gs1.length = pos + 1 + suf.length := by
        have := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons, List.length_nil, hpre_len] at this
        exact this
      rcases hout_r : env_r.getD out1 (Sum.inr false) with out_r | b_r
      · have hle_min := hgs1_min (pre ++ suf') out_r
          (fun h hh => by
            rcases List.mem_append.mp hh with h1 | h2
            · exact hpre_fan h h1
            · exact hsuf'_fan h h2)
          (fun y => by
            have h := hsuf'_ev out1 (by omega) y
            rw [hout_r] at h
            dsimp only [Sum.elim_inl] at h
            rw [List.foldl_append]
            have hd := hD_ev y
            change (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD out1 false = F9 y at hd
            rw [hsplit, List.foldl_append] at hd
            exact h.trans hd)
        simp only [List.length_append, hpre_len] at hle_min
        omega
      · have h0 := hsuf'_ev out1 (by omega) (fun _ => false)
        have h1 := hsuf'_ev out1 (by omega) (fun _ => true)
        rw [hout_r] at h0 h1
        dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hD_ev (fun _ => false)
        have hd1 := hD_ev (fun _ => true)
        change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
        rw [hsplit, List.foldl_append] at hd0 hd1
        rw [hd0] at h0; rw [hd1] at h1
        have hne : F9 (fun _ => false) ≠ F9 (fun _ => true) := by decide
        exact hne (h0.symm.trans h1)
    -- Consequence of minimality: no gate in gs1 has inputs {0, 9} or {2, 9}!
    have no_09 : ∀ j < gs1.length, ∀ g, gs1[j]? = some g → ¬ (0 ∈ g.inputs ∧ 9 ∈ g.inputs) := by
      intro j hj g hgj hpair
      have h0m := hpair.1
      have h9m := hpair.2
      have hcl := hgs1_clean g (List.mem_of_getElem? hgj)
      have hgt_ev : ∀ y : Fin 9 → Bool,
          (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD (10 + j) false =
            g.op.eval (g.inputs.map fun i =>
              (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD i false) := by
        intro y
        have hsplit : gs1 = gs1.take j ++ [g] ++ gs1.drop (j + 1) := by
          have h1 := (List.take_append_drop j gs1).symm
          have hget : gs1[j] = g := by rw [List.getElem?_eq_getElem hj] at hgj; injection hgj
          rw [h1, ← hget, List.drop_eq_getElem_cons hj]; simp
        have htake : (gs1.take j).length = j := List.length_take_of_le (by omega)
        have hpre_l : ((gs1.take j).foldl stepW (List.ofFn y ++ [y 0 && y 2])).length = 10 + j := by
          rw [foldl_len]; simp [htake]
        rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hmid_l : (stepW ((gs1.take j).foldl stepW (List.ofFn y ++ [y 0 && y 2])) g).length = 10 + j + 1 := by
          change (((gs1.take j).foldl stepW (List.ofFn y ++ [y 0 && y 2])) ++ [_]).length = 10 + j + 1
          simp only [List.length_append, List.length_cons, List.length_nil, hpre_l]
        rw [foldl_getD_lt (gs1.drop (j + 1)) _ (10 + j) (by omega)]
        change (((gs1.take j).foldl stepW _) ++ [_]).getD (10 + j) false = _
        rw [← hpre_l, getD_snoc_eq]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < 10 + j := by
          have hrb := hgs1_rb j hj a
          have hget : gs1.getD j ⟨GateOp.or, []⟩ = g := by simp only [List.getD_eq_getElem?_getD, hgj, Option.getD_some]
          rw [hget] at hrb; exact hrb ha
        rw [foldl_getD_lt (gs1.drop (j + 1)) _ a (by omega)]
        change _ = (((gs1.take j).foldl stepW _) ++ [_]).getD a false
        rw [getD_snoc_lt _ _ _ a (by omega)]
      have hw0 : ∀ y : Fin 9 → Bool, (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 0 false = y 0 := by
        intro y; rw [foldl_getD_lt gs1 _ 0 (by simp)]
        simp [List.getD_eq_getElem?_getD]
      have hw9 : ∀ y : Fin 9 → Bool, (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 9 false = (y 0 && y 2) := by
        intro y; rw [foldl_getD_lt gs1 _ 9 (by simp)]
        have := getD_snoc_eq (List.ofFn y) (y 0 && y 2) false
        simpa using this
      rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
      · have hlen2 := (hcl.2 (by rw [hop]; intro h; exact GateOp.noConfusion h)).1
        rcases list_le2 g.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at h0m h9m
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h0m h9m
          apply no_equiv_gate j g 9 hj hgj (by omega)
          intro y; rw [hgt_ev y, hop, hins, eval_and]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases h0m with rfl | rfl <;> rcases h9m with h1 | h1
          · omega
          · subst h1; rw [hw0, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · subst h1; rw [hw0, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · omega
      · have hlen2 := (hcl.2 (by rw [hop]; intro h; exact GateOp.noConfusion h)).1
        rcases list_le2 g.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at h0m h9m
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h0m h9m
          apply no_equiv_gate j g 0 hj hgj (by omega)
          intro y; rw [hgt_ev y, hop, hins, eval_or]
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rcases h0m with rfl | rfl <;> rcases h9m with h1 | h1
          · omega
          · subst h1; rw [hw0, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · subst h1; rw [hw0, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · omega
      · have hlen1 := hcl.1 hop
        rcases hins : g.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hlen1; simp at hlen1
        · rw [hins] at hlen1 h0m h9m
          simp only [List.length_cons] at hlen1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at h0m h9m; omega
    have no_29 : ∀ j < gs1.length, ∀ g, gs1[j]? = some g → ¬ (2 ∈ g.inputs ∧ 9 ∈ g.inputs) := by
      intro j hj g hgj hpair
      have h2m := hpair.1
      have h9m := hpair.2
      have hcl := hgs1_clean g (List.mem_of_getElem? hgj)
      have hgt_ev : ∀ y : Fin 9 → Bool,
          (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD (10 + j) false =
            g.op.eval (g.inputs.map fun i =>
              (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD i false) := by
        intro y
        have hsplit : gs1 = gs1.take j ++ [g] ++ gs1.drop (j + 1) := by
          have h1 := (List.take_append_drop j gs1).symm
          have hget : gs1[j] = g := by rw [List.getElem?_eq_getElem hj] at hgj; injection hgj
          rw [h1, ← hget, List.drop_eq_getElem_cons hj]; simp
        have htake : (gs1.take j).length = j := List.length_take_of_le (by omega)
        have hpre_l : ((gs1.take j).foldl stepW (List.ofFn y ++ [y 0 && y 2])).length = 10 + j := by
          rw [foldl_len]; simp [htake]
        rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hmid_l : (stepW ((gs1.take j).foldl stepW (List.ofFn y ++ [y 0 && y 2])) g).length = 10 + j + 1 := by
          change (((gs1.take j).foldl stepW (List.ofFn y ++ [y 0 && y 2])) ++ [_]).length = 10 + j + 1
          simp only [List.length_append, List.length_cons, List.length_nil, hpre_l]
        rw [foldl_getD_lt (gs1.drop (j + 1)) _ (10 + j) (by omega)]
        change (((gs1.take j).foldl stepW _) ++ [_]).getD (10 + j) false = _
        rw [← hpre_l, getD_snoc_eq]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < 10 + j := by
          have hrb := hgs1_rb j hj a
          have hget : gs1.getD j ⟨GateOp.or, []⟩ = g := by simp only [List.getD_eq_getElem?_getD, hgj, Option.getD_some]
          rw [hget] at hrb; exact hrb ha
        rw [foldl_getD_lt (gs1.drop (j + 1)) _ a (by omega)]
        change _ = (((gs1.take j).foldl stepW _) ++ [_]).getD a false
        rw [getD_snoc_lt _ _ _ a (by omega)]
      have hw2 : ∀ y : Fin 9 → Bool, (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 2 false = y 2 := by
        intro y; rw [foldl_getD_lt gs1 _ 2 (by simp)]
        simp [List.getD_eq_getElem?_getD]
      have hw9 : ∀ y : Fin 9 → Bool, (gs1.foldl stepW (List.ofFn y ++ [y 0 && y 2])).getD 9 false = (y 0 && y 2) := by
        intro y; rw [foldl_getD_lt gs1 _ 9 (by simp)]
        have := getD_snoc_eq (List.ofFn y) (y 0 && y 2) false
        simpa using this
      rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
      · have hlen2 := (hcl.2 (by rw [hop]; intro h; exact GateOp.noConfusion h)).1
        rcases list_le2 g.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at h2m h9m
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2m h9m
          apply no_equiv_gate j g 9 hj hgj (by omega)
          intro y; rw [hgt_ev y, hop, hins, eval_and]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases h2m with rfl | rfl <;> rcases h9m with h1 | h1
          · omega
          · subst h1; rw [hw2, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · subst h1; rw [hw2, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · omega
      · have hlen2 := (hcl.2 (by rw [hop]; intro h; exact GateOp.noConfusion h)).1
        rcases list_le2 g.inputs (by omega) with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at hlen2; simp at hlen2
        · rw [hins] at h2m h9m
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2m h9m
          apply no_equiv_gate j g 2 hj hgj (by omega)
          intro y; rw [hgt_ev y, hop, hins, eval_or]
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rcases h2m with rfl | rfl <;> rcases h9m with h1 | h1
          · omega
          · subst h1; rw [hw2, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · subst h1; rw [hw2, hw9]; cases y 0 <;> cases y 2 <;> rfl
          · omega
      · have hlen1 := hcl.1 hop
        rcases hins : g.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hlen1; simp at hlen1
        · rw [hins] at hlen1 h2m h9m
          simp only [List.length_cons] at hlen1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at h2m h9m; omega
    -- Wire-insensitivity lemma
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
    -- Prove out1 ≠ 0, out1 ≠ 2, out1 ≠ 9, and deg(0) ≥ 1, deg(2) ≥ 1, deg(9) ≥ 1
    have hout1_ne0 : out1 ≠ 0 := by
      intro heq
      have h := hD_ev (fun k => decide (k = 0))
      change (gs1.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 0)) ++ [true && false])).getD out1 false = _ at h
      rw [heq, foldl_getD_lt gs1 _ 0 (by simp)] at h
      have hl : (List.ofFn (fun k : Fin 9 => decide (k = 0)) ++ [true && false]).getD 0 false = true := by decide
      have hr : F9 (fun k => decide (k = 0)) = false := by decide
      rw [hl, hr] at h; exact Bool.noConfusion h
    have hout1_ne2 : out1 ≠ 2 := by
      intro heq
      have h := hD_ev (fun k => decide (k = 2))
      change (gs1.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 2)) ++ [false && true])).getD out1 false = _ at h
      rw [heq, foldl_getD_lt gs1 _ 2 (by simp)] at h
      have hl : (List.ofFn (fun k : Fin 9 => decide (k = 2)) ++ [false && true]).getD 2 false = true := by decide
      have hr : F9 (fun k => decide (k = 2)) = false := by decide
      rw [hl, hr] at h; exact Bool.noConfusion h
    have hout1_ne9 : out1 ≠ 9 := by
      intro heq
      have h := hD_ev (fun k => decide (k = 0 ∨ k = 2))
      change (gs1.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 0 ∨ k = 2)) ++ [true && true])).getD out1 false = _ at h
      rw [heq, foldl_getD_lt gs1 _ 9 (by simp)] at h
      have hl : (List.ofFn (fun k : Fin 9 => decide (k = 0 ∨ k = 2)) ++ [true && true]).getD 9 false = true := by decide
      have hr : F9 (fun k => decide (k = 0 ∨ k = 2)) = false := by decide
      rw [hl, hr] at h; exact Bool.noConfusion h
    have hr0_pos : 1 ≤ (gs1.filter (fun g => decide (0 ∈ g.inputs))).length := by
      by_contra h0
      have hnone : ∀ g ∈ gs1, 0 ∉ g.inputs := by
        intro g hg hm
        have hmem : g ∈ gs1.filter (fun g => decide (0 ∈ g.inputs)) := List.mem_filter.mpr ⟨hg, decide_eq_true hm⟩
        have := List.length_pos_of_mem hmem
        omega
      let u1 : Fin 9 → Bool := fun k => decide (k = 1)
      let u2 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 1)
      have heq := wire_agree gs1 (List.ofFn u1 ++ [u1 0 && u1 2]) (List.ofFn u2 ++ [u2 0 && u2 2])
        (fun i => i = 0) (by simp)
        (by
          intro i hi hne
          have hchk : ∀ j : Fin 10, j.val ≠ 0 →
              (List.ofFn u1 ++ [u1 0 && u1 2]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 && u2 2]).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne)
        (by intro j _ g hgj _ i hi he; subst he; exact hnone g (List.mem_of_getElem? hgj) hi)
        out1 (by rw [foldl_len]; simp; omega) hout1_ne0
      have h1 := hD_ev u1; have h2 := hD_ev u2
      change (gs1.foldl stepW _).getD out1 false = F9 u1 at h1
      change (gs1.foldl stepW _).getD out1 false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
    have hr2_pos : 1 ≤ (gs1.filter (fun g => decide (2 ∈ g.inputs))).length := by
      by_contra h0
      have hnone : ∀ g ∈ gs1, 2 ∉ g.inputs := by
        intro g hg hm
        have hmem : g ∈ gs1.filter (fun g => decide (2 ∈ g.inputs)) := List.mem_filter.mpr ⟨hg, decide_eq_true hm⟩
        have := List.length_pos_of_mem hmem
        omega
      let u1 : Fin 9 → Bool := fun k => decide (k = 1)
      let u2 : Fin 9 → Bool := fun k => decide (k = 1 ∨ k = 2)
      have heq := wire_agree gs1 (List.ofFn u1 ++ [u1 0 && u1 2]) (List.ofFn u2 ++ [u2 0 && u2 2])
        (fun i => i = 2) (by simp)
        (by
          intro i hi hne
          have hchk : ∀ j : Fin 10, j.val ≠ 2 →
              (List.ofFn u1 ++ [u1 0 && u1 2]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 && u2 2]).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne)
        (by intro j _ g hgj _ i hi he; subst he; exact hnone g (List.mem_of_getElem? hgj) hi)
        out1 (by rw [foldl_len]; simp; omega) hout1_ne2
      have h1 := hD_ev u1; have h2 := hD_ev u2
      change (gs1.foldl stepW _).getD out1 false = F9 u1 at h1
      change (gs1.foldl stepW _).getD out1 false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
    -- Helper: if gs1 computes F9 even when wire 9 is replaced by false, contradicts hNo14!
    have no_drop_wire9 : (∀ y : Fin 9 → Bool,
        (gs1.foldl stepW (List.ofFn y ++ [false])).getD out1 false = F9 y) → False := by
      intro hf9
      let init_f9 : List (ℕ ⊕ Bool) := List.ofFn (fun i : Fin 9 => Sum.inl i.val) ++ [Sum.inr false]
      obtain ⟨gs_f9, env_f9, _, henv_f9_len, _, _, hsz_f9, _, _, hgs_f9_fan, _, _, _, hgs_f9_ev⟩ :=
        simplify 9 10 9 (fun y => List.ofFn y ++ [false]) (fun y => List.ofFn y) init_f9 gs1
          (by intro y; simp) (by intro y; simp) (by simp [init_f9]) hgs1_fan
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
      rcases hout_f9 : env_f9.getD out1 (Sum.inr false) with out_f9 | b_f9
      · apply hNo14
        refine ⟨⟨gs_f9, out_f9⟩, ?_, by change gs_f9.length ≤ 14; omega, ?_⟩
        · intro g hg
          have h := hgs_f9_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_f9_ev out1 (by omega) y
          rw [hout_f9] at h; dsimp only [Sum.elim_inl] at h
          change (gs_f9.foldl stepW (List.ofFn y)).getD out_f9 false = F9 y
          exact h.trans (hf9 y)
      · have h0 := hgs_f9_ev out1 (by omega) (fun _ => false)
        have h1 := hgs_f9_ev out1 (by omega) (fun _ => true)
        rw [hout_f9] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
        rw [hf9] at h0 h1
        have hne : F9 (fun _ => false) ≠ F9 (fun _ => true) := by decide
        exact hne (h0.symm.trans h1)
    have hr9_pos : 1 ≤ (gs1.filter (fun g => decide (9 ∈ g.inputs))).length := by
      by_contra h0
      have hnone : ∀ g ∈ gs1, 9 ∉ g.inputs := by
        intro g hg hm
        have hmem : g ∈ gs1.filter (fun g => decide (9 ∈ g.inputs)) := List.mem_filter.mpr ⟨hg, decide_eq_true hm⟩
        have := List.length_pos_of_mem hmem
        omega
      apply no_drop_wire9
      intro y
      have heq := wire_agree gs1 (List.ofFn y ++ [false]) (List.ofFn y ++ [y 0 && y 2])
        (fun i => i = 9) (by simp)
        (by
          intro i hi hne
          have hlt : i < 9 := by simp at hi; omega
          rw [getD_snoc_lt _ _ _ i (by simp; omega), getD_snoc_lt _ _ _ i (by simp; omega)])
        (by intro j _ g hgj _ i hi he; subst he; exact hnone g (List.mem_of_getElem? hgj) hi)
        out1 (by rw [foldl_len]; simp; omega) hout1_ne9
      exact heq.trans (hD_ev y)
    -- Step 2: Automorphism of P - v9 and restrictions at y 0 = false and y 2 = false (both give F8d0!)
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
    -- Restrict gs1 at y 0 = false (sets BOTH wire 0 AND wire 9 to Sum.inr false!)
    let init_d0 : List (ℕ ⊕ Bool) := init_d0_base ++ [Sum.inr false]
    obtain ⟨gs_d0, env_d0, drop_d0, henv_d0_len, hinit_d0_eq, _, hsz_d0, hdrop_d0_c, hprop_d0_c,
      hgs_d0_fan, _, _, _, hgs_d0_ev⟩ :=
      simplify 8 10 8 (fun y => List.ofFn (ext0 y) ++ [ext0 y 0 && ext0 y 2]) (fun y => List.ofFn y)
        init_d0 gs1 (by intro y; simp) (by intro y; simp) rfl hgs1_fan
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
      rcases hout_d0 : env_d0.getD out1 (Sum.inr false) with out_d0 | b_d0
      · apply hDel0
        refine ⟨⟨gs_d0, out_d0⟩, ?_, by change gs_d0.length ≤ 11; omega, ?_⟩
        · intro g hg
          have h := hgs_d0_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_d0_ev out1 (by omega) y
          rw [hout_d0] at h; dsimp only [Sum.elim_inl] at h
          have hd := hD_ev (ext0 y)
          change (gs1.foldl stepW _).getD out1 false = F9 (ext0 y) at hd
          change (gs_d0.foldl stepW (List.ofFn y)).getD out_d0 false = F8d0 y
          rw [h, hd, hF9_ext0]
      · have h0 := hgs_d0_ev out1 (by omega) (fun _ => false)
        have h1 := hgs_d0_ev out1 (by omega) (fun _ => true)
        rw [hout_d0] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hD_ev (ext0 (fun _ => false))
        have hd1 := hD_ev (ext0 (fun _ => true))
        change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
        rw [hd0] at h0; rw [hd1] at h1
        have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
        exact hne (h0.symm.trans h1)
    -- Restrict gs1 at y 2 = false (via p2 = aut^[4], sets BOTH wire 2 AND wire 9 to Sum.inr false!)
    let p2 : Fin 9 → Fin 9 := aut^[4]
    have hp2_2 : p2 2 = 0 := by decide
    let ext2 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y => ext0 y ∘ p2
    let init_d2 : List (ℕ ⊕ Bool) :=
      List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2 i).val (Sum.inr false)) ++ [Sum.inr false]
    obtain ⟨gs_d2, env_d2, drop_d2, henv_d2_len, hinit_d2_eq, _, hsz_d2, hdrop_d2_c, hprop_d2_c,
      hgs_d2_fan, _, _, _, hgs_d2_ev⟩ :=
      simplify 8 10 8 (fun y => List.ofFn (ext2 y) ++ [ext2 y 0 && ext2 y 2]) (fun y => List.ofFn y)
        init_d2 gs1 (by intro y; simp) (by intro y; simp) (by simp [init_d2]) hgs1_fan
        (by
          intro i hi y
          by_cases hlt : i < 9
          · have hi1 : init_d2.getD i (Sum.inr false) = init_d0_base.getD (p2 ⟨i, hlt⟩).val (Sum.inr false) := by
              dsimp only [init_d2]
              rw [getD_snoc_lt _ _ _ i (by simp; omega)]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
            have hi2 : (List.ofFn (ext2 y) ++ [ext2 y 0 && ext2 y 2]).getD i false = ext0 y (p2 ⟨i, hlt⟩) := by
              rw [getD_snoc_lt _ _ _ i (by simp; omega)]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
                Option.getD_some, ext2, Function.comp_def]
            rw [hi1, hi2]
            have hchk : ∀ j : Fin 9,
                Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d0_base.getD j.val (Sum.inr false)) = ext0 y j := by
              intro j; fin_cases j <;> simp [init_d0_base, ext0]
            exact hchk (p2 ⟨i, hlt⟩)
          · have hieq : i = 9 := by omega
            subst hieq
            have hi1 : init_d2.getD 9 (Sum.inr false) = Sum.inr false := by
              dsimp only [init_d2]
              have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2 i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
              simpa using this
            rw [hi1]; dsimp only [Sum.elim_inr, id_eq]
            have hsn := getD_snoc_eq (List.ofFn (ext2 y)) (ext2 y 0 && ext2 y 2) false
            simp only [List.length_ofFn] at hsn
            rw [hsn]
            have h2f : ext2 y 2 = false := by dsimp [ext2, Function.comp_def]; rw [hp2_2]; rfl
            rw [h2f, Bool.and_false])
        (by
          intro i hi w hw
          by_cases hlt : i < 9
          · dsimp only [init_d2] at hw
            rw [getD_snoc_lt _ _ _ i (by simp; omega)] at hw
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hw
            have hchk : ∀ j : Fin 9, ∀ u, init_d0_base.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
              intro j u hu; fin_cases j <;> simp [init_d0_base] at hu <;> omega
            exact hchk (p2 ⟨i, hlt⟩) w hw
          · have hieq : i = 9 := by omega
            subst hieq; dsimp only [init_d2] at hw
            have hsn := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2 i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
            simp only [List.length_ofFn] at hsn; rw [hsn] at hw; cases hw)
    have hd2_ge12 : 12 ≤ gs_d2.length := by
      by_contra hle11
      rcases hout_d2 : env_d2.getD out1 (Sum.inr false) with out_d2 | b_d2
      · apply hDel0
        refine ⟨⟨gs_d2, out_d2⟩, ?_, by change gs_d2.length ≤ 11; omega, ?_⟩
        · intro g hg
          have h := hgs_d2_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_d2_ev out1 (by omega) y
          rw [hout_d2] at h; dsimp only [Sum.elim_inl] at h
          have hd := hD_ev (ext2 y)
          change (gs1.foldl stepW _).getD out1 false = F9 (ext2 y) at hd
          change (gs_d2.foldl stepW (List.ofFn y)).getD out_d2 false = F8d0 y
          rw [h, hd]; dsimp only [ext2]; rw [aut_pow_inv 4, hF9_ext0]
      · have h0 := hgs_d2_ev out1 (by omega) (fun _ => false)
        have h1 := hgs_d2_ev out1 (by omega) (fun _ => true)
        rw [hout_d2] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hD_ev (ext2 (fun _ => false))
        have hd1 := hD_ev (ext2 (fun _ => true))
        change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
        rw [hd0] at h0; rw [hd1] at h1
        dsimp only [ext2] at h0 h1
        rw [aut_pow_inv 4] at h0 h1
        have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
        exact hne (h0.symm.trans h1)
    -- Count dropped gates at y 0 = false (includes R0 ∪ R9) and y 2 = false (includes R2 ∪ R9)
    have h09_in_drop : ∀ j < gs1.length, ∀ g, gs1[j]? = some g → (0 ∈ g.inputs ∨ 9 ∈ g.inputs) → j ∈ drop_d0 := by
      intro j hj g hgj hm
      have h0c : env_d0.getD 0 (Sum.inr false) = Sum.inr false := hinit_d0_eq 0 (by omega)
      have h9c : env_d0.getD 9 (Sum.inr false) = Sum.inr false := hinit_d0_eq 9 (by omega)
      have hcl := hgs1_clean g (List.mem_of_getElem? hgj)
      apply hdrop_d0_c j hj g hgj
      rcases hm with h0m | h9m
      · rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, 0, h0m, by omega, false, h0c⟩
        · exact Or.inr ⟨Or.inr hop, 0, h0m, by omega, false, h0c⟩
        · refine Or.inl ⟨hop, 0, ?_, by omega, false, h0c⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 h0m; simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at h0m; subst h0m; rfl
      · rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, 9, h9m, by omega, false, h9c⟩
        · exact Or.inr ⟨Or.inr hop, 9, h9m, by omega, false, h9c⟩
        · refine Or.inl ⟨hop, 9, ?_, by omega, false, h9c⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 h9m; simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at h9m; subst h9m; rfl
    have h29_in_drop : ∀ j < gs1.length, ∀ g, gs1[j]? = some g → (2 ∈ g.inputs ∨ 9 ∈ g.inputs) → j ∈ drop_d2 := by
      intro j hj g hgj hm
      have h2c : env_d2.getD 2 (Sum.inr false) = Sum.inr false := by
        rw [hinit_d2_eq 2 (by omega)]
        dsimp only [init_d2]
        rw [getD_snoc_lt _ _ _ 2 (by simp)]
        have hlt2 : 2 < 9 := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2, ↓reduceDIte, Option.getD_some]
        change init_d0_base.getD (p2 2).val (Sum.inr false) = Sum.inr false
        rw [hp2_2]; rfl
      have h9c : env_d2.getD 9 (Sum.inr false) = Sum.inr false := by
        rw [hinit_d2_eq 9 (by omega)]
        dsimp only [init_d2]
        have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2 i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
        simpa using this
      have hcl := hgs1_clean g (List.mem_of_getElem? hgj)
      apply hdrop_d2_c j hj g hgj
      rcases hm with h2m | h9m
      · rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, 2, h2m, by omega, false, h2c⟩
        · exact Or.inr ⟨Or.inr hop, 2, h2m, by omega, false, h2c⟩
        · refine Or.inl ⟨hop, 2, ?_, by omega, false, h2c⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 h2m; simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at h2m; subst h2m; rfl
      · rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, 9, h9m, by omega, false, h9c⟩
        · exact Or.inr ⟨Or.inr hop, 9, h9m, by omega, false, h9c⟩
        · refine Or.inl ⟨hop, 9, ?_, by omega, false, h9c⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 h9m; simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at h9m; subst h9m; rfl
    -- Disjoint union count: (filter 0).length + (filter 9).length ≤ drop_d0.card ≤ 2!
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
        · simp [hsub]; omega
        · simp [hsub]; omega
        · exact False.elim (hg ⟨hp, hq⟩)
    have h09_sum : (gs1.filter (fun g => decide (0 ∈ g.inputs))).length +
        (gs1.filter (fun g => decide (9 ∈ g.inputs))).length ≤ drop_d0.card := by
      have hdisj : ∀ g ∈ gs1, ¬ (decide (0 ∈ g.inputs) = true ∧ decide (9 ∈ g.inputs) = true) := by
        intro g hg hpair
        have h0 := hpair.1
        have h9 := hpair.2
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact no_09 j hj gs1[j] (List.getElem?_eq_getElem hj) ⟨of_decide_eq_true h0, of_decide_eq_true h9⟩
      rw [filt_disj_sum gs1 _ _ hdisj]
      apply filter_le_card gs1 _ drop_d0
      intro j hj g hgj hor
      rcases Bool.or_eq_true_iff.mp hor with h0 | h9
      · exact h09_in_drop j hj g hgj (Or.inl (of_decide_eq_true h0))
      · exact h09_in_drop j hj g hgj (Or.inr (of_decide_eq_true h9))
    have h29_sum : (gs1.filter (fun g => decide (2 ∈ g.inputs))).length +
        (gs1.filter (fun g => decide (9 ∈ g.inputs))).length ≤ drop_d2.card := by
      have hdisj : ∀ g ∈ gs1, ¬ (decide (2 ∈ g.inputs) = true ∧ decide (9 ∈ g.inputs) = true) := by
        intro g hg hpair
        have h2 := hpair.1
        have h9 := hpair.2
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact no_29 j hj gs1[j] (List.getElem?_eq_getElem hj) ⟨of_decide_eq_true h2, of_decide_eq_true h9⟩
      rw [filt_disj_sum gs1 _ _ hdisj]
      apply filter_le_card gs1 _ drop_d2
      intro j hj g hgj hor
      rcases Bool.or_eq_true_iff.mp hor with h2 | h9
      · exact h29_in_drop j hj g hgj (Or.inl (of_decide_eq_true h2))
      · exact h29_in_drop j hj g hgj (Or.inr (of_decide_eq_true h9))
    have hdrop_d0_le2 : drop_d0.card ≤ 2 := by omega
    have hdrop_d2_le2 : drop_d2.card ≤ 2 := by omega
    have hgs1_eq14 : gs1.length = 14 := by omega
    have hr0_eq1 : (gs1.filter (fun g => decide (0 ∈ g.inputs))).length = 1 := by omega
    have hr2_eq1 : (gs1.filter (fun g => decide (2 ∈ g.inputs))).length = 1 := by omega
    have hr9_eq1 : (gs1.filter (fun g => decide (9 ∈ g.inputs))).length = 1 := by omega
    -- Extract unique gate h9 reading wire 9, and prove h9.op = GateOp.or!
    have hunique9 : ∃ h : Gate, h.op = GateOp.or ∧ gs1.filter (fun g => decide (9 ∈ g.inputs)) = [h] := by
      rcases hfl : gs1.filter (fun g => decide (9 ∈ g.inputs)) with _ | ⟨h, rest⟩
      · rw [hfl] at hr9_eq1; simp at hr9_eq1
      · rw [hfl] at hr9_eq1
        simp only [List.length_cons] at hr9_eq1
        have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        have hh_mem : h ∈ gs1 ∧ 9 ∈ h.inputs := by
          have hm : h ∈ gs1.filter (fun g => decide (9 ∈ g.inputs)) := by rw [hfl]; simp
          have hm' := List.mem_filter.mp hm
          exact ⟨hm'.1, of_decide_eq_true hm'.2⟩
        obtain ⟨pos, hpos_lt, hpos_eq⟩ := List.getElem_of_mem hh_mem.1
        have hpos_some : gs1[pos]? = some h := by rw [List.getElem?_eq_getElem hpos_lt, hpos_eq]
        -- Extract unique index p0 reading 0 and unique index p2 reading 2
        have hex_p0 : ∃ p0 < gs1.length, ∃ g0', gs1[p0]? = some g0' ∧ 0 ∈ g0'.inputs := by
          rcases hfl0 : gs1.filter (fun g => decide (0 ∈ g.inputs)) with _ | ⟨g0', _⟩
          · rw [hfl0] at hr0_eq1; simp at hr0_eq1
          · have hm : g0' ∈ gs1.filter (fun g => decide (0 ∈ g.inputs)) := by rw [hfl0]; simp
            have hm' := List.mem_filter.mp hm
            obtain ⟨p0, hp0_lt, hp0_eq⟩ := List.getElem_of_mem hm'.1
            exact ⟨p0, hp0_lt, g0', by rw [List.getElem?_eq_getElem hp0_lt, hp0_eq], of_decide_eq_true hm'.2⟩
        have hex_p2 : ∃ p2 < gs1.length, ∃ g2', gs1[p2]? = some g2' ∧ 2 ∈ g2'.inputs := by
          rcases hfl2 : gs1.filter (fun g => decide (2 ∈ g.inputs)) with _ | ⟨g2', _⟩
          · rw [hfl2] at hr2_eq1; simp at hr2_eq1
          · have hm : g2' ∈ gs1.filter (fun g => decide (2 ∈ g.inputs)) := by rw [hfl2]; simp
            have hm' := List.mem_filter.mp hm
            obtain ⟨p2, hp2_lt, hp2_eq⟩ := List.getElem_of_mem hm'.1
            exact ⟨p2, hp2_lt, g2', by rw [List.getElem?_eq_getElem hp2_lt, hp2_eq], of_decide_eq_true hm'.2⟩
        obtain ⟨pos0, hp0_lt, g0', hp0_some, hg0'_0⟩ := hex_p0
        obtain ⟨pos2, hp2_lt, g2', hp2_some, hg2'_2⟩ := hex_p2
        have hp0_ne_pos : pos0 ≠ pos := by
          intro heq; subst heq; rw [hpos_some] at hp0_some; injection hp0_some with he; subst he
          exact no_09 pos0 hp0_lt h hpos_some ⟨hg0'_0, hh_mem.2⟩
        have hp2_ne_pos : pos2 ≠ pos := by
          intro heq; subst heq; rw [hpos_some] at hp2_some; injection hp2_some with he; subst he
          exact no_29 pos2 hp2_lt h hpos_some ⟨hg2'_2, hh_mem.2⟩
        have hpos_d0 : pos ∈ drop_d0 := h09_in_drop pos hpos_lt h hpos_some (Or.inr hh_mem.2)
        have hp0_d0 : pos0 ∈ drop_d0 := h09_in_drop pos0 hp0_lt g0' hp0_some (Or.inl hg0'_0)
        have hpos_d2 : pos ∈ drop_d2 := h29_in_drop pos hpos_lt h hpos_some (Or.inr hh_mem.2)
        have hp2_d2 : pos2 ∈ drop_d2 := h29_in_drop pos2 hp2_lt g2' hp2_some (Or.inl hg2'_2)
        -- Helper: if env_d0[10+pos] = inr b0 and env_d2[10+pos] = inr b2, contradiction!
        have contra_const_pos : (∃ b0, env_d0.getD (10 + pos) (Sum.inr false) = Sum.inr b0) →
            (∃ b2, env_d2.getD (10 + pos) (Sum.inr false) = Sum.inr b2) → False := by
          intro hb0 hb2
          obtain ⟨b0, hbh0⟩ := hb0
          obtain ⟨b2, hbh2⟩ := hb2
          by_cases hread : ∃ j < gs1.length, ∃ g', gs1[j]? = some g' ∧ (10 + pos) ∈ g'.inputs
          · obtain ⟨j, hj_lt, g', hgj, hmem_j⟩ := hread
            have hj_gt : pos < j := by
              have hrb := hgs1_rb j hj_lt (10 + pos)
              have hget : gs1.getD j ⟨GateOp.or, []⟩ = g' := by simp only [List.getD_eq_getElem?_getD, hgj, Option.getD_some]
              rw [hget] at hrb; have := hrb hmem_j; omega
            have hj_d0 : j ∈ drop_d0 := by
              have hcl' := hgs1_clean g' (List.mem_of_getElem? hgj)
              apply hdrop_d0_c j hj_lt g' hgj
              rcases (hgs1_fan g' (List.mem_of_getElem? hgj)).1 with hop' | hop' | hop'
              · exact Or.inr ⟨Or.inl hop', 10 + pos, hmem_j, by omega, b0, hbh0⟩
              · exact Or.inr ⟨Or.inr hop', 10 + pos, hmem_j, by omega, b0, hbh0⟩
              · refine Or.inl ⟨hop', 10 + pos, ?_, by omega, b0, hbh0⟩
                have hl1 := hcl'.1 hop'
                rcases hins : g'.inputs with _ | ⟨a, rest'⟩
                · rw [hins] at hl1; simp at hl1
                · rw [hins] at hl1 hmem_j; simp only [List.length_cons] at hl1
                  have hnil' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
                  subst hnil'; simp only [List.mem_singleton] at hmem_j; subst hmem_j; rfl
            have hj_d2 : j ∈ drop_d2 := by
              have hcl' := hgs1_clean g' (List.mem_of_getElem? hgj)
              apply hdrop_d2_c j hj_lt g' hgj
              rcases (hgs1_fan g' (List.mem_of_getElem? hgj)).1 with hop' | hop' | hop'
              · exact Or.inr ⟨Or.inl hop', 10 + pos, hmem_j, by omega, b2, hbh2⟩
              · exact Or.inr ⟨Or.inr hop', 10 + pos, hmem_j, by omega, b2, hbh2⟩
              · refine Or.inl ⟨hop', 10 + pos, ?_, by omega, b2, hbh2⟩
                have hl1 := hcl'.1 hop'
                rcases hins : g'.inputs with _ | ⟨a, rest'⟩
                · rw [hins] at hl1; simp at hl1
                · rw [hins] at hl1 hmem_j; simp only [List.length_cons] at hl1
                  have hnil' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
                  subst hnil'; simp only [List.mem_singleton] at hmem_j; subst hmem_j; rfl
            -- Since drop_d0.card ≤ 2 and {pos, pos0} ⊆ drop_d0 with pos < j, j must equal pos0!
            have hj_eq_p0 : j = pos0 := by
              by_contra hne
              have hsub : ({pos, pos0, j} : Finset ℕ) ⊆ drop_d0 := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              have hc2 : ({pos0, j} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hne)
              have hnm : pos ∉ ({pos0, j} : Finset ℕ) := by simp [Ne.symm hp0_ne_pos, Nat.ne_of_lt hj_gt]
              have hc3 : ({pos, pos0, j} : Finset ℕ).card = 3 := by rw [Finset.card_insert_of_notMem hnm, hc2]
              have := Finset.card_le_card hsub; omega
            -- Similarly j must equal pos2!
            have hj_eq_p2 : j = pos2 := by
              by_contra hne
              have hsub : ({pos, pos2, j} : Finset ℕ) ⊆ drop_d2 := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              have hc2 : ({pos2, j} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hne)
              have hnm : pos ∉ ({pos2, j} : Finset ℕ) := by simp [Ne.symm hp2_ne_pos, Nat.ne_of_lt hj_gt]
              have hc3 : ({pos, pos2, j} : Finset ℕ).card = 3 := by rw [Finset.card_insert_of_notMem hnm, hc2]
              have := Finset.card_le_card hsub; omega
            -- So g' reads 0, 2, AND 10 + pos (3 distinct inputs in a list of length ≤ 2!)
            have h0_g' : 0 ∈ g'.inputs := by
              rw [hj_eq_p0] at hgj; rw [hp0_some] at hgj; injection hgj with he; rw [← he]; exact hg0'_0
            have h2_g' : 2 ∈ g'.inputs := by
              rw [hj_eq_p2] at hgj; rw [hp2_some] at hgj; injection hgj with he; rw [← he]; exact hg2'_2
            have hle2 := (hgs1_fan g' (List.mem_of_getElem? hgj)).2
            rcases list_le2 g'.inputs hle2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
            · rw [hins] at h0_g'; simp at h0_g'
            · rw [hins] at h0_g' h2_g'; simp only [List.mem_singleton] at h0_g' h2_g'; omega
            · rw [hins] at h0_g' h2_g' hmem_j
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h0_g' h2_g' hmem_j
              omega
          · -- No gate in gs1 reads 10 + pos, and out1 ≠ 10 + pos, so wire 9 is never used -> contradicts hNo14!
            push Not at hread
            have hout_ne_pos : out1 ≠ 10 + pos := by
              intro heq
              have h0 := hgs_d0_ev out1 (by omega) (fun _ => false)
              have h1 := hgs_d0_ev out1 (by omega) (fun _ => true)
              rw [heq, hbh0] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
              have hd0 := hD_ev (ext0 (fun _ => false))
              have hd1 := hD_ev (ext0 (fun _ => true))
              change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
              rw [heq] at hd0 hd1; rw [hd0] at h0; rw [hd1] at h1
              have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
              exact hne (h0.symm.trans h1)
            apply no_drop_wire9
            intro y
            have heq := wire_agree gs1 (List.ofFn y ++ [false]) (List.ofFn y ++ [y 0 && y 2])
              (fun i => i = 9 ∨ i = 10 + pos) (by simp)
              (by
                intro i hi hnb
                have hlt : i < 9 := by
                  have hne9 : i ≠ 9 := fun h => hnb (Or.inl h)
                  simp at hi; omega
                rw [getD_snoc_lt _ _ _ i (by simp; omega), getD_snoc_lt _ _ _ i (by simp; omega)])
              (by
                intro j hj g' hgj hnb i hi hibad
                rcases hibad with rfl | rfl
                · have hj_d0 : j ∈ drop_d0 := h09_in_drop j hj g' hgj (Or.inr hi)
                  have hj_ne_p0 : j ≠ pos0 := by
                    intro heq; subst heq; rw [hp0_some] at hgj; injection hgj with he; subst he
                    exact no_09 j hj g0' hp0_some ⟨hg0'_0, hi⟩
                  have hj_eq : j = pos := by
                    by_contra hne
                    have hsub : ({pos, pos0, j} : Finset ℕ) ⊆ drop_d0 := by
                      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with rfl | rfl | rfl <;> assumption
                    have hc2 : ({pos0, j} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hj_ne_p0)
                    have hnm : pos ∉ ({pos0, j} : Finset ℕ) := by simp [Ne.symm hp0_ne_pos, Ne.symm hne]
                    have hc3 : ({pos, pos0, j} : Finset ℕ).card = 3 := by rw [Finset.card_insert_of_notMem hnm, hc2]
                    have := Finset.card_le_card hsub; omega
                  apply hnb; right; simp [hj_eq]
                · exact hread j hj g' hgj hi)
              out1 (by rw [foldl_len]; simp; omega)
              (fun hb => by rcases hb with h1 | h2; exact hout1_ne9 h1; exact hout_ne_pos h2)
            exact heq.trans (hD_ev y)
        have h9c0 : env_d0.getD 9 (Sum.inr false) = Sum.inr false := hinit_d0_eq 9 (by omega)
        have h9c2 : env_d2.getD 9 (Sum.inr false) = Sum.inr false := by
          rw [hinit_d2_eq 9 (by omega)]; dsimp only [init_d2]
          have := getD_snoc_eq (List.ofFn (fun i : Fin 9 => init_d0_base.getD (p2 i).val (Sum.inr false))) (Sum.inr false) (Sum.inr false)
          simpa using this
        have hhop : h.op = GateOp.or := by
          rcases (hgs1_fan h hh_mem.1).1 with hand | hor | hnot
          · exact False.elim (contra_const_pos
              (hprop_d0_c pos hpos_lt h hpos_some (Or.inr ⟨hand, 9, hh_mem.2, by omega, h9c0⟩))
              (hprop_d2_c pos hpos_lt h hpos_some (Or.inr ⟨hand, 9, hh_mem.2, by omega, h9c2⟩)))
          · exact hor
          · have hl1 := (hgs1_clean h hh_mem.1).1 hnot
            have hhd9 : h.inputs.head? = some 9 := by
              have h9m := hh_mem.2
              rcases hins : h.inputs with _ | ⟨a, rest'⟩
              · rw [hins] at hl1; simp at hl1
              · rw [hins] at hl1 h9m; simp only [List.length_cons] at hl1
                have hnil' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst hnil'; simp only [List.mem_singleton] at h9m; subst h9m; rfl
            exact False.elim (contra_const_pos
              (hprop_d0_c pos hpos_lt h hpos_some (Or.inl ⟨hnot, 9, hhd9, by omega, false, h9c0⟩))
              (hprop_d2_c pos hpos_lt h hpos_some (Or.inl ⟨hnot, 9, hhd9, by omega, false, h9c2⟩)))
        exact ⟨h, hhop, hfl⟩
    -- Step 3: Bound fan-out of {4, 6, 7} (≤ 2) and {1, 3, 5, 8} (≤ 3) via gs_full = AND[0,2] :: gs1
    let gs_full : List Gate := ⟨GateOp.and, [0, 2]⟩ :: gs1
    have hfull_len : gs_full.length = 15 := by simp [gs_full, hgs1_eq14]
    have hfull_fan : ∀ g ∈ gs_full, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hmem
      · exact ⟨Or.inl rfl, le_refl 2⟩
      · exact hgs1_fan g hmem
    have hfull_clean : ∀ g ∈ gs_full, (g.op = GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup) := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hmem
      · exact ⟨fun h => GateOp.noConfusion h, fun _ => ⟨rfl, by decide⟩⟩
      · exact hgs1_clean g hmem
    have hfull_ev : ∀ y : Fin 9 → Bool, (gs_full.foldl stepW (List.ofFn y)).getD out1 false = F9 y := by
      intro y
      dsimp only [gs_full]; rw [List.foldl_cons]
      have hs0 : stepW (List.ofFn y) ⟨GateOp.and, [0, 2]⟩ = List.ofFn y ++ [y 0 && y 2] := by
        change List.ofFn y ++ [GateOp.and.eval _] = _
        rw [eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have h0 : (List.ofFn y).getD 0 false = y 0 := by simp [List.getD_eq_getElem?_getD]
        have h2 : (List.ofFn y).getD 2 false = y 2 := by simp [List.getD_eq_getElem?_getD]
        rw [h0, h2]
      rw [hs0]; exact hD_ev y
    have deg_bound_del4 : ∀ (v : Fin 9) (k : ℕ), v.val ≠ 0 → v.val ≠ 2 → aut^[k] v = 4 →
        (gs1.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ 2 := by
      intro v k hv0 hv2 hpk
      let p : Fin 9 → Fin 9 := aut^[k]
      let map4 : Fin 9 → ℕ ⊕ Bool := fun i => init_d4_base.getD (p i).val (Sum.inr false)
      have hmap4_eval : ∀ (i : Fin 9) (y : Fin 8 → Bool),
          Sum.elim (fun w => (List.ofFn y).getD w false) id (map4 i) = ext4 y (p i) := by
        intro i y
        have hchk : ∀ j : Fin 9,
            Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d4_base.getD j.val (Sum.inr false)) = ext4 y j := by
          intro j; fin_cases j <;> simp [init_d4_base, ext4]
        exact hchk (p i)
      have hmap4_bd : ∀ (i : Fin 9) (w : ℕ), map4 i = Sum.inl w → w < 8 := by
        intro i w hw
        have hchk : ∀ j : Fin 9, ∀ u, init_d4_base.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
          intro j u hu; fin_cases j <;> simp [init_d4_base] at hu <;> omega
        exact hchk (p i) w hw
      let init_v : List (ℕ ⊕ Bool) := List.ofFn map4
      obtain ⟨gs_v, env_v, drop_v, henv_v_len, hinit_v_eq, _, hsz_v, hdrop_v_c, _,
        hgs_v_fan, _, _, _, hgs_v_ev⟩ :=
        simplify 8 9 8 (fun y => List.ofFn (ext4 y ∘ p)) (fun y => List.ofFn y)
          init_v gs_full (by intro y; simp) (by intro y; simp) (by simp [init_v]) hfull_fan
          (by
            intro i hi y
            have hi1 : init_v.getD i (Sum.inr false) = map4 ⟨i, hi⟩ := by
              simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
            have hi2 : (List.ofFn (ext4 y ∘ p)).getD i false = ext4 y (p ⟨i, hi⟩) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, Function.comp_def]
            rw [hi1, hi2]; exact hmap4_eval ⟨i, hi⟩ y)
          (by
            intro i hi w hw
            simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] at hw
            exact hmap4_bd ⟨i, hi⟩ w hw)
      have hgs_v_ge13 : 13 ≤ gs_v.length := by
        by_contra hle12
        rcases hout_v : env_v.getD out1 (Sum.inr false) with out_v | b_v
        · apply hDel4
          refine ⟨⟨gs_v, out_v⟩, ?_, by change gs_v.length ≤ 12; omega, ?_⟩
          · intro g hg
            have h := hgs_v_fan g hg
            exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
          · intro y
            have h := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) y
            rw [hout_v] at h; dsimp only [Sum.elim_inl] at h
            change (gs_v.foldl stepW (List.ofFn y)).getD out_v false = F8d4 y
            rw [h, hfull_ev (ext4 y ∘ p), aut_pow_inv k, hF9_ext4]
        · have h0 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => false)
          have h1 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => true)
          rw [hout_v] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
          rw [hfull_ev, aut_pow_inv k] at h0; rw [hfull_ev, aut_pow_inv k] at h1
          have hne : F9 (ext4 (fun _ => false)) ≠ F9 (ext4 (fun _ => true)) := by decide
          exact hne (h0.symm.trans h1)
      have hvc : env_v.getD v.val (Sum.inr false) = Sum.inr false := by
        rw [hinit_v_eq v.val v.isLt]
        simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        dsimp only [map4, p]; rw [hpk]; rfl
      have hv_drop : ∀ j < gs_full.length, ∀ g, gs_full[j]? = some g → decide (v.val ∈ g.inputs) = true → j ∈ drop_v := by
        intro j hj g hgj hvm
        have hvm' : v.val ∈ g.inputs := of_decide_eq_true hvm
        have hcl := hfull_clean g (List.mem_of_getElem? hgj)
        apply hdrop_v_c j hj g hgj
        rcases (hfull_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, v.val, hvm', by omega, false, hvc⟩
        · exact Or.inr ⟨Or.inr hop, v.val, hvm', by omega, false, hvc⟩
        · refine Or.inl ⟨hop, v.val, ?_, by omega, false, hvc⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 hvm'; simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at hvm'; subst hvm'; rfl
      have hle_drop := filter_le_card gs_full (fun g => decide (v.val ∈ g.inputs)) drop_v hv_drop
      have hfilt_eq : gs_full.filter (fun g => decide (v.val ∈ g.inputs)) =
          gs1.filter (fun g => decide (v.val ∈ g.inputs)) := by
        dsimp only [gs_full]; rw [List.filter_cons]
        have hnot02 : decide (v.val ∈ ([0, 2] : List ℕ)) = false := by simp [hv0, hv2]
        simp only [hnot02, Bool.false_eq_true, ↓reduceIte]
      rw [hfilt_eq] at hle_drop; omega
    have deg_bound_del0 : ∀ (v : Fin 9) (k : ℕ), v.val ≠ 0 → v.val ≠ 2 → aut^[k] v = 0 →
        (gs1.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ 3 := by
      intro v k hv0 hv2 hpk
      let p : Fin 9 → Fin 9 := aut^[k]
      let map0 : Fin 9 → ℕ ⊕ Bool := fun i => init_d0_base.getD (p i).val (Sum.inr false)
      have hmap0_eval : ∀ (i : Fin 9) (y : Fin 8 → Bool),
          Sum.elim (fun w => (List.ofFn y).getD w false) id (map0 i) = ext0 y (p i) := by
        intro i y
        have hchk : ∀ j : Fin 9,
            Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d0_base.getD j.val (Sum.inr false)) = ext0 y j := by
          intro j; fin_cases j <;> simp [init_d0_base, ext0]
        exact hchk (p i)
      have hmap0_bd : ∀ (i : Fin 9) (w : ℕ), map0 i = Sum.inl w → w < 8 := by
        intro i w hw
        have hchk : ∀ j : Fin 9, ∀ u, init_d0_base.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
          intro j u hu; fin_cases j <;> simp [init_d0_base] at hu <;> omega
        exact hchk (p i) w hw
      let init_v : List (ℕ ⊕ Bool) := List.ofFn map0
      obtain ⟨gs_v, env_v, drop_v, henv_v_len, hinit_v_eq, _, hsz_v, hdrop_v_c, _,
        hgs_v_fan, _, _, _, hgs_v_ev⟩ :=
        simplify 8 9 8 (fun y => List.ofFn (ext0 y ∘ p)) (fun y => List.ofFn y)
          init_v gs_full (by intro y; simp) (by intro y; simp) (by simp [init_v]) hfull_fan
          (by
            intro i hi y
            have hi1 : init_v.getD i (Sum.inr false) = map0 ⟨i, hi⟩ := by
              simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
            have hi2 : (List.ofFn (ext0 y ∘ p)).getD i false = ext0 y (p ⟨i, hi⟩) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, Function.comp_def]
            rw [hi1, hi2]; exact hmap0_eval ⟨i, hi⟩ y)
          (by
            intro i hi w hw
            simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] at hw
            exact hmap0_bd ⟨i, hi⟩ w hw)
      have hgs_v_ge12 : 12 ≤ gs_v.length := by
        by_contra hle11
        rcases hout_v : env_v.getD out1 (Sum.inr false) with out_v | b_v
        · apply hDel0
          refine ⟨⟨gs_v, out_v⟩, ?_, by change gs_v.length ≤ 11; omega, ?_⟩
          · intro g hg
            have h := hgs_v_fan g hg
            exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
          · intro y
            have h := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) y
            rw [hout_v] at h; dsimp only [Sum.elim_inl] at h
            change (gs_v.foldl stepW (List.ofFn y)).getD out_v false = F8d0 y
            rw [h, hfull_ev (ext0 y ∘ p), aut_pow_inv k, hF9_ext0]
        · have h0 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => false)
          have h1 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => true)
          rw [hout_v] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
          rw [hfull_ev, aut_pow_inv k] at h0; rw [hfull_ev, aut_pow_inv k] at h1
          have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
          exact hne (h0.symm.trans h1)
      have hvc : env_v.getD v.val (Sum.inr false) = Sum.inr false := by
        rw [hinit_v_eq v.val v.isLt]
        simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        dsimp only [map0, p]; rw [hpk]; rfl
      have hv_drop : ∀ j < gs_full.length, ∀ g, gs_full[j]? = some g → decide (v.val ∈ g.inputs) = true → j ∈ drop_v := by
        intro j hj g hgj hvm
        have hvm' : v.val ∈ g.inputs := of_decide_eq_true hvm
        have hcl := hfull_clean g (List.mem_of_getElem? hgj)
        apply hdrop_v_c j hj g hgj
        rcases (hfull_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, v.val, hvm', by omega, false, hvc⟩
        · exact Or.inr ⟨Or.inr hop, v.val, hvm', by omega, false, hvc⟩
        · refine Or.inl ⟨hop, v.val, ?_, by omega, false, hvc⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 hvm'; simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at hvm'; subst hvm'; rfl
      have hle_drop := filter_le_card gs_full (fun g => decide (v.val ∈ g.inputs)) drop_v hv_drop
      have hfilt_eq : gs_full.filter (fun g => decide (v.val ∈ g.inputs)) =
          gs1.filter (fun g => decide (v.val ∈ g.inputs)) := by
        dsimp only [gs_full]; rw [List.filter_cons]
        have hnot02 : decide (v.val ∈ ([0, 2] : List ℕ)) = false := by simp [hv0, hv2]
        simp only [hnot02, Bool.false_eq_true, ↓reduceIte]
      rw [hfilt_eq] at hle_drop; omega
    have hr4_le2 : (gs1.filter (fun g => decide (4 ∈ g.inputs))).length ≤ 2 :=
      deg_bound_del4 4 0 (by decide) (by decide) (by decide)
    have hr6_le2 : (gs1.filter (fun g => decide (6 ∈ g.inputs))).length ≤ 2 :=
      deg_bound_del4 6 2 (by decide) (by decide) (by decide)
    have hr7_le2 : (gs1.filter (fun g => decide (7 ∈ g.inputs))).length ≤ 2 :=
      deg_bound_del4 7 1 (by decide) (by decide) (by decide)
    have hr02_eq1 : ∀ i ∈ ([0, 2] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length = 1 := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hr0_eq1
      · exact hr2_eq1
    have hr467_le2 : ∀ i ∈ ([4, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2 := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact hr4_le2
      · exact hr6_le2
      · exact hr7_le2
    have hr_all_le3 : ∀ i : Fin 9, (D.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3 := by
      intro i
      fin_cases i
      · exact hr0_eq1.le.trans (by omega)
      · exact deg_bound_del0 1 5 (by decide) (by decide) (by decide)
      · exact hr2_eq1.le.trans (by omega)
      · exact deg_bound_del0 3 3 (by decide) (by decide) (by decide)
      · exact hr4_le2.trans (by omega)
      · exact deg_bound_del0 5 1 (by decide) (by decide) (by decide)
      · exact hr6_le2.trans (by omega)
      · exact hr7_le2.trans (by omega)
      · exact deg_bound_del0 8 2 (by decide) (by decide) (by decide)
    have hD_fan : FanInTwo D := by
      intro g hg
      have h := hgs1_fan g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
    exact hSuff14 D hD_fan hgs1_rb hgs1_clean hgs1_eq14 hunique9 hr02_eq1 hr467_le2 hr_all_le3 hD_ev
  · have h0 := hgs1_ev out0 hout0_lt (fun _ => false)
    have h1 := hgs1_ev out0 hout0_lt (fun _ => true)
    rw [hout1] at h0 h1; dsimp only [Sum.elim_inr, id_eq] at h0 h1
    rw [hgs0_ev] at h0 h1
    have hne : F9 (fun _ => false) ≠ F9 (fun _ => true) := by decide
    exact hne (h0.symm.trans h1)
