import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2590_619
    (hEdgeOr :
      let G : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D → D.size ≤ 19 →
        D.output = 10 + (D.size - 1) →
        (∀ j < D.size, PEqualNP.TopForm.opnd D j 0 ≠ PEqualNP.TopForm.opnd D j 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        PEqualNP.TopForm.opnd D 0 0 = 0 → PEqualNP.TopForm.opnd D 0 1 = 1 → False)
    (hNonEdgeOr :
      let G : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D → D.size ≤ 19 →
        D.output = 10 + (D.size - 1) →
        (∀ j < D.size, PEqualNP.TopForm.opnd D j 0 ≠ PEqualNP.TopForm.opnd D j 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        PEqualNP.TopForm.opnd D 0 0 = 0 → PEqualNP.TopForm.opnd D 0 1 = 2 → False)
    (hEdgeAnd :
      let G : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D → D.size ≤ 19 →
        D.output = 10 + (D.size - 1) →
        (∀ j < D.size, PEqualNP.TopForm.opnd D j 0 ≠ PEqualNP.TopForm.opnd D j 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.TopForm.opnd D 0 0 = 0 → PEqualNP.TopForm.opnd D 0 1 = 1 → False)
    (hNonEdgeAnd :
      let G : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D → D.size ≤ 19 →
        D.output = 10 + (D.size - 1) →
        (∀ j < D.size, PEqualNP.TopForm.opnd D j 0 ≠ PEqualNP.TopForm.opnd D j 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.TopForm.opnd D 0 0 = 0 → PEqualNP.TopForm.opnd D 0 1 = 2 → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  classical
  intro C0 hMono0 hSz0 hComp0
  let G : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  let F : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have hGraphEq : ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = F x := by
    dsimp only [G, F]; decide +kernel
  have hF_true : F (fun _ => true) = true := by decide
  have hF_false : F (fun _ => false) = false := by decide
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    change (gs ++ [g]).foldl _ x = _
    rw [List.foldl_append]; rfl
  have hrun_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [hrun_snoc]; simp [ih]; omega
  have hgetD_lt : ∀ {α : Type} (l : List α) (b d : α) (t : ℕ), t < l.length →
      (l ++ [b]).getD t d = l.getD t d := by
    intro α l b d t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have hgetD_at : ∀ {α : Type} (l : List α) (b d : α), (l ++ [b]).getD l.length d = b := by
    intro α l b d; simp [List.getD_eq_getElem?_getD]
  have hrun_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, hrun_snoc, hgetD_lt _ _ _ _ (by rw [hrun_len, List.length_append]; omega), ih]
  have hrun_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := hrun_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1; exact h1
  have hrun_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false =
        (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map fun i =>
            if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; exfalso; exact Nat.not_lt_zero j hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (run gs x).length = x.length + gs.length := hrun_len gs x
      have hsame : ∀ k ≤ gs.length, ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
          l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact hrun_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · have hgd : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
        rw [hgd, hsame j (Nat.le_of_lt hlt), hrun_prefix gs [g] x _ (by omega)]
        exact ih j hlt
      · have hjeq : j = gs.length := by rw [List.length_append, List.length_singleton] at hj; omega
        subst hjeq
        have hgd : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hgd, hsame gs.length le_rfl, hrun_snoc, ← hlen, hgetD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hwires_in : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 10 → Bool) (w : ℕ) (hw : w < 10),
      (D.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro D x w hw
    change (run D.gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [hrun_input D.gates (List.ofFn x) w (by simp [hw])]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hw]
    rfl
  let valOf : List Bool → Sum Bool ℕ → Bool := fun w v =>
    Sum.rec (fun b => b) (fun idx => w.getD idx false) v
  have hNormalize : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 10 D ∧ D.size ≤ C.size ∧
        PEqualNP.MetaComplexity.circuitFun 10 D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        (∀ j < D.size, PEqualNP.TopForm.opnd D j 0 ≠ PEqualNP.TopForm.opnd D j 1) := by
    intro C hMono hCeq
    have hPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        ∃ (ds : List PEqualNP.CircuitLowerBounds.Gate) (env : List (Sum Bool ℕ)),
          ds.length ≤ gs.length ∧
          env.length = 10 + gs.length ∧
          (∀ g ∈ ds, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
          (∀ j < ds.length, ∀ i ∈ (ds.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < 10 + j) ∧
          (∀ j < ds.length,
            (ds.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 0 0 ≠
            (ds.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 1 0) ∧
          (∀ v ∈ env, ∀ idx, v = Sum.inr idx → idx < 10 + ds.length) ∧
          (∀ (x : Fin 10 → Bool) (k : ℕ), valOf (run ds (List.ofFn x)) (env.getD k (Sum.inl false)) = (run gs (List.ofFn x)).getD k false) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _
        refine ⟨[], List.ofFn (fun i : Fin 10 => Sum.inr i.val), le_rfl, by simp,
          by simp, by intro j hj; exfalso; exact Nat.not_lt_zero j hj,
          by intro j hj; exfalso; exact Nat.not_lt_zero j hj, ?_, ?_⟩
        · intro v hv idx hveq
          rw [List.mem_ofFn] at hv
          rcases hv with ⟨i, hi⟩
          rw [← hi] at hveq
          cases hveq
          exact i.isLt
        · intro x k
          by_cases hk : k < 10
          · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hk]
            change (List.ofFn x).getD k false = (List.ofFn x).getD k false
            rfl
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [run]; omega)]
      | append_singleton gs g ih =>
        intro hgs
        have hgs' : ∀ g' ∈ gs, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hgs g' (List.mem_append_left _ hg')
        obtain ⟨hop_mem, hglen⟩ := hgs g (List.mem_append_right _ (List.mem_singleton_self g))
        obtain ⟨ds, env, hds_le, henv_len, hds_ao, hds_rb, hds_ne, henv_lt, hval⟩ := ih hgs'
        have hval_at : ∀ (x : Fin 10 → Bool) (i : ℕ),
            valOf (run ds (List.ofFn x)) (env.getD i (Sum.inl false)) = (run gs (List.ofFn x)).getD i false :=
          fun x i => hval x i
        have hlookup_lt : ∀ (i idx : ℕ), env.getD i (Sum.inl false) = Sum.inr idx → idx < 10 + ds.length := by
          intro i idx hi
          by_cases hlt : i < env.length
          · rw [List.getD_eq_getElem _ _ hlt] at hi
            exact henv_lt _ (List.getElem_mem hlt) idx hi
          · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)] at hi
            cases hi
        have hNoGate : ∀ (v : Sum Bool ℕ),
            (∀ idx, v = Sum.inr idx → idx < 10 + ds.length) →
            (∀ x : Fin 10 → Bool, valOf (run ds (List.ofFn x)) v = g.op.eval (g.inputs.map fun i => (run gs (List.ofFn x)).getD i false)) →
            ∃ (ds' : List PEqualNP.CircuitLowerBounds.Gate) (env' : List (Sum Bool ℕ)),
              ds'.length ≤ (gs ++ [g]).length ∧ env'.length = 10 + (gs ++ [g]).length ∧
              (∀ g' ∈ ds', (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g'.inputs.length = 2) ∧
              (∀ j < ds'.length, ∀ i ∈ (ds'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < 10 + j) ∧
              (∀ j < ds'.length,
                (ds'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 0 0 ≠
                (ds'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 1 0) ∧
              (∀ u ∈ env', ∀ idx, u = Sum.inr idx → idx < 10 + ds'.length) ∧
              (∀ (x : Fin 10 → Bool) (k : ℕ), valOf (run ds' (List.ofFn x)) (env'.getD k (Sum.inl false)) = (run (gs ++ [g]) (List.ofFn x)).getD k false) := by
          intro v hvlt hvev
          refine ⟨ds, env ++ [v], by simp; omega, by simp [henv_len]; omega, hds_ao, hds_rb, hds_ne, ?_, ?_⟩
          · intro u hu idx hueq
            rw [List.mem_append, List.mem_singleton] at hu
            rcases hu with hu | rfl
            · exact henv_lt u hu idx hueq
            · exact hvlt idx hueq
          · intro x k
            have hrun_l : (run gs (List.ofFn x)).length = 10 + gs.length := by rw [hrun_len, List.length_ofFn]
            rcases Nat.lt_trichotomy k (10 + gs.length) with hlt | rfl | hgt
            · rw [hgetD_lt _ _ _ _ (by omega), hrun_snoc, hgetD_lt _ _ _ _ (by omega)]
              exact hval x k
            · rw [← henv_len, hgetD_at, hrun_snoc, henv_len, ← hrun_l, hgetD_at]
              exact hvev x
            · rw [List.getD_eq_default _ _ (by simp [henv_len]; omega),
                  List.getD_eq_default _ _ (by rw [hrun_len, List.length_ofFn, List.length_append, List.length_singleton]; omega)]
        have hEmitGate : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (a b : ℕ),
            (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
            a < 10 + ds.length → b < 10 + ds.length → a ≠ b →
            (∀ x : Fin 10 → Bool,
              op.eval [(run ds (List.ofFn x)).getD a false, (run ds (List.ofFn x)).getD b false] =
              g.op.eval (g.inputs.map fun i => (run gs (List.ofFn x)).getD i false)) →
            ∃ (ds' : List PEqualNP.CircuitLowerBounds.Gate) (env' : List (Sum Bool ℕ)),
              ds'.length ≤ (gs ++ [g]).length ∧ env'.length = 10 + (gs ++ [g]).length ∧
              (∀ g' ∈ ds', (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g'.inputs.length = 2) ∧
              (∀ j < ds'.length, ∀ i ∈ (ds'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < 10 + j) ∧
              (∀ j < ds'.length,
                (ds'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 0 0 ≠
                (ds'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 1 0) ∧
              (∀ u ∈ env', ∀ idx, u = Sum.inr idx → idx < 10 + ds'.length) ∧
              (∀ (x : Fin 10 → Bool) (k : ℕ), valOf (run ds' (List.ofFn x)) (env'.getD k (Sum.inl false)) = (run (gs ++ [g]) (List.ofFn x)).getD k false) := by
          intro op a b hop ha hb hab hev
          let ng : PEqualNP.CircuitLowerBounds.Gate := ⟨op, [a, b]⟩
          refine ⟨ds ++ [ng], env ++ [Sum.inr (10 + ds.length)], by simp; omega, by simp [henv_len]; omega, ?_, ?_, ?_, ?_, ?_⟩
          · intro g' hg'
            rw [List.mem_append, List.mem_singleton] at hg'
            rcases hg' with hg' | rfl
            · exact hds_ao g' hg'
            · exact ⟨hop, rfl⟩
          · intro j hj i hi
            rcases Nat.lt_or_ge j ds.length with hlt | hge
            · rw [hgetD_lt _ _ _ _ hlt] at hi
              exact hds_rb j hlt i hi
            · have hjeq : j = ds.length := by rw [List.length_append, List.length_singleton] at hj; omega
              subst hjeq
              rw [hgetD_at] at hi
              simp only [ng, List.mem_cons, List.mem_nil_iff, or_false] at hi
              rcases hi with rfl | rfl <;> assumption
          · intro j hj
            rcases Nat.lt_or_ge j ds.length with hlt | hge
            · rw [hgetD_lt _ _ _ _ hlt]
              exact hds_ne j hlt
            · have hjeq : j = ds.length := by rw [List.length_append, List.length_singleton] at hj; omega
              subst hjeq
              rw [hgetD_at]
              exact hab
          · intro u hu idx hueq
            rw [List.mem_append, List.mem_singleton] at hu
            rcases hu with hu | rfl
            · have := henv_lt u hu idx hueq; simp; omega
            · cases hueq; rw [List.length_append, List.length_singleton]; omega
          · intro x k
            have hrun_l : (run gs (List.ofFn x)).length = 10 + gs.length := by rw [hrun_len, List.length_ofFn]
            have hrun_d : (run ds (List.ofFn x)).length = 10 + ds.length := by rw [hrun_len, List.length_ofFn]
            rcases Nat.lt_trichotomy k (10 + gs.length) with hlt | rfl | hgt
            · rw [hgetD_lt env _ _ k (by omega), hrun_snoc gs g, hgetD_lt (run gs (List.ofFn x)) _ _ k (by omega)]
              cases hv : env.getD k (Sum.inl false) with
              | inl b0 =>
                have h1 := hval x k; rw [hv] at h1; exact h1
              | inr idx =>
                have hidx := hlookup_lt k idx hv
                have h1 := hval x k; rw [hv] at h1
                change (run (ds ++ [ng]) (List.ofFn x)).getD idx false = _
                rw [hrun_snoc ds ng, hgetD_lt (run ds (List.ofFn x)) _ _ idx (by omega)]
                exact h1
            · rw [← henv_len, hgetD_at env, hrun_snoc gs g, henv_len, ← hrun_l, hgetD_at (run gs (List.ofFn x))]
              change (run (ds ++ [ng]) (List.ofFn x)).getD (10 + ds.length) false = _
              rw [hrun_snoc ds ng, ← hrun_d, hgetD_at (run ds (List.ofFn x))]
              exact hev x
            · rw [List.getD_eq_default _ _ (by simp [henv_len]; omega),
                  List.getD_eq_default _ _ (by rw [hrun_len, List.length_ofFn, List.length_append, List.length_singleton]; omega)]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop_mem
        rcases hop_mem with hop | hop
        · rcases hgi : g.inputs with _ | ⟨i0, _ | ⟨i1, _ | ⟨i2, rest⟩⟩⟩
          · exact hNoGate (Sum.inl true) (fun _ h => by cases h) (fun x => by rw [hop, hgi, andEval]; rfl)
          · exact hNoGate (env.getD i0 (Sum.inl false)) (hlookup_lt i0) (fun x => by
              rw [hop, hgi, andEval]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              exact hval_at x i0)
          · cases hu : env.getD i0 (Sum.inl false) with
            | inl b0 =>
              cases b0
              · exact hNoGate (Sum.inl false) (fun _ h => by cases h) (fun x => by
                  have h0 := hval_at x i0; rw [hu] at h0
                  rw [hop, hgi, andEval]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ← h0, valOf, Bool.false_and])
              · exact hNoGate (env.getD i1 (Sum.inl false)) (hlookup_lt i1) (fun x => by
                  have h0 := hval_at x i0; rw [hu] at h0
                  rw [hop, hgi, andEval]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ← h0, valOf, Bool.true_and, Bool.and_true]
                  exact hval_at x i1)
            | inr a =>
              cases hv : env.getD i1 (Sum.inl false) with
              | inl b1 =>
                cases b1
                · exact hNoGate (Sum.inl false) (fun _ h => by cases h) (fun x => by
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, andEval]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ← h1, valOf, Bool.and_false, Bool.false_and])
                · exact hNoGate (Sum.inr a) (fun _ h => by cases h; exact hlookup_lt i0 a hu) (fun x => by
                    have h0 := hval_at x i0; rw [hu] at h0
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, andEval]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ← h0, ← h1, valOf, Bool.and_true])
              | inr b =>
                by_cases hab : a = b
                · subst hab
                  exact hNoGate (Sum.inr a) (fun _ h => by cases h; exact hlookup_lt i0 a hu) (fun x => by
                    have h0 := hval_at x i0; rw [hu] at h0
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, andEval]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ← h0, ← h1, valOf, Bool.and_true, Bool.and_self])
                · exact hEmitGate PEqualNP.CircuitLowerBounds.GateOp.and a b (Or.inl rfl)
                    (hlookup_lt i0 a hu) (hlookup_lt i1 b hv) hab (fun x => by
                    have h0 := hval_at x i0; rw [hu] at h0
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, andEval, andEval]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ← h0, ← h1, valOf, Bool.and_true])
          · rw [hgi] at hglen; simp at hglen
        · rcases hgi : g.inputs with _ | ⟨i0, _ | ⟨i1, _ | ⟨i2, rest⟩⟩⟩
          · exact hNoGate (Sum.inl false) (fun _ h => by cases h) (fun x => by rw [hop, hgi, orEval]; rfl)
          · exact hNoGate (env.getD i0 (Sum.inl false)) (hlookup_lt i0) (fun x => by
              rw [hop, hgi, orEval]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              exact hval_at x i0)
          · cases hu : env.getD i0 (Sum.inl false) with
            | inl b0 =>
              cases b0
              · exact hNoGate (env.getD i1 (Sum.inl false)) (hlookup_lt i1) (fun x => by
                  have h0 := hval_at x i0; rw [hu] at h0
                  rw [hop, hgi, orEval]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ← h0, valOf, Bool.false_or, Bool.or_false]
                  exact hval_at x i1)
              · exact hNoGate (Sum.inl true) (fun _ h => by cases h) (fun x => by
                  have h0 := hval_at x i0; rw [hu] at h0
                  rw [hop, hgi, orEval]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ← h0, valOf, Bool.true_or])
            | inr a =>
              cases hv : env.getD i1 (Sum.inl false) with
              | inl b1 =>
                cases b1
                · exact hNoGate (Sum.inr a) (fun _ h => by cases h; exact hlookup_lt i0 a hu) (fun x => by
                    have h0 := hval_at x i0; rw [hu] at h0
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, orEval]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ← h0, ← h1, valOf, Bool.or_false])
                · exact hNoGate (Sum.inl true) (fun _ h => by cases h) (fun x => by
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, orEval]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ← h1, valOf, Bool.or_true, Bool.true_or])
              | inr b =>
                by_cases hab : a = b
                · subst hab
                  exact hNoGate (Sum.inr a) (fun _ h => by cases h; exact hlookup_lt i0 a hu) (fun x => by
                    have h0 := hval_at x i0; rw [hu] at h0
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, orEval]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ← h0, ← h1, valOf, Bool.or_false, Bool.or_self])
                · exact hEmitGate PEqualNP.CircuitLowerBounds.GateOp.or a b (Or.inr rfl)
                    (hlookup_lt i0 a hu) (hlookup_lt i1 b hv) hab (fun x => by
                    have h0 := hval_at x i0; rw [hu] at h0
                    have h1 := hval_at x i1; rw [hv] at h1
                    rw [hop, hgi, orEval, orEval]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ← h0, ← h1, valOf, Bool.or_false])
          · rw [hgi] at hglen; simp at hglen
    obtain ⟨ds, env, hds_le, _, hds_ao, hds_rb, hds_ne, _, hval⟩ := hPref C.gates hMono
    cases hout : env.getD C.output (Sum.inl false) with
    | inl b =>
      cases b
      · have h1 := hval (fun _ => true) C.output
        rw [hout] at h1
        have h2 := hCeq (fun _ => true)
        rw [hGraphEq, hF_true] at h2
        change false = C.eval (List.ofFn (fun _ => true)) at h1
        rw [h2] at h1; cases h1
      · have h1 := hval (fun _ => false) C.output
        rw [hout] at h1
        have h2 := hCeq (fun _ => false)
        rw [hGraphEq, hF_false] at h2
        change true = C.eval (List.ofFn (fun _ => false)) at h1
        rw [h2] at h1; cases h1
    | inr out =>
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨ds, out⟩
      refine ⟨D, ⟨fun g hg => (hds_ao g hg).1, hds_rb, fun g hg => (hds_ao g hg).2⟩, hds_le, ?_, hds_ne⟩
      funext x
      have h1 := hval x C.output
      rw [hout] at h1
      exact h1.trans (hCeq x)
  have hEx0 : ∃ m : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 10 D ∧
      PEqualNP.MetaComplexity.circuitFun 10 D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size = m := by
    obtain ⟨D, hDao, _, hDfun, _⟩ := hNormalize C0 hMono0 (fun x => (hComp0 x).trans (hGraphEq x).symm)
    exact ⟨D.size, D, hDao, hDfun, rfl⟩
  let mMin := Nat.find hEx0
  obtain ⟨D1, hD1ao, hD1fun, hD1sz⟩ := Nat.find_spec hEx0
  have hMinLe19 : mMin ≤ 19 := by
    obtain ⟨D, hDao, hDle, hDfun, _⟩ := hNormalize C0 hMono0 (fun x => (hComp0 x).trans (hGraphEq x).symm)
    exact (Nat.find_min' hEx0 ⟨D, hDao, hDfun, rfl⟩).trans (hDle.trans hSz0)
  have hD1mono : PEqualNP.MetaComplexity.Monotone2 D1 := by
    intro g hg
    refine ⟨?_, by rw [hD1ao.2.2 g hg]⟩
    rcases hD1ao.1 g hg with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))
  obtain ⟨D2, hD2ao, hD2le, hD2fun, hD2dist⟩ := hNormalize D1 hD1mono (fun x => congrFun hD1fun x)
  have hD2least : PEqualNP.TopForm.IsLeastAO G D2 := by
    refine ⟨hD2ao, hD2fun, fun C' hC'ao hC'fun => ?_⟩
    have hm : mMin ≤ C'.size := Nat.find_min' hEx0 ⟨C', hC'ao, hC'fun, rfl⟩
    omega
  have hD2sz : D2.size ≤ 19 := by omega
  have hD2outLt : D2.output < 10 + D2.size := by
    by_contra hge
    have hlen : (run D2.gates (List.ofFn (fun _ : Fin 10 => true))).length = 10 + D2.size := by
      rw [hrun_len, List.length_ofFn]; rfl
    have hev : PEqualNP.MetaComplexity.circuitFun 10 D2 (fun _ => true) = false := by
      change (run D2.gates (List.ofFn (fun _ : Fin 10 => true))).getD D2.output false = false
      exact List.getD_eq_default _ _ (by omega)
    rw [hD2fun, hGraphEq, hF_true] at hev; cases hev
  have hD2outGe : 10 ≤ D2.output := by
    by_contra hlt
    have hlt10 : D2.output < 10 := Nat.lt_of_not_ge hlt
    let xs : Fin 10 → Bool := fun i => decide (i.val = D2.output)
    have hev : PEqualNP.MetaComplexity.circuitFun 10 D2 xs = true := by
      change (D2.wires (List.ofFn xs)).getD D2.output false = true
      rw [hwires_in D2 xs D2.output hlt10]
      simp [xs]
    rw [hD2fun, hGraphEq] at hev
    have hF0 : ∀ k : Fin 10, F (fun i => decide (i.val = k.val)) = false := by
      dsimp only [F]; decide +kernel
    have hbad := hF0 ⟨D2.output, hlt10⟩
    rw [hbad] at hev; cases hev
  have hD2outEq : D2.output = 10 + (D2.size - 1) := by
    by_contra hne
    let k : ℕ := D2.output - 10 + 1
    have hklt : k < D2.size := by omega
    have hklt_g : k < D2.gates.length := hklt
    let Dcut : PEqualNP.CircuitLowerBounds.Circuit := ⟨D2.gates.take k, D2.output⟩
    have hDcut_sz : Dcut.size = k := List.length_take_of_le (Nat.le_of_lt hklt)
    have hDcut_ao : PEqualNP.TopForm.IsAO2 10 Dcut := by
      refine ⟨fun g hg => hD2ao.1 g (List.mem_of_mem_take hg), ?_, fun g hg => hD2ao.2.2 g (List.mem_of_mem_take hg)⟩
      intro j hj i hi
      have hj' : j < k := hDcut_sz ▸ hj
      have hj2 : j < D2.gates.length := by omega
      have hgd : Dcut.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          D2.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
        change (D2.gates.take k).getD j _ = D2.gates.getD j _
        rw [List.getD_eq_getElem _ _ (by rw [List.length_take_of_le (Nat.le_of_lt hklt_g)]; exact hj'),
            List.getD_eq_getElem _ _ hj2, List.getElem_take]
      change i ∈ (Dcut.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
      rw [hgd] at hi
      exact hD2ao.2.1 j hj2 i hi
    have hDcut_fun : PEqualNP.MetaComplexity.circuitFun 10 Dcut = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      funext x
      have h1 : (run D2.gates (List.ofFn x)).getD D2.output false = (run (D2.gates.take k) (List.ofFn x)).getD D2.output false := by
        have hsp : D2.gates = D2.gates.take k ++ D2.gates.drop k := (List.take_append_drop k D2.gates).symm
        conv_lhs => rw [hsp]
        exact hrun_prefix (D2.gates.take k) (D2.gates.drop k) (List.ofFn x) D2.output
          (by rw [List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hklt)]; omega)
      exact h1.symm.trans (congrFun hD2fun x)
    have hle := hD2least.2.2 Dcut hDcut_ao hDcut_fun
    omega
  have hD2pos : 0 < D2.size := by omega
  have hGateInfo : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 10 D →
      ∀ j < D.size,
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs =
          [PEqualNP.TopForm.opnd D j 0, PEqualNP.TopForm.opnd D j 1] ∧
        PEqualNP.TopForm.opnd D j 0 < 10 + j ∧ PEqualNP.TopForm.opnd D j 1 < 10 + j := by
    intro D hD j hj
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt D j ∈ D.gates := by
      change D.gates.getD j _ ∈ D.gates
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hop := hD.1 _ hmem
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    have hin : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs =
        [PEqualNP.TopForm.opnd D j 0, PEqualNP.TopForm.opnd D j 1] := by
      rcases hgl : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · rw [hgl] at hlen; cases hlen
      · rw [hgl] at hlen; cases hlen
      · unfold PEqualNP.TopForm.opnd; rw [hgl]; rfl
      · rw [hgl] at hlen; cases hlen
    exact ⟨hop, hin, hD.2.1 j hj _ (by rw [hin]; simp), hD.2.1 j hj _ (by rw [hin]; simp)⟩
  have hwires_gate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 10 D →
      ∀ (x : Fin 10 → Bool) (j : ℕ) (hj : j < D.size),
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn x)).getD (10 + j) false =
            ((D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 0) false &&
             (D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 1) false)) ∧
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (D.wires (List.ofFn x)).getD (10 + j) false =
            ((D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 0) false ||
             (D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 1) false)) := by
    intro D hD x j hj
    obtain ⟨_, hin, hlt0, hlt1⟩ := hGateInfo D hD j hj
    have hrg := hrun_gate D.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hrg
    change (D.wires (List.ofFn x)).getD (10 + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs.map fun i =>
          if i < 10 + j then (D.wires (List.ofFn x)).getD i false else false) at hrg
    rw [hin, List.map_cons, List.map_cons, List.map_nil, ite_eq_left hlt0, ite_eq_left hlt1] at hrg
    constructor
    · intro hop; rw [hrg, hop, andEval]; simp
    · intro hop; rw [hrg, hop, orEval]; simp
  let auts : Fin 30 → Fin 10 → Fin 10 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
      ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
      ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
      ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
      ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![3, 2, 1, 6, 8, 4, 7, 0, 9, 5],
      ![3, 2, 7, 5, 8, 4, 1, 9, 0, 6],
      ![3, 2, 7, 9, 4, 8, 1, 5, 6, 0],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![3, 8, 5, 7, 2, 4, 6, 0, 9, 1],
      ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
      ![4, 3, 2, 7, 9, 0, 8, 1, 5, 6],
      ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
      ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
      ![1, 0, 4, 9, 6, 2, 5, 3, 7, 8],
      ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
      ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5],
      ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1],
      ![3, 8, 6, 1, 2, 4, 5, 9, 0, 7],
      ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 8, 3, 4, 9, 1, 5, 2, 0, 7],
      ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
      ![8, 3, 2, 7, 5, 6, 4, 1, 9, 0],
      ![8, 3, 4, 0, 5, 6, 2, 9, 1, 7],
      ![8, 3, 4, 9, 6, 5, 2, 0, 7, 1],
      ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
      ![8, 6, 9, 4, 3, 5, 1, 7, 0, 2]]
  let adjPet (i j : Fin 10) : Bool :=
    decide (G.Adj i j)
  have hAutCert :
      (∀ k : Fin 30, (∀ i j : Fin 10, auts k i = auts k j → i = j) ∧
        (∀ i j : Fin 10, adjPet (auts k i) (auts k j) = adjPet i j)) ∧
      (∀ a b : Fin 10, a ≠ b → ∃ k : Fin 30,
        (min (auts k a).val (auts k b).val = 0 ∧
         (max (auts k a).val (auts k b).val = 1 ∨ max (auts k a).val (auts k b).val = 2))) := by
    dsimp only [auts, adjPet, G]; decide +kernel
  obtain ⟨_, _, ha0lt, hb0lt⟩ := hGateInfo D2 hD2ao 0 hD2pos
  have ha010 : PEqualNP.TopForm.opnd D2 0 0 < 10 := by omega
  have hb010 : PEqualNP.TopForm.opnd D2 0 1 < 10 := by omega
  let A0 : Fin 10 := ⟨PEqualNP.TopForm.opnd D2 0 0, ha010⟩
  let B0 : Fin 10 := ⟨PEqualNP.TopForm.opnd D2 0 1, hb010⟩
  have hABne : A0 ≠ B0 := fun h => hD2dist 0 hD2pos (congrArg Fin.val h)
  obtain ⟨k, hmin0, hmax12⟩ := hAutCert.2 A0 B0 hABne
  obtain ⟨hAutInj, hAutAdj⟩ := hAutCert.1 k
  let σ : Equiv.Perm (Fin 10) := Equiv.ofBijective (auts k) (Finite.injective_iff_bijective.mp hAutInj)
  have hσ_pres_F : ∀ x : Fin 10 → Bool, F (x ∘ σ) = F x := by
    intro x
    rw [← hGraphEq, ← hGraphEq]
    have hiff : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (x ∘ σ) = true ↔
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
      have hGchar : ∀ y : Fin 10 → Bool,
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true ↔
          ∃ i j : Fin 10, adjPet i j = true ∧ y i = true ∧ y j = true := by
        dsimp only [adjPet, G]; decide +kernel
      rw [hGchar, hGchar]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        exact ⟨σ i, σ j, (hAutAdj i j).trans hij, hi, hj⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨σ.symm i, σ.symm j, ?_, ?_, ?_⟩
        · have h1 := hAutAdj (σ.symm i) (σ.symm j)
          change adjPet (σ (σ.symm i)) (σ (σ.symm j)) = adjPet (σ.symm i) (σ.symm j) at h1
          rw [σ.apply_symm_apply, σ.apply_symm_apply] at h1
          exact h1.symm.trans hij
        · change x (σ (σ.symm i)) = true; rwa [σ.apply_symm_apply]
        · change x (σ (σ.symm j)) = true; rwa [σ.apply_symm_apply]
    cases h1 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (x ∘ σ) <;>
    cases h2 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
    · rfl
    · exfalso; exact Bool.noConfusion ((hiff.mpr h2).symm.trans h1)
    · exfalso; exact Bool.noConfusion ((hiff.mp h1).symm.trans h2)
    · rfl
  let M (w : ℕ) : ℕ := if h : w < 10 then (σ ⟨w, h⟩).val else w
  have hMlt : ∀ w, M w < 10 ↔ w < 10 := by
    intro w
    by_cases hw : w < 10
    · simp only [M, dite_eq_left hw, hw, iff_true]; exact (σ ⟨w, hw⟩).isLt
    · simp [M, hw]
  have hMfin : ∀ i : Fin 10, M i.val = (σ i).val := fun i => by simp [M, i.isLt]
  have hMinj : ∀ u v, M u = M v → u = v := by
    intro u v huv
    by_cases hu : u < 10
    · have hv : v < 10 := (hMlt v).mp (huv ▸ (hMlt u).mpr hu)
      have h1 : (σ ⟨u, hu⟩).val = (σ ⟨v, hv⟩).val := by simpa [M, hu, hv] using huv
      exact congrArg Fin.val (σ.injective (Fin.ext h1))
    · have hv : ¬ v < 10 := fun hv => hu ((hMlt u).mp (huv.symm ▸ (hMlt v).mpr hv))
      simpa [M, hu, hv] using huv
  have hMbound : ∀ w j, w < 10 + j → M w < 10 + j := by
    intro w j hwj
    by_cases hw : w < 10
    · have := (hMlt w).mpr hw; omega
    · simpa [M, hw] using hwj
  let mapGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map M⟩
  let D3 : PEqualNP.CircuitLowerBounds.Circuit := ⟨D2.gates.map mapGate, M D2.output⟩
  have hD3sz : D3.size = D2.size := List.length_map mapGate
  have hD3gate : ∀ j < D2.size,
      PEqualNP.MetaComplexity.NestedCover.gateAt D3 j = mapGate (PEqualNP.MetaComplexity.NestedCover.gateAt D2 j) := by
    intro j hj
    change (D2.gates.map mapGate).getD j _ = mapGate (D2.gates.getD j _)
    rw [List.getD_eq_getElem _ _ (by simp; exact hj), List.getD_eq_getElem _ _ hj, List.getElem_map]
    rfl
  have hD3inputs : ∀ j < D2.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D3 j).inputs =
        [M (PEqualNP.TopForm.opnd D2 j 0), M (PEqualNP.TopForm.opnd D2 j 1)] := by
    intro j hj
    rw [hD3gate j hj]
    change (PEqualNP.MetaComplexity.NestedCover.gateAt D2 j).inputs.map M = _
    rw [(hGateInfo D2 hD2ao j hj).2.1]; rfl
  have hD3opnd : ∀ j < D2.size,
      PEqualNP.TopForm.opnd D3 j 0 = M (PEqualNP.TopForm.opnd D2 j 0) ∧
      PEqualNP.TopForm.opnd D3 j 1 = M (PEqualNP.TopForm.opnd D2 j 1) := by
    intro j hj
    change (PEqualNP.MetaComplexity.NestedCover.gateAt D3 j).inputs.getD 0 0 = _ ∧
           (PEqualNP.MetaComplexity.NestedCover.gateAt D3 j).inputs.getD 1 0 = _
    rw [hD3inputs j hj]; exact ⟨rfl, rfl⟩
  have hD3ao : PEqualNP.TopForm.IsAO2 10 D3 := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg; exact hD2ao.1 g' hg'
    · intro j hj w hw
      have hj' : j < D2.size := hD3sz ▸ hj
      rw [hD3inputs j hj', List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact hMbound _ j (hGateInfo D2 hD2ao j hj').2.2.1
      · exact hMbound _ j (hGateInfo D2 hD2ao j hj').2.2.2
    · intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      change (g'.inputs.map M).length = 2; rw [List.length_map]; exact hD2ao.2.2 g' hg'
  have hD3dist : ∀ j < D3.size, PEqualNP.TopForm.opnd D3 j 0 ≠ PEqualNP.TopForm.opnd D3 j 1 := by
    intro j hj
    have hj' : j < D2.size := hD3sz ▸ hj
    rw [(hD3opnd j hj').1, (hD3opnd j hj').2]
    intro heq; exact hD2dist j hj' (hMinj _ _ heq)
  have hD3out : D3.output = 10 + (D3.size - 1) := by
    change M D2.output = 10 + (D3.size - 1)
    simp [M, hD2outEq, hD3sz]
  have hD3wires : ∀ (x : Fin 10 → Bool) (w : ℕ), w < 10 + D2.size →
      (D3.wires (List.ofFn x)).getD (M w) false = (D2.wires (List.ofFn (x ∘ σ))).getD w false := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt
      by_cases hw10 : w < 10
      · let i : Fin 10 := ⟨w, hw10⟩
        change (D3.wires (List.ofFn x)).getD (M i.val) false = (D2.wires (List.ofFn (x ∘ σ))).getD i.val false
        rw [hMfin, hwires_in D3 x (σ i).val (σ i).isLt, hwires_in D2 (x ∘ σ) i.val i.isLt]
        rfl
      · let j : ℕ := w - 10
        have hwj : w = 10 + j := by omega
        have hj2 : j < D2.size := by omega
        have hj3 : j < D3.size := hD3sz.symm ▸ hj2
        have hMw : M w = 10 + j := by simp [M, hwj]
        rw [hMw, hwj]
        have hOpEq : (PEqualNP.MetaComplexity.NestedCover.gateAt D3 j).op =
            (PEqualNP.MetaComplexity.NestedCover.gateAt D2 j).op := by rw [hD3gate j hj2]
        obtain ⟨hCop, _, hlt0, hlt1⟩ := hGateInfo D2 hD2ao j hj2
        rcases hCop with hand | hor
        · rw [(hwires_gate D3 hD3ao x j hj3).1 (hOpEq.trans hand),
              (hwires_gate D2 hD2ao (x ∘ σ) j hj2).1 hand,
              (hD3opnd j hj2).1, (hD3opnd j hj2).2,
              ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
        · rw [(hwires_gate D3 hD3ao x j hj3).2 (hOpEq.trans hor),
              (hwires_gate D2 hD2ao (x ∘ σ) j hj2).2 hor,
              (hD3opnd j hj2).1, (hD3opnd j hj2).2,
              ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
  have hD3fun : PEqualNP.MetaComplexity.circuitFun 10 D3 = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext x
    have h1 : PEqualNP.MetaComplexity.circuitFun 10 D3 x = PEqualNP.MetaComplexity.circuitFun 10 D2 (x ∘ σ) :=
      hD3wires x D2.output hD2outLt
    rw [h1, hD2fun, hGraphEq, hGraphEq, hσ_pres_F]
  have hD3least : PEqualNP.TopForm.IsLeastAO G D3 :=
    ⟨hD3ao, hD3fun, fun C' hC'ao hC'fun => by rw [hD3sz]; exact hD2least.2.2 C' hC'ao hC'fun⟩
  have hDispatch : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsLeastAO G D → 0 < D.size → D.size ≤ 19 →
      D.output = 10 + (D.size - 1) →
      (∀ j < D.size, PEqualNP.TopForm.opnd D j 0 ≠ PEqualNP.TopForm.opnd D j 1) →
      PEqualNP.TopForm.opnd D 0 0 = 0 →
      (PEqualNP.TopForm.opnd D 0 1 = 1 ∨ PEqualNP.TopForm.opnd D 0 1 = 2) → False := by
    intro D hDL hDpos hDsz hDout hDdist h0 h12
    rcases (hGateInfo D hDL.1 0 hDpos).1 with hand | hor
    · rcases h12 with h1 | h2
      · exact hEdgeAnd D hDL hDsz hDout hDdist hand h0 h1
      · exact hNonEdgeAnd D hDL hDsz hDout hDdist hand h0 h2
    · rcases h12 with h1 | h2
      · exact hEdgeOr D hDL hDsz hDout hDdist hor h0 h1
      · exact hNonEdgeOr D hDL hDsz hDout hDdist hor h0 h2
  have hD3op0 : PEqualNP.TopForm.opnd D3 0 0 = (auts k A0).val := by
    rw [(hD3opnd 0 hD2pos).1]; exact hMfin A0
  have hD3op1 : PEqualNP.TopForm.opnd D3 0 1 = (auts k B0).val := by
    rw [(hD3opnd 0 hD2pos).2]; exact hMfin B0
  by_cases hOrd : PEqualNP.TopForm.opnd D3 0 0 ≤ PEqualNP.TopForm.opnd D3 0 1
  · have h0 : PEqualNP.TopForm.opnd D3 0 0 = 0 := by
      rw [hD3op0]; rw [hD3op0, hD3op1] at hOrd; omega
    have h12 : PEqualNP.TopForm.opnd D3 0 1 = 1 ∨ PEqualNP.TopForm.opnd D3 0 1 = 2 := by
      rw [hD3op1]; rw [hD3op0, hD3op1] at hOrd; omega
    exact hDispatch D3 hD3least (by omega) (by omega) hD3out hD3dist h0 h12
  · rcases hgs3 : D3.gates with _ | ⟨g0, rest⟩
    · have : D3.size = 0 := by change D3.gates.length = 0; rw [hgs3]; rfl
      omega
    · have hg0eq : g0 = PEqualNP.MetaComplexity.NestedCover.gateAt D3 0 := by
        change g0 = D3.gates.getD 0 _; rw [hgs3]; rfl
      have hg0in : g0.inputs = [PEqualNP.TopForm.opnd D3 0 0, PEqualNP.TopForm.opnd D3 0 1] := by
        rw [hg0eq]; exact (hGateInfo D3 hD3ao 0 (by omega)).2.1
      let g0' : PEqualNP.CircuitLowerBounds.Gate := ⟨g0.op, [PEqualNP.TopForm.opnd D3 0 1, PEqualNP.TopForm.opnd D3 0 0]⟩
      let D4 : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0' :: rest, D3.output⟩
      have hD4sz : D4.size = D3.size := by change (g0' :: rest).length = D3.gates.length; rw [hgs3]; rfl
      have hD4glen : D4.gates.length = D3.gates.length := hD4sz
      have hD4ao : PEqualNP.TopForm.IsAO2 10 D4 := by
        refine ⟨?_, ?_, ?_⟩
        · intro g hg
          rw [List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact hD3ao.1 g0 (by rw [hgs3]; exact List.mem_cons_self)
          · exact hD3ao.1 g (by rw [hgs3]; exact List.mem_cons_of_mem _ hg)
        · intro j hj i hi
          cases j with
          | zero =>
            change i ∈ g0'.inputs at hi
            simp only [g0', List.mem_cons, List.mem_nil_iff, or_false] at hi
            have hlt0 := (hGateInfo D3 hD3ao 0 (by omega)).2.2.1
            have hlt1 := (hGateInfo D3 hD3ao 0 (by omega)).2.2.2
            rcases hi with rfl | rfl <;> omega
          | succ j' =>
            have hj3 : j' + 1 < D3.gates.length := hD4glen ▸ hj
            have hi' : i ∈ (D3.gates.getD (j' + 1) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs := by
              rw [hgs3]; exact hi
            exact hD3ao.2.1 (j' + 1) hj3 i hi'
        · intro g hg
          rw [List.mem_cons] at hg
          rcases hg with rfl | hg
          · rfl
          · exact hD3ao.2.2 g (by rw [hgs3]; exact List.mem_cons_of_mem _ hg)
      have hD4dist : ∀ j < D4.size, PEqualNP.TopForm.opnd D4 j 0 ≠ PEqualNP.TopForm.opnd D4 j 1 := by
        intro j hj
        cases j with
        | zero =>
          change PEqualNP.TopForm.opnd D3 0 1 ≠ PEqualNP.TopForm.opnd D3 0 0
          exact Ne.symm (hD3dist 0 (by omega))
        | succ j' =>
          have h1 := hD3dist (j' + 1) (by omega)
          change (D3.gates.getD (j' + 1) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 0 0 ≠
                 (D3.gates.getD (j' + 1) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 1 0 at h1
          rw [hgs3] at h1
          exact h1
      have hD4fun : PEqualNP.MetaComplexity.circuitFun 10 D4 = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
        funext x
        have hstep0 : (g0'.op.eval (g0'.inputs.map fun i => (List.ofFn x).getD i false)) =
            (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)) := by
          have hg0op := hD3ao.1 g0 (by rw [hgs3]; exact List.mem_cons_self)
          dsimp only [g0']
          rw [hg0in]
          rcases hg0op with hand | hor
          · rw [hand, andEval, andEval]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact Bool.and_comm _ _
          · rw [hor, orEval, orEval]
            simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact Bool.or_comm _ _
        have hwires_eq : D4.wires (List.ofFn x) = D3.wires (List.ofFn x) := by
          change (g0' :: rest).foldl _ (List.ofFn x) = D3.gates.foldl _ (List.ofFn x)
          rw [hgs3, List.foldl_cons, List.foldl_cons, hstep0]
        change (D4.wires (List.ofFn x)).getD D3.output false = _
        rw [hwires_eq]
        exact congrFun hD3fun x
      have hD4least : PEqualNP.TopForm.IsLeastAO G D4 :=
        ⟨hD4ao, hD4fun, fun C' hC'ao hC'fun => by rw [hD4sz]; exact hD3least.2.2 C' hC'ao hC'fun⟩
      have h0 : PEqualNP.TopForm.opnd D4 0 0 = 0 := by
        change PEqualNP.TopForm.opnd D3 0 1 = 0
        rw [hD3op1]; rw [hD3op0, hD3op1] at hOrd; omega
      have h12 : PEqualNP.TopForm.opnd D4 0 1 = 1 ∨ PEqualNP.TopForm.opnd D4 0 1 = 2 := by
        change PEqualNP.TopForm.opnd D3 0 0 = 1 ∨ PEqualNP.TopForm.opnd D3 0 0 = 2
        rw [hD3op0]; rw [hD3op0, hD3op1] at hOrd; omega
      exact hDispatch D4 hD4least (by omega) (by omega) (by change D3.output = 10 + (D4.size - 1); omega) hD4dist h0 h12
