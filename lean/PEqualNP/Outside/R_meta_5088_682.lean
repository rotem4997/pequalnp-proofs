import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5088_682
    (deletedLower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))))
    (boundedReads : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      C.gates.countP (fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some 0 || g.inputs.head? == some 10 else g.inputs.contains 0 || g.inputs.contains 10) ∈ Set.Icc 1 2 →
      (∀ v : Fin 10, 15 + C.gates.countP (fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some v.val else g.inputs.contains v.val) ≤ C.size) →
      ∃ x, C.eval (List.ofFn x ++ [!x 0]) ≠ (fun (x : Fin 10 → Bool) => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       have x4 : ℕ := List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => if x4.op.eval [Bool.false] = Bool.true then x4.inputs.head? == Option.some (0 : ℕ) || x4.inputs.head? == Option.some (10 : ℕ) else x4.inputs.contains (0 : ℕ) || x4.inputs.contains (10 : ℕ)) x1.gates;       (1 : ℕ) ≤ x4 → x4 ≤ (2 : ℕ) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  -- Constant folding follows the compiler in R_meta_2598_314.
  -- One extra NOT gate supplies the complemented input after deleting another vertex.
  have restrictSize : ∀ (C : Circuit) (v : Fin 10) (σ : Fin 10 → Option (Fin 9)),
      FanInTwo C → C.size ≤ 18 → σ v = none →
      C.size + 1 ≤ 15 + C.gates.countP (fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some v.val else g.inputs.contains v.val) →
      HasCircuitSize 9 (fun y =>
        let x := fun i => (σ i).elim false y
        C.eval (List.ofFn x ++ [!x 0])) 15 := by
    intro C v σ hfan hsize hv hcount
    have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
    let pivot := v.val
    have hpivot : pivot < 10 := v.isLt
    let readsPivot := fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some pivot else g.inputs.contains pivot
    let wstep : List Bool → Gate → List Bool := fun w g =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let evalSym : List Bool → Sum Bool ℕ → Bool := fun w s =>
      Sum.elim id (fun k => w.getD k false) s
    let symBd : ℕ → Sum Bool ℕ → Prop := fun m s =>
      Sum.elim (fun _ => True) (fun k => k < 9 + m) s
    let cstep : (List (Sum Bool ℕ) × List Gate) → Gate → (List (Sum Bool ℕ) × List Gate) :=
      fun st g =>
        let env := st.1
        let dgs := st.2
        if g.op.eval [false] then
          if g.inputs.isEmpty then (env ++ [Sum.inl true], dgs)
          else
            Sum.elim
              (fun b => (env ++ [Sum.inl (!b)], dgs))
              (fun k => (env ++ [Sum.inr (9 + dgs.length)], dgs ++ [⟨GateOp.not, [k]⟩]))
              (env.getD (g.inputs.getD 0 0) (Sum.inl false))
        else if g.op.eval [] then
          if g.inputs.length == 0 then (env ++ [Sum.inl true], dgs)
          else if g.inputs.length == 1 then
            (env ++ [env.getD (g.inputs.getD 0 0) (Sum.inl false)], dgs)
          else
            let ea := env.getD (g.inputs.getD 0 0) (Sum.inl false)
            let eb := env.getD (g.inputs.getD 1 0) (Sum.inl false)
            Sum.elim
              (fun ba => if ba then (env ++ [eb], dgs) else (env ++ [Sum.inl false], dgs))
              (fun ka =>
                Sum.elim
                  (fun bb => if bb then (env ++ [Sum.inr ka], dgs) else (env ++ [Sum.inl false], dgs))
                  (fun kb => (env ++ [Sum.inr (9 + dgs.length)], dgs ++ [⟨GateOp.and, [ka, kb]⟩]))
                  eb)
              ea
        else
          if g.inputs.length == 0 then (env ++ [Sum.inl false], dgs)
          else if g.inputs.length == 1 then
            (env ++ [env.getD (g.inputs.getD 0 0) (Sum.inl false)], dgs)
          else
            let ea := env.getD (g.inputs.getD 0 0) (Sum.inl false)
            let eb := env.getD (g.inputs.getD 1 0) (Sum.inl false)
            Sum.elim
              (fun ba => if ba then (env ++ [Sum.inl true], dgs) else (env ++ [eb], dgs))
              (fun ka =>
                Sum.elim
                  (fun bb => if bb then (env ++ [Sum.inl true], dgs) else (env ++ [Sum.inr ka], dgs))
                  (fun kb => (env ++ [Sum.inr (9 + dgs.length)], dgs ++ [⟨GateOp.or, [ka, kb]⟩]))
                  eb)
              ea
    have wlen : ∀ (gs : List Gate) (w : List Bool), (gs.foldl wstep w).length = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g rest ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp [wstep, Nat.add_comm, Nat.add_left_comm]
    have hcomp_ind : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (dgs : List Gate)
        (wC : (Fin 9 → Bool) → List Bool),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ dgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        11 ≤ env.length →
        env.getD pivot (Sum.inl false) = Sum.inl false →
        (∀ y : Fin 9 → Bool, (wC y).length = env.length) →
        (∀ i : ℕ, symBd dgs.length (env.getD i (Sum.inl false))) →
        (∀ y : Fin 9 → Bool, ∀ i : ℕ,
          evalSym (dgs.foldl wstep (List.ofFn y)) (env.getD i (Sum.inl false)) = (wC y).getD i false) →
        let res := gs.foldl cstep (env, dgs)
        res.2.length + (gs.filter readsPivot).length ≤ dgs.length + gs.length ∧
        (∀ g ∈ res.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (∀ y : Fin 9 → Bool, ∀ i : ℕ,
          evalSym (res.2.foldl wstep (List.ofFn y)) (res.1.getD i (Sum.inl false)) =
            (gs.foldl wstep (wC y)).getD i false) := by
      intro gs
      induction gs with
      | nil =>
        intro env dgs wC _ hdgs _ _ _ _ heq
        exact ⟨by simp, hdgs, heq⟩
      | cons g rest ih =>
        intro env dgs wC hfg hdgs h11 h0 hwlen hbd heq
        have hgf := hfg g List.mem_cons_self
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgf.1
        let st1 := cstep (env, dgs) g
        have hstep :
            st1.1.length = env.length + 1 ∧
            st1.1.getD pivot (Sum.inl false) = Sum.inl false ∧
            (st1.2.length + (if readsPivot g then 1 else 0) ≤ dgs.length + 1) ∧
            (∀ g' ∈ st1.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
            (∀ i : ℕ, symBd st1.2.length (st1.1.getD i (Sum.inl false))) ∧
            (∀ y : Fin 9 → Bool, ∀ i : ℕ,
              evalSym (st1.2.foldl wstep (List.ofFn y)) (st1.1.getD i (Sum.inl false)) =
                (wstep (wC y) g).getD i false) := by
          have hstep_noemit : ∀ (v : Sum Bool ℕ),
              symBd dgs.length v →
              (∀ y : Fin 9 → Bool, evalSym (dgs.foldl wstep (List.ofFn y)) v =
                g.op.eval (g.inputs.map fun i => (wC y).getD i false)) →
              (env ++ [v]).length = env.length + 1 ∧
              (env ++ [v]).getD pivot (Sum.inl false) = Sum.inl false ∧
              (dgs.length + (if readsPivot g then 1 else 0) ≤ dgs.length + 1) ∧
              (∀ g' ∈ dgs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
              (∀ i : ℕ, symBd dgs.length ((env ++ [v]).getD i (Sum.inl false))) ∧
              (∀ y : Fin 9 → Bool, ∀ i : ℕ,
                evalSym (dgs.foldl wstep (List.ofFn y)) ((env ++ [v]).getD i (Sum.inl false)) =
                  (wstep (wC y) g).getD i false) := by
            intro v hvbd hveval
            refine ⟨by simp, ?_, by split_ifs <;> omega, hdgs, ?_, ?_⟩
            · rw [List.getD_append _ _ _ _ (by omega)]; exact h0
            · intro i
              by_cases hi : i < env.length
              · rw [List.getD_append _ _ _ _ hi]; exact hbd i
              · by_cases hi2 : i = env.length
                · subst hi2
                  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                  exact hvbd
                · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
            · intro y i
              by_cases hi : i < env.length
              · rw [List.getD_append _ _ _ _ hi]
                simp only [wstep]
                rw [List.getD_append _ _ _ _ (by rw [hwlen y]; exact hi)]
                exact heq y i
              · by_cases hi2 : i = env.length
                · subst hi2
                  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                  simp only [wstep]
                  rw [List.getD_append_right _ _ _ _ (by rw [hwlen y]), hwlen y, Nat.sub_self, List.getD_cons_zero]
                  exact hveval y
                · rw [List.getD_eq_default _ _ (by simp; omega)]
                  simp only [wstep]
                  rw [List.getD_eq_default _ _ (by simp [hwlen y]; omega)]
                  rfl
          have hstep_emit : ∀ (ng : Gate),
              ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2 →
              readsPivot g = false →
              (∀ y : Fin 9 → Bool,
                ng.op.eval (ng.inputs.map fun i => (dgs.foldl wstep (List.ofFn y)).getD i false) =
                  g.op.eval (g.inputs.map fun i => (wC y).getD i false)) →
              (env ++ [Sum.inr (9 + dgs.length)]).length = env.length + 1 ∧
              (env ++ [Sum.inr (9 + dgs.length)]).getD pivot (Sum.inl false) = Sum.inl false ∧
              ((dgs ++ [ng]).length + (if readsPivot g then 1 else 0) ≤ dgs.length + 1) ∧
              (∀ g' ∈ dgs ++ [ng], g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
              (∀ i : ℕ, symBd (dgs ++ [ng]).length ((env ++ [Sum.inr (9 + dgs.length)]).getD i (Sum.inl false))) ∧
              (∀ y : Fin 9 → Bool, ∀ i : ℕ,
                evalSym ((dgs ++ [ng]).foldl wstep (List.ofFn y)) ((env ++ [Sum.inr (9 + dgs.length)]).getD i (Sum.inl false)) =
                  (wstep (wC y) g).getD i false) := by
            intro ng hng hnr hngeval
            refine ⟨by simp, ?_, by simp [hnr], ?_, ?_, ?_⟩
            · rw [List.getD_append _ _ _ _ (by omega)]; exact h0
            · intro g' hg'
              rcases List.mem_append.mp hg' with hg' | hg'
              · exact hdgs g' hg'
              · simp only [List.mem_singleton] at hg'; subst hg'; exact hng
            · intro i
              by_cases hi : i < env.length
              · rw [List.getD_append _ _ _ _ hi]
                have hbi := hbd i
                cases hvi : env.getD i (Sum.inl false) with
                | inl _ => trivial
                | inr k =>
                  rw [hvi] at hbi
                  simp only [symBd, Sum.elim_inr, List.length_append, List.length_singleton] at hbi ⊢
                  omega
              · by_cases hi2 : i = env.length
                · subst hi2
                  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                  simp [symBd]
                · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
            · intro y i
              have hfold : (dgs ++ [ng]).foldl wstep (List.ofFn y) =
                  wstep (dgs.foldl wstep (List.ofFn y)) ng := by
                rw [List.foldl_append]; rfl
              have hdwlen : (dgs.foldl wstep (List.ofFn y)).length = 9 + dgs.length := by
                rw [wlen]; simp
              by_cases hi : i < env.length
              · rw [List.getD_append _ _ _ _ hi]
                simp only [wstep]
                rw [List.getD_append _ _ _ _ (by rw [hwlen y]; exact hi)]
                rw [← heq y i, hfold]
                have hbi := hbd i
                cases hvi : env.getD i (Sum.inl false) with
                | inl b => rfl
                | inr k =>
                  rw [hvi] at hbi
                  simp only [symBd, Sum.elim_inr] at hbi
                  simp only [evalSym, Sum.elim_inr, wstep]
                  exact List.getD_append _ _ _ _ (by rw [hdwlen]; exact hbi)
              · by_cases hi2 : i = env.length
                · subst hi2
                  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                  simp only [wstep]
                  rw [List.getD_append_right _ _ _ _ (by rw [hwlen y]), hwlen y, Nat.sub_self, List.getD_cons_zero]
                  simp only [evalSym, Sum.elim_inr, hfold, wstep]
                  rw [List.getD_append_right _ _ _ _ (by rw [hdwlen]), hdwlen, Nat.sub_self, List.getD_cons_zero]
                  exact hngeval y
                · rw [List.getD_eq_default _ _ (by simp; omega)]
                  simp only [wstep]
                  rw [List.getD_eq_default _ _ (by simp [hwlen y]; omega)]
                  rfl
          rcases hgop with hop | hop | hop
          · have hlen2 : g.inputs.length ≤ 2 := hgf.2
            cases hgin : g.inputs with
            | nil =>
              have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]; rfl
              rw [hst]
              exact hstep_noemit (Sum.inl true) trivial (fun y => by simp [hop, hgin, andEval, evalSym])
            | cons a tl =>
              cases tl with
              | nil =>
                have hst : st1 = (env ++ [env.getD a (Sum.inl false)], dgs) := by
                  dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]; rfl
                rw [hst]
                exact hstep_noemit (env.getD a (Sum.inl false)) (hbd a)
                  (fun y => by simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, Bool.and_true]; exact heq y a)
              | cons b tl2 =>
                cases tl2 with
                | cons _ _ => simp [hgin] at hlen2
                | nil =>
                  cases ha : env.getD a (Sum.inl false) with
                  | inl ba =>
                    cases ba with
                    | false =>
                      have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                        simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, ha,
                          Sum.elim_inl]
                      rw [hst]
                      exact hstep_noemit (Sum.inl false) trivial (fun y => by
                        have h1 := heq y a; rw [ha] at h1
                        simp only [evalSym, Sum.elim_inl, id_eq] at h1
                        simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inl]
                        rw [← h1]; rfl)
                    | true =>
                      cases hb : env.getD b (Sum.inl false) with
                      | inl bb =>
                        cases bb with
                        | false =>
                          have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                            dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                            simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                              List.getD_cons_succ, ha, hb, Sum.elim_inl]
                          rw [hst]
                          exact hstep_noemit (Sum.inl false) trivial (fun y => by
                            have h2 := heq y b; rw [hb] at h2
                            simp only [evalSym, Sum.elim_inl, id_eq] at h2
                            simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inl]
                            rw [← h2]; simp)
                        | true =>
                          have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                            dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                            simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                              List.getD_cons_succ, ha, hb, Sum.elim_inl]
                          rw [hst]
                          exact hstep_noemit (Sum.inl true) trivial (fun y => by
                            have h1 := heq y a; rw [ha] at h1
                            have h2 := heq y b; rw [hb] at h2
                            simp only [evalSym, Sum.elim_inl, id_eq] at h1 h2
                            simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inl]
                            rw [← h1, ← h2]; rfl)
                      | inr kb =>
                        have hkb := hbd b; rw [hb] at hkb
                        have hst : st1 = (env ++ [Sum.inr kb], dgs) := by
                          dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                          simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                            List.getD_cons_succ, ha, hb, Sum.elim_inl]
                        rw [hst]
                        exact hstep_noemit (Sum.inr kb) hkb (fun y => by
                          have h1 := heq y a; rw [ha] at h1
                          have h2 := heq y b; rw [hb] at h2
                          simp only [evalSym, Sum.elim_inl, Sum.elim_inr, id_eq] at h1 h2
                          simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inr]
                          rw [← h1, ← h2]; simp)
                  | inr ka =>
                    cases hb : env.getD b (Sum.inl false) with
                    | inl bb =>
                      cases bb with
                      | false =>
                        have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                          dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                          simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                            List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                        rw [hst]
                        exact hstep_noemit (Sum.inl false) trivial (fun y => by
                          have h2 := heq y b; rw [hb] at h2
                          simp only [evalSym, Sum.elim_inl, id_eq] at h2
                          simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inl]
                          rw [← h2]; simp)
                      | true =>
                        have hka := hbd a; rw [ha] at hka
                        have hst : st1 = (env ++ [Sum.inr ka], dgs) := by
                          dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                          simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                            List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                        rw [hst]
                        exact hstep_noemit (Sum.inr ka) hka (fun y => by
                          have h1 := heq y a; rw [ha] at h1
                          have h2 := heq y b; rw [hb] at h2
                          simp only [evalSym, Sum.elim_inl, Sum.elim_inr, id_eq] at h1 h2
                          simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inr]
                          rw [← h1, ← h2]; simp)
                    | inr kb =>
                      have hnr : readsPivot g = false := by
                        have ha0 : a ≠ pivot := by intro h; subst a; rw [h0] at ha; cases ha
                        have hb0 : b ≠ pivot := by intro h; subst b; rw [h0] at hb; cases hb
                        simp [readsPivot, hop, hgin, andEval]
                        exact ⟨ha0.symm, hb0.symm⟩
                      have hst : st1 = (env ++ [Sum.inr (9 + dgs.length)], dgs ++ [⟨GateOp.and, [ka, kb]⟩]) := by
                        dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                        simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                          List.getD_cons_succ, ha, hb, Sum.elim_inr]
                      rw [hst]
                      exact hstep_emit ⟨GateOp.and, [ka, kb]⟩ ⟨Or.inl rfl, by simp⟩ hnr (fun y => by
                        have h1 := heq y a; rw [ha] at h1
                        have h2 := heq y b; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inr] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq]
                        rw [h1, h2])
          · have hlen2 : g.inputs.length ≤ 2 := hgf.2
            cases hgin : g.inputs with
            | nil =>
              have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]; rfl
              rw [hst]
              exact hstep_noemit (Sum.inl false) trivial (fun y => by simp [hop, hgin, orEval, evalSym])
            | cons a tl =>
              cases tl with
              | nil =>
                have hst : st1 = (env ++ [env.getD a (Sum.inl false)], dgs) := by
                  dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]; rfl
                rw [hst]
                exact hstep_noemit (env.getD a (Sum.inl false)) (hbd a)
                  (fun y => by simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; exact heq y a)
              | cons b tl2 =>
                cases tl2 with
                | cons _ _ => simp [hgin] at hlen2
                | nil =>
                  cases ha : env.getD a (Sum.inl false) with
                  | inl ba =>
                    cases ba with
                    | true =>
                      have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, ha,
                          Sum.elim_inl]
                      rw [hst]
                      exact hstep_noemit (Sum.inl true) trivial (fun y => by
                        have h1 := heq y a; rw [ha] at h1
                        simp only [evalSym, Sum.elim_inl, id_eq] at h1
                        simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inl]
                        rw [← h1]; rfl)
                    | false =>
                      cases hb : env.getD b (Sum.inl false) with
                      | inl bb =>
                        cases bb with
                        | true =>
                          have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                            dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                            simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                              List.getD_cons_succ, ha, hb, Sum.elim_inl]
                          rw [hst]
                          exact hstep_noemit (Sum.inl true) trivial (fun y => by
                            have h2 := heq y b; rw [hb] at h2
                            simp only [evalSym, Sum.elim_inl, id_eq] at h2
                            simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inl]
                            rw [← h2]; simp)
                        | false =>
                          have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                            dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                            simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                              List.getD_cons_succ, ha, hb, Sum.elim_inl]
                          rw [hst]
                          exact hstep_noemit (Sum.inl false) trivial (fun y => by
                            have h1 := heq y a; rw [ha] at h1
                            have h2 := heq y b; rw [hb] at h2
                            simp only [evalSym, Sum.elim_inl, id_eq] at h1 h2
                            simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inl]
                            rw [← h1, ← h2]; rfl)
                      | inr kb =>
                        have hkb := hbd b; rw [hb] at hkb
                        have hst : st1 = (env ++ [Sum.inr kb], dgs) := by
                          dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                          simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                            List.getD_cons_succ, ha, hb, Sum.elim_inl]
                        rw [hst]
                        exact hstep_noemit (Sum.inr kb) hkb (fun y => by
                          have h1 := heq y a; rw [ha] at h1
                          have h2 := heq y b; rw [hb] at h2
                          simp only [evalSym, Sum.elim_inl, Sum.elim_inr, id_eq] at h1 h2
                          simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inr]
                          rw [← h1, ← h2]; simp)
                  | inr ka =>
                    cases hb : env.getD b (Sum.inl false) with
                    | inl bb =>
                      cases bb with
                      | true =>
                        have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                          dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                          simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                            List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                        rw [hst]
                        exact hstep_noemit (Sum.inl true) trivial (fun y => by
                          have h2 := heq y b; rw [hb] at h2
                          simp only [evalSym, Sum.elim_inl, id_eq] at h2
                          simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inl]
                          rw [← h2]; simp)
                      | false =>
                        have hka := hbd a; rw [ha] at hka
                        have hst : st1 = (env ++ [Sum.inr ka], dgs) := by
                          dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                          simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                            List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                        rw [hst]
                        exact hstep_noemit (Sum.inr ka) hka (fun y => by
                          have h1 := heq y a; rw [ha] at h1
                          have h2 := heq y b; rw [hb] at h2
                          simp only [evalSym, Sum.elim_inl, Sum.elim_inr, id_eq] at h1 h2
                          simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inr]
                          rw [← h1, ← h2]; simp)
                    | inr kb =>
                      have hnr : readsPivot g = false := by
                        have ha0 : a ≠ pivot := by intro h; subst a; rw [h0] at ha; cases ha
                        have hb0 : b ≠ pivot := by intro h; subst b; rw [h0] at hb; cases hb
                        simp [readsPivot, hop, hgin, orEval]
                        exact ⟨ha0.symm, hb0.symm⟩
                      have hst : st1 = (env ++ [Sum.inr (9 + dgs.length)], dgs ++ [⟨GateOp.or, [ka, kb]⟩]) := by
                        dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero,
                          List.getD_cons_succ, ha, hb, Sum.elim_inr]
                      rw [hst]
                      exact hstep_emit ⟨GateOp.or, [ka, kb]⟩ ⟨Or.inr (Or.inl rfl), by simp⟩ hnr (fun y => by
                        have h1 := heq y a; rw [ha] at h1
                        have h2 := heq y b; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inr] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq]
                        rw [h1, h2])
          · cases hgin : g.inputs with
            | nil =>
              have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                dsimp only [st1, cstep]; rw [hop, notEval, hgin]; rfl
              rw [hst]
              exact hstep_noemit (Sum.inl true) trivial (fun y => by simp [hop, hgin, notEval, evalSym])
            | cons a tl =>
              cases ha : env.getD a (Sum.inl false) with
              | inl ba =>
                have hst : st1 = (env ++ [Sum.inl (!ba)], dgs) := by
                  dsimp only [st1, cstep]; rw [hop, notEval, hgin]
                  simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
                    List.getD_cons_zero, ha, Sum.elim_inl]
                rw [hst]
                exact hstep_noemit (Sum.inl (!ba)) trivial (fun y => by
                  have h1 := heq y a; rw [ha] at h1
                  simp only [evalSym, Sum.elim_inl, id_eq] at h1
                  simp only [hop, hgin, List.map_cons, notEval, List.headD_cons, evalSym, Sum.elim_inl, id_eq]
                  rw [← h1])
              | inr ka =>
                have hnr : readsPivot g = false := by
                  have ha0 : a ≠ pivot := by intro h; subst a; rw [h0] at ha; cases ha
                  simp [readsPivot, hop, hgin, notEval, ha0]
                have hst : st1 = (env ++ [Sum.inr (9 + dgs.length)], dgs ++ [⟨GateOp.not, [ka]⟩]) := by
                  dsimp only [st1, cstep]; rw [hop, notEval, hgin]
                  simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
                    List.getD_cons_zero, ha, Sum.elim_inr]
                rw [hst]
                exact hstep_emit ⟨GateOp.not, [ka]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ hnr (fun y => by
                  have h1 := heq y a; rw [ha] at h1
                  simp only [evalSym, Sum.elim_inr] at h1
                  simp only [hop, hgin, List.map_cons, notEval, List.headD_cons]
                  rw [h1])
        rcases hstep with ⟨hslen, hs0, hssz, hsfan, hsbd, hseq⟩
        have hrec := ih st1.1 st1.2 (fun y => wstep (wC y) g)
          (fun g' hg' => hfg g' (List.mem_cons_of_mem _ hg'))
          hsfan (by omega) hs0
          (fun y => by simp [wstep, hwlen y, hslen])
          hsbd hseq
        rcases hrec with ⟨hsz', hfan', heq'⟩
        refine ⟨?_, hfan', heq'⟩
        change (rest.foldl cstep st1).2.length + ((g :: rest).filter readsPivot).length ≤ dgs.length + (g :: rest).length
        have hsz1 : (rest.foldl cstep st1).2.length + (rest.filter readsPivot).length ≤ st1.2.length + rest.length := hsz'
        cases hrg : readsPivot g with
        | false =>
          simp only [List.filter_cons, hrg, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hssz ⊢
          omega
        | true =>
          simp only [List.filter_cons, hrg, ↓reduceIte, List.length_cons] at hssz ⊢
          omega
    let sym (i : Fin 10) : Sum Bool ℕ := (σ i).elim (Sum.inl false) (fun j => Sum.inr j.val)
    let extra : Sum Bool ℕ := (σ 0).elim (Sum.inl true) (fun _ => Sum.inr 9)
    let env0 := List.ofFn sym ++ [extra]
    let inv : List Gate := [⟨GateOp.not, [((σ 0).getD 0).val]⟩]
    let lift := fun (y : Fin 9 → Bool) (i : Fin 10) => (σ i).elim false y
    have atFn {α : Type} {n : Nat} (f : Fin n → α) (j : Fin n) (d : α) :
        (List.ofFn f).getD j.val d = f j := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
    have start (y : Fin 9 → Bool) : inv.foldl wstep (List.ofFn y) =
        List.ofFn y ++ [!y ((σ 0).getD 0)] := by
      change List.ofFn y ++ [!((List.ofFn y).getD ((σ 0).getD 0).val false)] = _
      rw [atFn]
    have refAt (i : Fin 10) : env0.getD i.val (Sum.inl false) = sym i := by
      rw [List.getD_append _ _ _ _ (by simp)]
      exact atFn sym i _
    have extraAt : env0.getD 10 (Sum.inl false) = extra := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    have ids : env0.getD pivot (Sum.inl false) = Sum.inl false := by
      rw [refAt v]; simp [sym, hv]
    have bounded : ∀ i : ℕ, symBd inv.length (env0.getD i (Sum.inl false)) := by
      intro i
      by_cases hi : i < 10
      · rw [refAt ⟨i,hi⟩]
        cases hs : σ ⟨i,hi⟩ with
        | none => simp [sym, hs, symBd]
        | some j => simp [sym, hs, symBd, inv]; omega
      · by_cases hi' : i = 10
        · subst i; rw [extraAt]; cases hs : σ 0 <;> simp [extra, hs, symBd, inv]
        · rw [List.getD_eq_default _ _ (by simp [env0]; omega)]; trivial
    have agree : ∀ y : Fin 9 → Bool, ∀ i : ℕ,
        evalSym (inv.foldl wstep (List.ofFn y)) (env0.getD i (Sum.inl false)) =
          (List.ofFn (lift y) ++ [!lift y 0]).getD i false := by
      intro y i
      rw [start]
      by_cases hi : i < 10
      · rw [refAt ⟨i,hi⟩, List.getD_append _ _ _ _ (by simpa using hi), atFn (lift y) ⟨i,hi⟩ false]
        cases hs : σ ⟨i,hi⟩ with
        | none => simp [evalSym, sym, lift, hs]
        | some j =>
          simp only [evalSym, sym, lift, hs, Option.elim_some, Sum.elim_inr]
          rw [List.getD_append _ _ _ _ (by simp), atFn]
      · by_cases hi' : i = 10
        · subst i; rw [extraAt]; cases hs : σ 0 <;>
            simp [evalSym, extra, hs, lift, List.getD_eq_getElem?_getD]
        · rw [List.getD_eq_default _ _ (by simp [env0]; omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
    have result := hcomp_ind C.gates env0 inv (fun y => List.ofFn (lift y) ++ [!lift y 0])
      hfan (by simp [inv, Set.mem_insert_iff, Set.mem_singleton_iff])
      (by simp [env0]) ids (fun y => by simp [env0]) bounded agree
    obtain ⟨hsz, valid, sem⟩ := result
    let res := C.gates.foldl cstep (env0, inv)
    cases hw : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      let D : Circuit := ⟨[⟨if b then GateOp.and else GateOp.or, []⟩], 9⟩
      refine ⟨D, ?_, by change 1 ≤ 15; decide, ?_⟩
      · intro g hg
        change g ∈ [⟨if b then GateOp.and else GateOp.or, []⟩] at hg
        have hg' := List.mem_singleton.mp hg
        subst g
        cases b <;> simp
      · intro y
        have e := sem y C.output
        change evalSym _ (res.1.getD C.output (Sum.inl false)) = _ at e
        rw [hw] at e
        refine Eq.trans ?_ e
        cases b
        · change (List.ofFn y ++ [false]).getD 9 false = false
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        · change (List.ofFn y ++ [true]).getD 9 false = true
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
    | inr k =>
      refine ⟨⟨res.2, k⟩, valid, ?_, ?_⟩
      · change res.2.length ≤ 15
        change res.2.length + _ ≤ inv.length + C.gates.length at hsz
        change C.gates.length ≤ 18 at hsize
        change C.size + 1 ≤ 15 + C.gates.countP readsPivot at hcount
        change C.gates.length + 1 ≤ 15 + C.gates.countP readsPivot at hcount
        rw [List.countP_eq_length_filter] at hcount
        simp only [inv, List.length_singleton] at hsz
        omega
      · intro y
        have e := sem y C.output
        change evalSym _ (res.1.getD C.output (Sum.inl false)) = _ at e
        rw [hw] at e
        exact e

  intro C fan size r hlo hhi
  let f10 : (Fin 10 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let f9 : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let reads := fun (v : Fin 10) => fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some v.val else g.inputs.contains v.val
  have maskEq : ∀ x : Fin 10 → Bool, f10 x = (fun (x : Fin 10 → Bool) => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x := by decide +kernel
  by_contra no
  have correct (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [!x 0]) = f10 x := by
    by_contra h
    exact no ⟨x, h⟩
  have relabelAt (v : Fin 10) : ∃ σ : Fin 10 → Option (Fin 9),
      σ v = none ∧ ∀ y : Fin 9 → Bool, f10 (fun i => (σ i).elim false y) = f9 y := by
    fin_cases v
    · refine ⟨fun i => ([none, some 4, some 0, some 1, some 6, some 7, some 3, some 5, some 2, some 8] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (false && y 4 || y 4 && y 0 || y 0 && y 1 || y 1 && y 6 || y 6 && false || false && y 7 || y 4 && y 3 || y 0 && y 5 || y 1 && y 2 || y 6 && y 8 || y 7 && y 5 || y 5 && y 8 || y 8 && y 3 || y 3 && y 2 || y 2 && y 7) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 4, none, some 6, some 1, some 0, some 3, some 7, some 8, some 2, some 5] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 4 && false || false && y 6 || y 6 && y 1 || y 1 && y 0 || y 0 && y 4 || y 4 && y 3 || false && y 7 || y 6 && y 8 || y 1 && y 2 || y 0 && y 5 || y 3 && y 8 || y 8 && y 5 || y 5 && y 7 || y 7 && y 2 || y 2 && y 3) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 0, some 4, none, some 6, some 1, some 5, some 3, some 7, some 8, some 2] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 0 && y 4 || y 4 && false || false && y 6 || y 6 && y 1 || y 1 && y 0 || y 0 && y 5 || y 4 && y 3 || false && y 7 || y 6 && y 8 || y 1 && y 2 || y 5 && y 7 || y 7 && y 2 || y 2 && y 3 || y 3 && y 8 || y 8 && y 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 0, some 1, some 6, none, some 4, some 5, some 2, some 8, some 7, some 3] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 0 && y 1 || y 1 && y 6 || y 6 && false || false && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 2 || y 6 && y 8 || false && y 7 || y 4 && y 3 || y 5 && y 8 || y 8 && y 3 || y 3 && y 2 || y 2 && y 7 || y 7 && y 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 4, some 0, some 1, some 6, none, some 3, some 5, some 2, some 8, some 7] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 4 && y 0 || y 0 && y 1 || y 1 && y 6 || y 6 && false || false && y 4 || y 4 && y 3 || y 0 && y 5 || y 1 && y 2 || y 6 && y 8 || false && y 7 || y 3 && y 2 || y 2 && y 7 || y 7 && y 5 || y 5 && y 8 || y 8 && y 3) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 4, some 0, some 1, some 2, some 3, none, some 5, some 6, some 7, some 8] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 4 && y 0 || y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && false || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || false && y 6 || y 6 && y 8 || y 8 && y 5 || y 5 && y 7 || y 7 && false) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 0, some 4, some 3, some 2, some 1, some 5, none, some 8, some 7, some 6] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 0 && y 4 || y 4 && y 3 || y 3 && y 2 || y 2 && y 1 || y 1 && y 0 || y 0 && y 5 || y 4 && false || y 3 && y 8 || y 2 && y 7 || y 1 && y 6 || y 5 && y 8 || y 8 && y 6 || y 6 && false || false && y 7 || y 7 && y 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 0, some 1, some 6, some 8, some 5, some 4, some 2, none, some 3, some 7] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 0 && y 1 || y 1 && y 6 || y 6 && y 8 || y 8 && y 5 || y 5 && y 0 || y 0 && y 4 || y 1 && y 2 || y 6 && false || y 8 && y 3 || y 5 && y 7 || y 4 && false || false && y 7 || y 7 && y 2 || y 2 && y 3 || y 3 && y 4) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 0, some 1, some 2, some 7, some 5, some 4, some 6, some 3, none, some 8] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 0 && y 1 || y 1 && y 2 || y 2 && y 7 || y 7 && y 5 || y 5 && y 0 || y 0 && y 4 || y 1 && y 6 || y 2 && y 3 || y 7 && false || y 5 && y 8 || y 4 && y 3 || y 3 && y 8 || y 8 && y 6 || y 6 && false || false && y 4) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]
      ac_rfl
    · refine ⟨fun i => ([some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8, none] : List (Option (Fin 9))).getD i.val none, rfl, ?_⟩
      intro y
      change (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 4 && false || y 5 && y 7 || y 7 && false || false && y 6 || y 6 && y 8 || y 8 && y 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.false_and, Bool.and_false, Bool.or_false]

  have bound (v : Fin 10) : 15 + C.gates.countP (reads v) ≤ C.size := by
    by_contra h
    obtain ⟨σ, hv, iso⟩ := relabelAt v
    obtain ⟨D, df, ds, eq⟩ := restrictSize C v σ fan size hv (by change C.size + 1 ≤ 15 + C.gates.countP (reads v); omega)
    obtain ⟨y, different⟩ := deletedLower D df ds
    exact different ((eq y).trans ((correct _).trans (iso y)))
  obtain ⟨x, bad⟩ := boundedReads C fan size ⟨hlo,hhi⟩ bound
  exact bad ((correct x).trans (maskEq x))
