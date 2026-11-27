import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3865_1
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (14 : ℕ) →
      ∃ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) ||
         x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) ||
         x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) ||
         x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
         x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
         x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (11 : ℕ) →
      ∃ (x : Fin (8 : ℕ) → Bool), C.eval (List.ofFn x) ≠
        (x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) ||
         x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) || x (0 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) ||
         x (1 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
         x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
         x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1 = [(9 : ℕ), (1 : ℕ)] ∨ x1 = [(9 : ℕ), (2 : ℕ)] ∨ x1 = [(9 : ℕ), (3 : ℕ)] ∨ x1 = [(9 : ℕ), (4 : ℕ)] ∨ x1 = [(9 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 C hfan hs
  refine Classical.byContradiction fun hno => ?_
  have hagree0 : ∀ (x : Fin 9 → Bool),
      C.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
         x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) :=
    fun x => Classical.byContradiction fun hne => hno ⟨x, hne⟩
  let fP9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let fH : (Fin 8 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  have hgetFn : ∀ (x : Fin 9 → Bool) (extra : List Bool) (i : Fin 9),
      (List.ofFn x ++ extra).getD i.val false = x i := by
    intro x extra i
    have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hgetFn8 : ∀ (y : Fin 8 → Bool) (i : Fin 8),
      (List.ofFn y).getD i.val false = y i := by
    intro y i
    have hi : i.val < (List.ofFn y).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hget9 : ∀ (x : Fin 9 → Bool), (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := by
    intro x
    have hle : (List.ofFn x).length ≤ 9 := by rw [List.length_ofFn]
    rw [List.getD_append_right _ _ _ _ hle, List.length_ofFn]
    rfl
  obtain ⟨idx, hidxMem, hagree⟩ :
      ∃ idx : Fin 9, (idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 6) ∧
        ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, !x 0 || x idx]) = fP9 x := by
    have hmk : ∀ (k : Fin 9),
        (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6) → x1 = [9, k.val] →
        ∃ idx : Fin 9, (idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 6) ∧
          ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, !x 0 || x idx]) = fP9 x := by
      intro k hk heq
      refine ⟨k, hk, fun x => ?_⟩
      have hx := hagree0 x
      rw [heq] at hx
      have hor : GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [9, k.val]) =
          (!x 0 || x k) := by
        rw [List.map_cons, List.map_cons, List.map_nil]
        change ([(List.ofFn x ++ [!x 0]).getD 9 false, (List.ofFn x ++ [!x 0]).getD k.val false].any id) = _
        rw [hget9 x, hgetFn x [!x 0] k]
        cases (!x 0) <;> cases (x k) <;> rfl
      rw [hor, List.append_assoc, List.cons_append, List.nil_append] at hx
      exact hx
    rcases hx1 with h | h | h | h | h
    · exact hmk 1 (Or.inl rfl) h
    · exact hmk 2 (Or.inr (Or.inl rfl)) h
    · exact hmk 3 (Or.inr (Or.inr (Or.inl rfl))) h
    · exact hmk 4 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
    · exact hmk 6 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have heval_run : ∀ (D : Circuit) (w : List Bool), D.eval w = (run D.gates w).getD D.output false :=
    fun _ _ => rfl
  have hsz_len : ∀ (D : Circuit), D.size = D.gates.length := fun _ => rfl
  have hstep_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
    intro w g
    simp only [step, List.length_append, List.length_singleton]
  have hrun_cons : ∀ (g : Gate) (gs : List Gate) (w : List Bool), run (g :: gs) w = run gs (step w g) :=
    fun _ _ _ => rfl
  have hrun_append : ∀ (gs hs : List Gate) (w : List Bool), run (gs ++ hs) w = run hs (run gs w) :=
    fun gs hs w => List.foldl_append
  have hrun_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [hrun_cons, ih, hstep_len, List.length_cons]
      omega
  have hrun_preserves : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), m < w.length →
      (run gs w).getD m false = w.getD m false := by
    intro gs
    induction gs with
    | nil => intro w m _; rfl
    | cons g gs ih =>
      intro w m hm
      rw [hrun_cons, ih _ _ (by rw [hstep_len]; omega)]
      exact List.getD_append _ _ _ _ hm
  have hgetD_append_len : ∀ {α : Type} (xs ys : List α) (d : α),
      (xs ++ ys).getD xs.length d = ys.getD 0 d := by
    intro α xs ys d
    rw [List.getD_append_right xs ys d xs.length (le_refl _), Nat.sub_self]
  let initW : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x 0, !x 0 || x idx]
  have hinit_len : ∀ x, (initW x).length = 11 := by
    intro x
    change (List.ofFn x ++ [!x 0, !x 0 || x idx]).length = 11
    rw [List.length_append, List.length_ofFn]
    rfl
  have hinit_0 : ∀ x, (initW x).getD 0 false = x 0 := fun x => hgetFn x _ 0
  have hinit_9 : ∀ x, (initW x).getD 9 false = !x 0 := by
    intro x
    rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn]
    rfl
  have hinit_10 : ∀ x, (initW x).getD 10 false = (!x 0 || x idx) := by
    intro x
    rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn]
    rfl
  let effInputs (g : Gate) : List ℕ :=
    GateOp.casesOn (motive := fun _ => List ℕ) g.op
      g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
  have heff : ∀ (g : Gate) (w : List Bool),
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval ((effInputs g).map fun i => w.getD i false) := by
    intro g w
    cases g
    rename_i op ins
    cases op <;> cases ins <;> rfl
  have heff_len : ∀ (g : Gate), g.inputs.length ≤ 2 → (effInputs g).length ≤ 2 := by
    intro g hg
    cases g
    rename_i op ins
    cases op with
    | not =>
      cases ins with
      | nil => simp [effInputs]
      | cons a l => simp [effInputs]
    | and => exact hg
    | or => exact hg
    | mod _ => exact hg
    | maj => exact hg
  let isZ : ℕ → Bool := fun w => decide (w = 0 ∨ w = 9 ∨ w = 10)
  let readsZero : Gate → Bool := fun g => (effInputs g).any isZ
  -- Part A: constant propagation under x 0 = false
  let evalVal : List Bool → Sum Bool ℕ → Bool := fun W v =>
    Sum.casesOn (motive := fun _ => Bool) v (fun b => b) (fun w => W.getD w false)
  let evalOne (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate) : Sum Bool ℕ × Option Gate :=
    GateOp.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.op
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl true, none) fun a t =>
        List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) t (env.getD a (Sum.inl false), none) fun b _ =>
          Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
            (fun ba => cond ba (env.getD b (Sum.inl false), none) (Sum.inl false, none))
            (fun wa => Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD b (Sum.inl false))
              (fun bb => cond bb (Sum.inr wa, none) (Sum.inl false, none))
              (fun wb => (Sum.inr (8 + gs'.length), some ⟨GateOp.and, [wa, wb]⟩))))
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl false, none) fun a t =>
        List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) t (env.getD a (Sum.inl false), none) fun b _ =>
          Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
            (fun ba => cond ba (Sum.inl true, none) (env.getD b (Sum.inl false), none))
            (fun wa => Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD b (Sum.inl false))
              (fun bb => cond bb (Sum.inl true, none) (Sum.inr wa, none))
              (fun wb => (Sum.inr (8 + gs'.length), some ⟨GateOp.or, [wa, wb]⟩))))
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl true, none) fun a _ =>
        Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
          (fun b => (Sum.inl (!b), none))
          (fun wa => (Sum.inr (8 + gs'.length), some ⟨GateOp.not, [wa]⟩)))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  let compileStep (st : List (Sum Bool ℕ) × List Gate) (g : Gate) : List (Sum Bool ℕ) × List Gate :=
    let r := evalOne g st.1 st.2
    Option.casesOn (motive := fun _ => List (Sum Bool ℕ) × List Gate) r.2
      (st.1 ++ [r.1], st.2)
      (fun g' => (st.1 ++ [r.1], st.2 ++ [g']))
  let compileLoop : List Gate → List (Sum Bool ℕ) × List Gate → List (Sum Bool ℕ) × List Gate :=
    fun gs st => gs.foldl compileStep st
  let fanOK : Gate → Prop := fun g =>
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  have hcomp_step_props : ∀ (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate),
      fanOK g →
      11 ≤ env.length →
      env.getD 0 (Sum.inl false) = Sum.inl false →
      env.getD 9 (Sum.inl false) = Sum.inl true →
      env.getD 10 (Sum.inl false) = Sum.inl true →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < 8 + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      let st1 := compileStep (env, gs') g
      (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        (readsZero g = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < 8 + st1.2.length) ∧
        st1.1.length = env.length + 1 ∧
        st1.1.getD 0 (Sum.inl false) = Sum.inl false ∧
        st1.1.getD 9 (Sum.inl false) = Sum.inl true ∧
        st1.1.getD 10 (Sum.inl false) = Sum.inl true := by
    intro g env gs' hgfan hlen h0 h9 h10 hbound hfg
    cases g
    rename_i op ins
    let st1 := compileStep (env, gs') ⟨op, ins⟩
    have hpres : ∀ m, m < env.length → st1.1.getD m (Sum.inl false) = env.getD m (Sum.inl false) := by
      intro m hm
      dsimp [st1, compileStep]
      cases (evalOne ⟨op, ins⟩ env gs').2 <;> exact List.getD_append _ _ _ _ hm
    have hlen1 : st1.1.length = env.length + 1 := by
      dsimp [st1, compileStep]
      cases (evalOne ⟨op, ins⟩ env gs').2 <;> simp
    have h0' : st1.1.getD 0 (Sum.inl false) = Sum.inl false := (hpres 0 (by omega)).trans h0
    have h9' : st1.1.getD 9 (Sum.inl false) = Sum.inl true := (hpres 9 (by omega)).trans h9
    have h10' : st1.1.getD 10 (Sum.inl false) = Sum.inl true := (hpres 10 (by omega)).trans h10
    have hnone_case : ∀ v_out : Sum Bool ℕ,
        (∀ j, v_out = Sum.inr j → j < 8 + gs'.length) →
        (∃ ext1, gs' = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        (readsZero ⟨op, ins⟩ = true → gs' = gs') ∧
        (∀ g' ∈ gs', fanOK g') ∧
        (∀ v ∈ env ++ [v_out], ∀ j, v = Sum.inr j → j < 8 + gs'.length) := by
      intro v_out hv_bd
      refine ⟨⟨[], by simp⟩, fun _ => rfl, hfg, ?_⟩
      intro v hv j hj
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hbound v hv j hj
      · exact hv_bd j hj
    have hget_bound : ∀ a, ∀ j, env.getD a (Sum.inl false) = Sum.inr j → j < 8 + gs'.length := by
      intro a j ha
      by_cases hlt : a < env.length
      · rw [List.getD_eq_getElem _ _ hlt] at ha
        exact hbound _ (List.getElem_mem hlt) j ha
      · rw [List.getD_eq_default _ _ (by omega)] at ha
        cases ha
    have hrz_inl : ∀ a, isZ a = true → ∃ b, env.getD a (Sum.inl false) = Sum.inl b := by
      intro a ha
      change decide (a = 0 ∨ a = 9 ∨ a = 10) = true at ha
      rw [decide_eq_true_eq] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨false, h0⟩
      · exact ⟨true, h9⟩
      · exact ⟨true, h10⟩
    have hcore :
        (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        (readsZero ⟨op, ins⟩ = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < 8 + st1.2.length) := by
      rcases hgfan with ⟨hop, hilen⟩
      dsimp [st1, compileStep]
      rcases hop with rfl | rfl | rfl
      · -- and
        cases ins with
        | nil => exact hnone_case (Sum.inl true) (fun _ h => by cases h)
        | cons a t =>
          cases t with
          | nil => exact hnone_case (env.getD a (Sum.inl false)) (hget_bound a)
          | cons b r =>
            have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
            subst hr_nil
            have hrz_none : readsZero ⟨GateOp.and, [a, b]⟩ = true →
                (evalOne ⟨GateOp.and, [a, b]⟩ env gs').2 = none := by
              intro hrz
              change ([a, b].any isZ) = true at hrz
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hrz
              dsimp [evalOne]
              rcases hrz with ha | hb
              · obtain ⟨ba, hba⟩ := hrz_inl a ha
                rw [hba]
                cases ba <;> cases env.getD b (Sum.inl false) with
                | inl bb => cases bb <;> rfl
                | inr _ => rfl
              · obtain ⟨bb, hbb⟩ := hrz_inl b hb
                rw [hbb]
                cases env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> cases bb <;> rfl
                | inr _ => cases bb <;> rfl
            dsimp [evalOne]
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              cases ba
              · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
              · cases hgb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
                  · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
                | inr wb =>
                  exact hnone_case (Sum.inr wb) (fun j hj => by cases hj; exact hget_bound b wb hgb)
            | inr wa =>
              cases hgb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb
                · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
                · exact hnone_case (Sum.inr wa) (fun j hj => by cases hj; exact hget_bound a wa hga)
              | inr wb =>
                refine ⟨⟨[⟨GateOp.and, [wa, wb]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
                · intro hrz
                  have : ((Sum.inr (8 + gs'.length) : Sum Bool ℕ), some (Gate.mk GateOp.and [wa, wb])).2 = none := by
                    have h' := hrz_none hrz
                    dsimp [evalOne] at h'
                    rw [hga, hgb] at h'
                    exact h'
                  cases this
                · intro g' hg'
                  rw [List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hfg g' hg'
                  · exact ⟨Or.inl rfl, by simp⟩
                · intro v hv j hj
                  rw [List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | rfl
                  · have := hbound v hv j hj
                    rw [List.length_append, List.length_singleton]
                    omega
                  · cases hj
                    rw [List.length_append, List.length_singleton]
                    omega
      · -- or
        cases ins with
        | nil => exact hnone_case (Sum.inl false) (fun _ h => by cases h)
        | cons a t =>
          cases t with
          | nil => exact hnone_case (env.getD a (Sum.inl false)) (hget_bound a)
          | cons b r =>
            have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
            subst hr_nil
            have hrz_none : readsZero ⟨GateOp.or, [a, b]⟩ = true →
                (evalOne ⟨GateOp.or, [a, b]⟩ env gs').2 = none := by
              intro hrz
              change ([a, b].any isZ) = true at hrz
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hrz
              dsimp [evalOne]
              rcases hrz with ha | hb
              · obtain ⟨ba, hba⟩ := hrz_inl a ha
                rw [hba]
                cases ba <;> cases env.getD b (Sum.inl false) with
                | inl bb => cases bb <;> rfl
                | inr _ => rfl
              · obtain ⟨bb, hbb⟩ := hrz_inl b hb
                rw [hbb]
                cases env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> cases bb <;> rfl
                | inr _ => cases bb <;> rfl
            dsimp [evalOne]
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              cases ba
              · cases hgb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
                  · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
                | inr wb =>
                  exact hnone_case (Sum.inr wb) (fun j hj => by cases hj; exact hget_bound b wb hgb)
              · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
            | inr wa =>
              cases hgb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb
                · exact hnone_case (Sum.inr wa) (fun j hj => by cases hj; exact hget_bound a wa hga)
                · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
              | inr wb =>
                refine ⟨⟨[⟨GateOp.or, [wa, wb]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
                · intro hrz
                  have : ((Sum.inr (8 + gs'.length) : Sum Bool ℕ), some (Gate.mk GateOp.or [wa, wb])).2 = none := by
                    have h' := hrz_none hrz
                    dsimp [evalOne] at h'
                    rw [hga, hgb] at h'
                    exact h'
                  cases this
                · intro g' hg'
                  rw [List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hfg g' hg'
                  · exact ⟨Or.inr (Or.inl rfl), by simp⟩
                · intro v hv j hj
                  rw [List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | rfl
                  · have := hbound v hv j hj
                    rw [List.length_append, List.length_singleton]
                    omega
                  · cases hj
                    rw [List.length_append, List.length_singleton]
                    omega
      · -- not
        cases ins with
        | nil => exact hnone_case (Sum.inl true) (fun _ h => by cases h)
        | cons a t =>
          have hrz_none : readsZero ⟨GateOp.not, a :: t⟩ = true →
              (evalOne ⟨GateOp.not, a :: t⟩ env gs').2 = none := by
            intro hrz
            change (([a]).any isZ) = true at hrz
            simp only [List.any_cons, List.any_nil, Bool.or_false] at hrz
            obtain ⟨ba, hba⟩ := hrz_inl a hrz
            dsimp [evalOne]
            rw [hba]
          dsimp [evalOne]
          cases hga : env.getD a (Sum.inl false) with
          | inl ba =>
            exact hnone_case (Sum.inl (!ba)) (fun _ h => by cases h)
          | inr wa =>
            refine ⟨⟨[⟨GateOp.not, [wa]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
            · intro hrz
              have : ((Sum.inr (8 + gs'.length) : Sum Bool ℕ), some (Gate.mk GateOp.not [wa])).2 = none := by
                have h' := hrz_none hrz
                dsimp [evalOne] at h'
                rw [hga] at h'
                exact h'
              cases this
            · intro g' hg'
              rw [List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact hfg g' hg'
              · exact ⟨Or.inr (Or.inr rfl), by simp⟩
            · intro v hv j hj
              rw [List.mem_append, List.mem_singleton] at hv
              rcases hv with hv | rfl
              · have := hbound v hv j hj
                rw [List.length_append, List.length_singleton]
                omega
              · cases hj
                rw [List.length_append, List.length_singleton]
                omega
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2, hlen1, h0', h9', h10'⟩
  have hcomp_struct : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate),
      11 ≤ env.length →
      env.getD 0 (Sum.inl false) = Sum.inl false →
      env.getD 9 (Sum.inl false) = Sum.inl true →
      env.getD 10 (Sum.inl false) = Sum.inl true →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < 8 + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      (∀ g ∈ gs, fanOK g) →
      let res := compileLoop gs (env, gs')
      (∃ ext, res.2 = gs' ++ ext) ∧
        (∀ g' ∈ res.2, fanOK g') ∧
        (∀ v ∈ res.1, ∀ j, v = Sum.inr j → j < 8 + res.2.length) ∧
        res.2.length + gs.countP readsZero ≤ gs'.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro env gs' _ _ _ _ hbound hfg _
      refine ⟨⟨[], by dsimp [compileLoop]; simp⟩, hfg, hbound, ?_⟩
      change gs'.length + 0 ≤ gs'.length + 0
      exact le_refl _
    | cons g gs ih =>
      intro env gs' hlen h0 h9 h10 hbound hfg hgs
      have hgfan : fanOK g := hgs g List.mem_cons_self
      have hgs_tail : ∀ h ∈ gs, fanOK h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨⟨ext1, hext1, hext1_len⟩, hrz1, hfg1, hbound1, hlen1, h0', h9', h10'⟩ :=
        hcomp_step_props g env gs' hgfan hlen h0 h9 h10 hbound hfg
      obtain ⟨⟨ext2, hext2⟩, hfg2, hbound2, hcnt2⟩ :=
        ih (compileStep (env, gs') g).1 (compileStep (env, gs') g).2 (by omega) h0' h9' h10' hbound1 hfg1 hgs_tail
      have hfold : compileLoop (g :: gs) (env, gs') =
          compileLoop gs ((compileStep (env, gs') g).1, (compileStep (env, gs') g).2) := rfl
      rw [hfold]
      refine ⟨⟨ext1 ++ ext2, by rw [hext2, hext1, List.append_assoc]⟩, hfg2, hbound2, ?_⟩
      rw [List.countP_cons, List.length_cons]
      by_cases hrzg : readsZero g = true
      · simp only [hrzg, ↓reduceIte]
        rw [hrz1 hrzg] at hcnt2 ⊢
        omega
      · simp only [hrzg, Bool.false_eq_true, ↓reduceIte]
        rw [hext1] at hcnt2 ⊢
        rw [List.length_append] at hcnt2
        omega
  have hcomp_step_sem : ∀ (y : Fin 8 → Bool) (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate)
      (w WF : List Bool),
      fanOK g →
      env.length = w.length →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < 8 + gs'.length) →
      (∀ k, k < 8 + (compileStep (env, gs') g).2.length →
        WF.getD k false = (run (compileStep (env, gs') g).2 (List.ofFn y)).getD k false) →
      (∀ m, evalVal WF (env.getD m (Sum.inl false)) = w.getD m false) →
      ∀ m, evalVal WF ((compileStep (env, gs') g).1.getD m (Sum.inl false)) = (step w g).getD m false := by
    intro y g env gs' w WF hgfan hlen hbound hWF hsem m
    cases g
    rename_i op ins
    let st1 := compileStep (env, gs') ⟨op, ins⟩
    by_cases hm : m < w.length
    · have hm' : m < env.length := by omega
      have h1m : st1.1.getD m (Sum.inl false) = env.getD m (Sum.inl false) := by
        dsimp [st1, compileStep]
        cases (evalOne ⟨op, ins⟩ env gs').2 <;> exact List.getD_append _ _ _ _ hm'
      rw [h1m, List.getD_append _ _ _ _ hm]
      exact hsem m
    · by_cases heq : m = w.length
      · subst heq
        have hw1 : (step w ⟨op, ins⟩).getD w.length false = op.eval (ins.map fun i => w.getD i false) :=
          hgetD_append_len w [op.eval (ins.map fun i => w.getD i false)] false
        have hs1 : st1.1.getD env.length (Sum.inl false) = (evalOne ⟨op, ins⟩ env gs').1 := by
          dsimp [st1, compileStep]
          cases (evalOne ⟨op, ins⟩ env gs').2 <;> exact hgetD_append_len env _ _
        change evalVal WF (st1.1.getD w.length (Sum.inl false)) = (step w ⟨op, ins⟩).getD w.length false
        rw [hw1, ← hlen, hs1]
        have hget_bound : ∀ a, ∀ j, env.getD a (Sum.inl false) = Sum.inr j → j < 8 + gs'.length := by
          intro a j ha
          by_cases hlt : a < env.length
          · rw [List.getD_eq_getElem _ _ hlt] at ha
            exact hbound _ (List.getElem_mem hlt) j ha
          · rw [List.getD_eq_default _ _ (by omega)] at ha
            cases ha
        rcases hgfan with ⟨hop, hilen⟩
        rcases hop with rfl | rfl | rfl
        · -- and
          cases ins with
          | nil => rfl
          | cons a t =>
            cases t with
            | nil =>
              dsimp [evalOne]
              rw [hsem a]
              change _ = GateOp.and.eval [w.getD a false]
              cases (w.getD a false) <;> rfl
            | cons b r =>
              have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
              subst hr_nil
              have hsa := hsem a
              have hsb := hsem b
              dsimp [evalOne]
              change _ = (w.getD a false && (w.getD b false && true))
              cases hga : env.getD a (Sum.inl false) <;> cases hgb : env.getD b (Sum.inl false) <;>
                rw [hga] at hsa <;> rw [hgb] at hsb
              · rename_i ba bb
                cases ba <;> cases bb <;> dsimp [evalVal] at hsa hsb ⊢ <;> rw [← hsa, ← hsb] <;> rfl
              · rename_i ba wb
                cases ba <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsa]; rfl
                · rw [← hsa, hsb]; cases (w.getD b false) <;> rfl
              · rename_i wa bb
                cases bb <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsb]; cases (w.getD a false) <;> rfl
                · rw [hsa, ← hsb]; cases (w.getD a false) <;> rfl
              · rename_i wa wb
                have hst1eq : (compileStep (env, gs') ⟨GateOp.and, [a, b]⟩).2 = gs' ++ [⟨GateOp.and, [wa, wb]⟩] := by
                  dsimp [compileStep, evalOne]
                  rw [hga, hgb]
                have hlt1 : 8 + gs'.length < 8 + (compileStep (env, gs') ⟨GateOp.and, [a, b]⟩).2.length := by
                  rw [hst1eq, List.length_append, List.length_singleton]; omega
                have hw0 := hWF (8 + gs'.length) hlt1
                rw [hst1eq, hrun_append] at hw0
                have hlenrun : (run gs' (List.ofFn y)).length = 8 + gs'.length := by
                  rw [hrun_len, List.length_ofFn]
                have hw_eval : (run [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y))).getD (8 + gs'.length) false =
                    ((run gs' (List.ofFn y)).getD wa false && ((run gs' (List.ofFn y)).getD wb false && true)) := by
                  rw [← hlenrun]
                  exact hgetD_append_len (run gs' (List.ofFn y)) _ false
                have hwa_bd := hget_bound a wa hga
                have hwb_bd := hget_bound b wb hgb
                have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                  have hwa1 : WF.getD wa false = (run (compileStep (env, gs') ⟨GateOp.and, [a, b]⟩).2 (List.ofFn y)).getD wa false :=
                    hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwa1
                  have hp := hrun_preserves [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                  rw [hp] at hwa1
                  exact hwa1.symm
                have hwb_eq : (run gs' (List.ofFn y)).getD wb false = WF.getD wb false := by
                  have hwb1 : WF.getD wb false = (run (compileStep (env, gs') ⟨GateOp.and, [a, b]⟩).2 (List.ofFn y)).getD wb false :=
                    hWF wb (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwb1
                  have hp := hrun_preserves [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y)) wb (by rw [hlenrun]; exact hwb_bd)
                  rw [hp] at hwb1
                  exact hwb1.symm
                dsimp [evalVal] at hsa hsb ⊢
                rw [hw0, hw_eval, hwa_eq, hwb_eq, hsa, hsb]
        · -- or
          cases ins with
          | nil => rfl
          | cons a t =>
            cases t with
            | nil =>
              dsimp [evalOne]
              rw [hsem a]
              change _ = GateOp.or.eval [w.getD a false]
              cases (w.getD a false) <;> rfl
            | cons b r =>
              have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
              subst hr_nil
              have hsa := hsem a
              have hsb := hsem b
              dsimp [evalOne]
              change _ = (w.getD a false || (w.getD b false || false))
              cases hga : env.getD a (Sum.inl false) <;> cases hgb : env.getD b (Sum.inl false) <;>
                rw [hga] at hsa <;> rw [hgb] at hsb
              · rename_i ba bb
                cases ba <;> cases bb <;> dsimp [evalVal] at hsa hsb ⊢ <;> rw [← hsa, ← hsb] <;> rfl
              · rename_i ba wb
                cases ba <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsa, hsb]; cases (w.getD b false) <;> rfl
                · rw [← hsa]; rfl
              · rename_i wa bb
                cases bb <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [hsa, ← hsb]; cases (w.getD a false) <;> rfl
                · rw [← hsb]; cases (w.getD a false) <;> rfl
              · rename_i wa wb
                have hst1eq : (compileStep (env, gs') ⟨GateOp.or, [a, b]⟩).2 = gs' ++ [⟨GateOp.or, [wa, wb]⟩] := by
                  dsimp [compileStep, evalOne]
                  rw [hga, hgb]
                have hlt1 : 8 + gs'.length < 8 + (compileStep (env, gs') ⟨GateOp.or, [a, b]⟩).2.length := by
                  rw [hst1eq, List.length_append, List.length_singleton]; omega
                have hw0 := hWF (8 + gs'.length) hlt1
                rw [hst1eq, hrun_append] at hw0
                have hlenrun : (run gs' (List.ofFn y)).length = 8 + gs'.length := by
                  rw [hrun_len, List.length_ofFn]
                have hw_eval : (run [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y))).getD (8 + gs'.length) false =
                    ((run gs' (List.ofFn y)).getD wa false || ((run gs' (List.ofFn y)).getD wb false || false)) := by
                  rw [← hlenrun]
                  exact hgetD_append_len (run gs' (List.ofFn y)) _ false
                have hwa_bd := hget_bound a wa hga
                have hwb_bd := hget_bound b wb hgb
                have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                  have hwa1 : WF.getD wa false = (run (compileStep (env, gs') ⟨GateOp.or, [a, b]⟩).2 (List.ofFn y)).getD wa false :=
                    hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwa1
                  have hp := hrun_preserves [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                  rw [hp] at hwa1
                  exact hwa1.symm
                have hwb_eq : (run gs' (List.ofFn y)).getD wb false = WF.getD wb false := by
                  have hwb1 : WF.getD wb false = (run (compileStep (env, gs') ⟨GateOp.or, [a, b]⟩).2 (List.ofFn y)).getD wb false :=
                    hWF wb (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwb1
                  have hp := hrun_preserves [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y)) wb (by rw [hlenrun]; exact hwb_bd)
                  rw [hp] at hwb1
                  exact hwb1.symm
                dsimp [evalVal] at hsa hsb ⊢
                rw [hw0, hw_eval, hwa_eq, hwb_eq, hsa, hsb]
        · -- not
          cases ins with
          | nil => rfl
          | cons a t =>
            have hsa := hsem a
            dsimp [evalOne]
            change _ = !(w.getD a false)
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              rw [hga] at hsa
              dsimp [evalVal] at hsa ⊢
              rw [hsa]
            | inr wa =>
              rw [hga] at hsa
              have hst1eq : (compileStep (env, gs') ⟨GateOp.not, a :: t⟩).2 = gs' ++ [⟨GateOp.not, [wa]⟩] := by
                dsimp [compileStep, evalOne]
                rw [hga]
              have hlt1 : 8 + gs'.length < 8 + (compileStep (env, gs') ⟨GateOp.not, a :: t⟩).2.length := by
                rw [hst1eq, List.length_append, List.length_singleton]; omega
              have hw0 := hWF (8 + gs'.length) hlt1
              rw [hst1eq, hrun_append] at hw0
              have hlenrun : (run gs' (List.ofFn y)).length = 8 + gs'.length := by
                rw [hrun_len, List.length_ofFn]
              have hw_eval : (run [⟨GateOp.not, [wa]⟩] (run gs' (List.ofFn y))).getD (8 + gs'.length) false =
                  !((run gs' (List.ofFn y)).getD wa false) := by
                rw [← hlenrun]
                exact hgetD_append_len (run gs' (List.ofFn y)) _ false
              have hwa_bd := hget_bound a wa hga
              have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                have hwa1 : WF.getD wa false = (run (compileStep (env, gs') ⟨GateOp.not, a :: t⟩).2 (List.ofFn y)).getD wa false :=
                  hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                rw [hst1eq, hrun_append] at hwa1
                have hp := hrun_preserves [⟨GateOp.not, [wa]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                rw [hp] at hwa1
                exact hwa1.symm
              dsimp [evalVal] at hsa ⊢
              rw [hw0, hw_eval, hwa_eq, hsa]
      · have hgt1 : st1.1.length ≤ m := by
          dsimp [st1, compileStep]
          cases (evalOne ⟨op, ins⟩ env gs').2 <;> simp <;> omega
        have hgt2 : (step w ⟨op, ins⟩).length ≤ m := by
          rw [hstep_len]
          omega
        change evalVal WF (st1.1.getD m (Sum.inl false)) = (step w ⟨op, ins⟩).getD m false
        rw [List.getD_eq_default _ _ hgt1, List.getD_eq_default _ _ hgt2]
  have hcomp_sem : ∀ (y : Fin 8 → Bool) (gs : List Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate) (w : List Bool),
      11 ≤ env.length →
      env.length = w.length →
      env.getD 0 (Sum.inl false) = Sum.inl false →
      env.getD 9 (Sum.inl false) = Sum.inl true →
      env.getD 10 (Sum.inl false) = Sum.inl true →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < 8 + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      (∀ g ∈ gs, fanOK g) →
      (∀ m, evalVal (run (compileLoop gs (env, gs')).2 (List.ofFn y)) (env.getD m (Sum.inl false)) = w.getD m false) →
      ∀ m, evalVal (run (compileLoop gs (env, gs')).2 (List.ofFn y)) ((compileLoop gs (env, gs')).1.getD m (Sum.inl false)) =
        (run gs w).getD m false := by
    intro y gs
    induction gs with
    | nil =>
      intro env gs' w _ _ _ _ _ _ _ _ hsem m
      exact hsem m
    | cons g gs ih =>
      intro env gs' w hlen hwl h0 h9 h10 hbound hfg hgs hsem m
      have hgfan : fanOK g := hgs g List.mem_cons_self
      have hgs_tail : ∀ h ∈ gs, fanOK h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨_, _, hfg1, hbound1, hlen1, h0', h9', h10'⟩ :=
        hcomp_step_props g env gs' hgfan hlen h0 h9 h10 hbound hfg
      let st1 := compileStep (env, gs') g
      have hstr_tail := hcomp_struct gs st1.1 st1.2 (by dsimp [st1]; omega) h0' h9' h10' hbound1 hfg1 hgs_tail
      obtain ⟨ext2, hext2⟩ := hstr_tail.1
      have hfold : compileLoop (g :: gs) (env, gs') = compileLoop gs st1 := rfl
      rw [hfold]
      let WF := run (compileLoop gs st1).2 (List.ofFn y)
      have hWF_pres : ∀ k, k < 8 + st1.2.length → WF.getD k false = (run st1.2 (List.ofFn y)).getD k false := by
        intro k hk
        change (run (compileLoop gs st1).2 (List.ofFn y)).getD k false = _
        rw [hext2, hrun_append]
        exact hrun_preserves ext2 (run st1.2 (List.ofFn y)) k (by rw [hrun_len, List.length_ofFn]; exact hk)
      have hsem1 : ∀ k, evalVal WF (st1.1.getD k (Sum.inl false)) = (step w g).getD k false :=
        hcomp_step_sem y g env gs' w WF hgfan hwl hbound hWF_pres hsem
      exact ih st1.1 st1.2 (step w g) (by change st1.1.length = env.length + 1 at hlen1; omega)
        (by rw [hstep_len, ← hwl]; exact hlen1)
        h0' h9' h10' hbound1 hfg1 hgs_tail hsem1 m
  let env0 : List (Sum Bool ℕ) :=
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl true, Sum.inl true]
  let lift : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y j =>
    if h : j.val = 0 then false else y ⟨j.val - 1, by omega⟩
  have hlift_f : ∀ y : Fin 8 → Bool, fP9 (lift y) = fH y := by
    intro y
    have hc : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
        (false && b0 || b0 && b1 || b1 && b2 || b2 && b3 || b3 && false || false && b4 ||
         b0 && b5 || b1 && b6 || b2 && b7 || b4 && b6 || b5 && b7 || b7 && b4) =
        (b0 && b1 || b1 && b2 || b2 && b3 || b0 && b5 || b1 && b6 || b2 && b7 ||
         b4 && b6 || b5 && b7 || b7 && b4) := by
      decide
    exact hc (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  have henv0_bound : ∀ v ∈ env0, ∀ j, v = Sum.inr j → j < 8 + ([] : List Gate).length := by
    intro v hv j hj
    subst hj
    simp only [env0, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h | h | h | h | h | h | h
    · cases h
    · cases h; decide
    · cases h; decide
    · cases h; decide
    · cases h; decide
    · cases h; decide
    · cases h; decide
    · cases h; decide
    · cases h; decide
    · cases h
    · cases h
  have hCstr := hcomp_struct C.gates env0 [] (by decide) rfl rfl rfl henv0_bound (fun _ h => by cases h) hfan
  let resC := compileLoop C.gates (env0, [])
  have hsem0 : ∀ (y : Fin 8 → Bool) (m : ℕ),
      evalVal (run resC.2 (List.ofFn y)) (env0.getD m (Sum.inl false)) = (initW (lift y)).getD m false := by
    intro y m
    by_cases hm : m < 11
    · have hpres8 : ∀ k : Fin 8, (run resC.2 (List.ofFn y)).getD k.val false = y k := by
        intro k
        have hlt : k.val < (List.ofFn y).length := by rw [List.length_ofFn]; exact k.isLt
        rw [hrun_preserves resC.2 (List.ofFn y) k.val hlt]
        exact hgetFn8 y k
      interval_cases m
      · exact (hinit_0 (lift y)).symm
      · exact (hpres8 0).trans (hgetFn (lift y) _ 1).symm
      · exact (hpres8 1).trans (hgetFn (lift y) _ 2).symm
      · exact (hpres8 2).trans (hgetFn (lift y) _ 3).symm
      · exact (hpres8 3).trans (hgetFn (lift y) _ 4).symm
      · exact (hpres8 4).trans (hgetFn (lift y) _ 5).symm
      · exact (hpres8 5).trans (hgetFn (lift y) _ 6).symm
      · exact (hpres8 6).trans (hgetFn (lift y) _ 7).symm
      · exact (hpres8 7).trans (hgetFn (lift y) _ 8).symm
      · exact (hinit_9 (lift y)).symm
      · exact (hinit_10 (lift y)).symm
    · rw [List.getD_eq_default env0 _ (by change 11 ≤ m; omega),
        List.getD_eq_default (initW (lift y)) _ (by rw [hinit_len]; omega)]
  have hCsem : ∀ (y : Fin 8 → Bool) (m : ℕ),
      evalVal (run resC.2 (List.ofFn y)) (resC.1.getD m (Sum.inl false)) =
        (run C.gates (initW (lift y))).getD m false :=
    fun y => hcomp_sem y C.gates env0 [] (initW (lift y)) (by decide) (by rw [hinit_len]; rfl)
      rfl rfl rfl henv0_bound (fun _ h => by cases h) hfan (hsem0 y)
  have hk : C.gates.countP readsZero ≤ 1 := by
    cases hout_val : resC.1.getD C.output (Sum.inl false) with
    | inl b =>
      have hconst : ∀ y : Fin 8 → Bool, fH y = b := by
        intro y
        have h1y := hCsem y C.output
        rw [hout_val] at h1y
        have h2y := hagree (lift y)
        rw [heval_run] at h2y
        rw [← hlift_f y, ← h2y, ← h1y]
      have hf0 := hconst (fun _ => false)
      have hf1 := hconst (fun j => decide (j = 0 ∨ j = 1))
      have hn : fH (fun _ => false) ≠ fH (fun j => decide (j = 0 ∨ j = 1)) := by decide
      exact False.elim (hn (hf0.trans hf1.symm))
    | inr outW =>
      let C' : Circuit := ⟨resC.2, outW⟩
      have hfan' : FanInTwo C' := hCstr.2.1
      have hge12 : 12 ≤ resC.2.length := by
        refine Classical.byContradiction fun hlt => ?_
        have hle : C'.size ≤ 11 := by change resC.2.length ≤ 11; omega
        obtain ⟨y, hy⟩ := h2 C' hfan' hle
        apply hy
        have h1y := hCsem y C.output
        rw [hout_val] at h1y
        have h2y := hagree (lift y)
        rw [heval_run] at h2y
        change (run resC.2 (List.ofFn y)).getD outW false = fH y
        exact h1y.trans (h2y.trans (hlift_f y))
      have hcnt := hCstr.2.2.2
      change resC.2.length + C.gates.countP readsZero ≤ ([] : List Gate).length + C.gates.length at hcnt
      rw [List.length_nil, Nat.zero_add] at hcnt
      rw [hsz_len] at hs
      omega
  -- Part B: C.output ∉ {0, 9, 10}
  have hout_ne0 : C.output ≠ 0 := by
    intro h
    have hx := hagree (fun j => decide (j = 0))
    rw [heval_run, h, hrun_preserves _ _ 0 (by rw [hinit_len]; omega), hinit_0] at hx
    have hf : fP9 (fun j => decide (j = 0)) = false := by decide
    rw [hf] at hx
    cases hx
  have hout_ne9 : C.output ≠ 9 := by
    intro h
    have hx := hagree (fun _ => false)
    rw [heval_run, h, hrun_preserves _ _ 9 (by rw [hinit_len]; omega), hinit_9] at hx
    have hf : fP9 (fun _ => false) = false := by decide
    rw [hf] at hx
    cases hx
  have hout_ne10 : C.output ≠ 10 := by
    intro h
    have hx := hagree (fun _ => false)
    rw [heval_run, h, hrun_preserves _ _ 10 (by rw [hinit_len]; omega), hinit_10] at hx
    have hf : fP9 (fun _ => false) = false := by decide
    rw [hf] at hx
    cases hx
  -- Part C: no gate reading wire 10 implies contradiction via h1
  let shift : ℕ → ℕ := fun w => if w < 10 then w else w - 1
  have no_wire10_contra : ∀ (D0 : Circuit),
      FanInTwo D0 → D0.size ≤ 13 → D0.output ≠ 10 →
      (∀ g ∈ D0.gates, 10 ∉ effInputs g) →
      (∀ x : Fin 9 → Bool, D0.eval (initW x) = fP9 x) → False := by
    intro D0 hD0fan hD0sz hD0out hD0no10 hD0eq
    let mapGate : Gate → Gate := fun g => ⟨g.op, (effInputs g).map shift⟩
    let D : Circuit := ⟨⟨GateOp.not, [0]⟩ :: D0.gates.map mapGate, shift D0.output⟩
    have hDfan : FanInTwo D := by
      intro g hg
      change g ∈ Gate.mk GateOp.not [0] :: D0.gates.map mapGate at hg
      rcases List.mem_cons.mp hg with rfl | hmem
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hmem
        have hg0f := hD0fan g0 hg0
        exact ⟨hg0f.1, by simp only [mapGate, List.length_map]; exact heff_len g0 hg0f.2⟩
    have hDsz : D.size ≤ 14 := by
      change (Gate.mk GateOp.not [0] :: D0.gates.map mapGate).length ≤ 14
      rw [List.length_cons, List.length_map]
      rw [hsz_len] at hD0sz
      omega
    have hsim : ∀ (gs : List Gate) (W0 W1 : List Bool),
        W0.length = W1.length + 1 → 10 ≤ W1.length →
        (∀ g ∈ gs, 10 ∉ effInputs g) →
        (∀ m, m ≠ 10 → W1.getD (shift m) false = W0.getD m false) →
        ∀ m, m ≠ 10 → (run (gs.map mapGate) W1).getD (shift m) false = (run gs W0).getD m false := by
      intro gs
      induction gs with
      | nil =>
        intro W0 W1 _ _ _ hW m hm
        exact hW m hm
      | cons g gs ih =>
        intro W0 W1 hlen h10 hno hW m hm
        have hgno : 10 ∉ effInputs g := hno g List.mem_cons_self
        have hgsno : ∀ h ∈ gs, 10 ∉ effInputs h := fun h hh => hno h (List.mem_cons_of_mem _ hh)
        have hbit : (mapGate g).op.eval ((mapGate g).inputs.map fun i => W1.getD i false) =
            g.op.eval (g.inputs.map fun i => W0.getD i false) := by
          rw [heff g W0]
          change g.op.eval (((effInputs g).map shift).map fun i => W1.getD i false) =
            g.op.eval ((effInputs g).map fun i => W0.getD i false)
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hW a (fun h10eq => hgno (h10eq ▸ ha))
        have hstep_inv : ∀ k, k ≠ 10 → (step W1 (mapGate g)).getD (shift k) false = (step W0 g).getD k false := by
          intro k hk
          by_cases hklt : k < W0.length
          · have hsk : shift k < W1.length := by dsimp [shift]; split_ifs <;> omega
            rw [List.getD_append _ _ _ _ hsk, List.getD_append _ _ _ _ hklt]
            exact hW k hk
          · by_cases hkeq : k = W0.length
            · subst hkeq
              have hsk : shift W0.length = W1.length := by dsimp [shift]; split_ifs <;> omega
              rw [hsk]
              change (W1 ++ [_]).getD W1.length false = (W0 ++ [_]).getD W0.length false
              rw [hgetD_append_len, hgetD_append_len]
              exact hbit
            · have h1 : (step W1 (mapGate g)).length ≤ shift k := by
                rw [hstep_len]
                dsimp [shift]; split_ifs <;> omega
              have h2 : (step W0 g).length ≤ k := by
                rw [hstep_len]
                omega
              rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
        rw [List.map_cons, hrun_cons, hrun_cons]
        apply ih (step W0 g) (step W1 (mapGate g))
          (by rw [hstep_len, hstep_len, hlen]) (by rw [hstep_len]; omega) hgsno hstep_inv m hm
    obtain ⟨x, hx⟩ := h1 D hDfan hDsz
    apply hx
    rw [heval_run, hrun_cons]
    have hW1_init : step (List.ofFn x) ⟨GateOp.not, [0]⟩ = List.ofFn x ++ [!x 0] := by
      dsimp [step]
      rw [List.map_cons, List.map_nil]
      change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
      have hi0 : 0 < (List.ofFn x).length := by rw [List.length_ofFn]; decide
      rw [List.getD_eq_getElem _ _ hi0, List.getElem_ofFn]
      rfl
    have hW1_len : (step (List.ofFn x) ⟨GateOp.not, [0]⟩).length = 10 := by
      rw [hW1_init, List.length_append, List.length_ofFn, List.length_singleton]
    have hsimD := hsim D0.gates (initW x) (step (List.ofFn x) ⟨GateOp.not, [0]⟩)
      (by rw [hinit_len, hW1_len])
      (by rw [hW1_len])
      hD0no10
      (by
        intro m hm
        rw [hW1_init]
        by_cases hm9 : m < 9
        · have hsm : shift m = m := by dsimp [shift]; split_ifs <;> omega
          rw [hsm]
          exact (hgetFn x [!x 0] ⟨m, hm9⟩).trans (hgetFn x _ ⟨m, hm9⟩).symm
        · by_cases hm9eq : m = 9
          · subst hm9eq
            have hsm : shift 9 = 9 := by decide
            rw [hsm]
            exact (hget9 x).trans (hinit_9 x).symm
          · have h11 : 11 ≤ m := by omega
            have hsm : shift m = m - 1 := by dsimp [shift]; split_ifs <;> omega
            rw [hsm, List.getD_eq_default _ _ (by rw [List.length_append, List.length_ofFn, List.length_singleton]; omega),
              List.getD_eq_default (initW x) _ (by rw [hinit_len]; omega)])
      D0.output hD0out
    change (run (D0.gates.map mapGate) (step (List.ofFn x) ⟨GateOp.not, [0]⟩)).getD (shift D0.output) false = _
    rw [hsimD]
    exact hD0eq x
  -- Part D: if some gate reads wire 10, split at it and analyze 3 subcases
  by_cases hno10 : ∀ g ∈ C.gates, 10 ∉ effInputs g
  · exact no_wire10_contra C hfan hs hout_ne10 hno10 hagree
  · have hex10 : ∃ pre gS post, C.gates = pre ++ gS :: post ∧ 10 ∈ effInputs gS := by
      have haux : ∀ (gs : List Gate), (¬ ∀ g ∈ gs, 10 ∉ effInputs g) →
          ∃ pre gS post, gs = pre ++ gS :: post ∧ 10 ∈ effInputs gS := by
        intro gs
        induction gs with
        | nil => intro h; exact False.elim (h fun _ hg => by cases hg)
        | cons g gs ih =>
          intro h
          by_cases hg10 : 10 ∈ effInputs g
          · exact ⟨[], g, gs, rfl, hg10⟩
          · obtain ⟨pre, gS, post, hsplit, hgS⟩ := ih (fun all => h fun a ha => by
              rcases List.mem_cons.mp ha with rfl | ha'
              · exact hg10
              · exact all a ha')
            exact ⟨g :: pre, gS, post, by rw [hsplit]; rfl, hgS⟩
      exact haux C.gates hno10
    obtain ⟨pre, gS, post, hsplit, hgS10⟩ := hex10
    have hpre_noZ : ∀ g ∈ pre, readsZero g = false := by
      have hcnt : (pre ++ gS :: post).countP readsZero ≤ 1 := hsplit ▸ hk
      have hrzS : readsZero gS = true := by
        change (effInputs gS).any isZ = true
        exact List.any_eq_true.mpr ⟨10, hgS10, rfl⟩
      rw [List.countP_append, List.countP_cons] at hcnt
      simp only [hrzS, ↓reduceIte] at hcnt
      have hp0 : pre.countP readsZero = 0 := by omega
      intro g hg
      cases hrg : readsZero g
      · rfl
      · have hpos : 0 < pre.countP readsZero := List.countP_pos_iff.mpr ⟨g, hg, hrg⟩
        omega
    have hpost_noZ : ∀ g ∈ post, readsZero g = false := by
      have hcnt : (pre ++ gS :: post).countP readsZero ≤ 1 := hsplit ▸ hk
      have hrzS : readsZero gS = true := by
        change (effInputs gS).any isZ = true
        exact List.any_eq_true.mpr ⟨10, hgS10, rfl⟩
      rw [List.countP_append, List.countP_cons] at hcnt
      simp only [hrzS, ↓reduceIte] at hcnt
      have hp0 : post.countP readsZero = 0 := by omega
      intro g hg
      cases hrg : readsZero g
      · rfl
      · have hpos : 0 < post.countP readsZero := List.countP_pos_iff.mpr ⟨g, hg, hrg⟩
        omega
    have hnoZ_mem : ∀ g, readsZero g = false → ∀ a ∈ effInputs g, a ≠ 0 ∧ a ≠ 9 ∧ a ≠ 10 := by
      intro g hrz a ha
      have hna : isZ a = false := by
        cases ha_val : isZ a
        · rfl
        · have : readsZero g = true := List.any_eq_true.mpr ⟨a, ha, ha_val⟩
          rw [this] at hrz
          cases hrz
      change decide (a = 0 ∨ a = 9 ∨ a = 10) = false at hna
      rw [decide_eq_false_iff_not] at hna
      exact ⟨fun h => hna (Or.inl h), fun h => hna (Or.inr (Or.inl h)), fun h => hna (Or.inr (Or.inr h))⟩
    have hrun_noZ : ∀ (gs : List Gate) (W1 W2 : List Bool),
        (∀ g ∈ gs, readsZero g = false) →
        W1.length = W2.length → 11 ≤ W1.length →
        (∀ m, m ≠ 0 → m ≠ 9 → m ≠ 10 → W1.getD m false = W2.getD m false) →
        (run gs W1).length = (run gs W2).length ∧
          ∀ m, m ≠ 0 → m ≠ 9 → m ≠ 10 → (run gs W1).getD m false = (run gs W2).getD m false := by
      intro gs
      induction gs with
      | nil =>
        intro W1 W2 _ hlen _ hW
        exact ⟨hlen, hW⟩
      | cons g gs ih =>
        intro W1 W2 hno hlen h11 hW
        have hg := hno g List.mem_cons_self
        have hgs := fun h hh => hno h (List.mem_cons_of_mem _ hh)
        have hbit : g.op.eval (g.inputs.map fun i => W1.getD i false) =
            g.op.eval (g.inputs.map fun i => W2.getD i false) := by
          rw [heff g W1, heff g W2]
          congr 1
          apply List.map_congr_left
          intro a ha
          obtain ⟨ha0, ha9, ha10⟩ := hnoZ_mem g hg a ha
          exact hW a ha0 ha9 ha10
        rw [hrun_cons, hrun_cons]
        apply ih (step W1 g) (step W2 g) hgs
          (by rw [hstep_len, hstep_len, hlen]) (by rw [hstep_len]; omega)
        intro m hm0 hm9 hm10
        by_cases hmlt : m < W1.length
        · have hmlt2 : m < W2.length := by omega
          rw [List.getD_append _ _ _ _ hmlt, List.getD_append _ _ _ _ hmlt2]
          exact hW m hm0 hm9 hm10
        · by_cases hmeq : m = W1.length
          · subst hmeq
            change (W1 ++ [_]).getD W1.length false = (W2 ++ [_]).getD W1.length false
            rw [hgetD_append_len, hlen, hgetD_append_len]
            exact hbit
          · have h1 : (step W1 g).length ≤ m := by rw [hstep_len]; omega
            have h2 : (step W2 g).length ≤ m := by rw [hstep_len]; omega
            rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
    have hpre_eq : ∀ (xF xT : Fin 9 → Bool),
        (∀ i : Fin 9, i ≠ 0 → xF i = xT i) →
        (run pre (initW xF)).length = (run pre (initW xT)).length ∧
          ∀ m, m ≠ 0 → m ≠ 9 → m ≠ 10 → (run pre (initW xF)).getD m false = (run pre (initW xT)).getD m false := by
      intro xF xT hxi
      apply hrun_noZ pre (initW xF) (initW xT) hpre_noZ (by rw [hinit_len, hinit_len]) (by rw [hinit_len])
      intro m hm0 hm9 hm10
      by_cases hm9lt : m < 9
      · have hne0 : (⟨m, hm9lt⟩ : Fin 9) ≠ 0 := fun h => hm0 (congrArg Fin.val h)
        exact (hgetFn xF _ ⟨m, hm9lt⟩).trans ((hxi _ hne0).trans (hgetFn xT _ ⟨m, hm9lt⟩).symm)
      · have h11 : 11 ≤ m := by omega
        rw [List.getD_eq_default _ _ (by rw [hinit_len]; omega),
          List.getD_eq_default _ _ (by rw [hinit_len]; omega)]
    have agree_of_same_gstar : ∀ (xF xT : Fin 9 → Bool),
        (∀ i : Fin 9, i ≠ 0 → xF i = xT i) →
        gS.op.eval (gS.inputs.map fun w => (run pre (initW xF)).getD w false) =
          gS.op.eval (gS.inputs.map fun w => (run pre (initW xT)).getD w false) →
        fP9 xF ≠ fP9 xT → False := by
      intro xF xT hxi hgSeval hfdiff
      obtain ⟨hpreLen, hpreW⟩ := hpre_eq xF xT hxi
      have hstep_eq : ∀ m, m ≠ 0 → m ≠ 9 → m ≠ 10 →
          (step (run pre (initW xF)) gS).getD m false =
            (step (run pre (initW xT)) gS).getD m false := by
        intro m hm0 hm9 hm10
        by_cases hmlt : m < (run pre (initW xF)).length
        · have hmlt2 : m < (run pre (initW xT)).length := by omega
          rw [List.getD_append _ _ _ _ hmlt, List.getD_append _ _ _ _ hmlt2]
          exact hpreW m hm0 hm9 hm10
        · by_cases hmeq : m = (run pre (initW xF)).length
          · subst hmeq
            change (run pre (initW xF) ++ [_]).getD (run pre (initW xF)).length false =
              (run pre (initW xT) ++ [_]).getD (run pre (initW xF)).length false
            rw [hgetD_append_len, hpreLen, hgetD_append_len]
            exact hgSeval
          · have h1 : (step (run pre (initW xF)) gS).length ≤ m := by rw [hstep_len]; omega
            have h2 : (step (run pre (initW xT)) gS).length ≤ m := by rw [hstep_len]; omega
            rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
      have hpost := hrun_noZ post (step (run pre (initW xF)) gS) (step (run pre (initW xT)) gS)
        hpost_noZ (by rw [hstep_len, hstep_len, hpreLen]) (by rw [hstep_len, hrun_len, hinit_len]; omega) hstep_eq
      have hCeq : C.eval (initW xF) = C.eval (initW xT) := by
        rw [heval_run, heval_run, hsplit, hrun_append, hrun_append, hrun_cons, hrun_cons]
        exact hpost.2 C.output hout_ne0 hout_ne9 hout_ne10
      apply hfdiff
      rw [← hagree xF, ← hagree xT]
      exact hCeq
    have hgSfan : fanOK gS := hfan gS (by rw [hsplit]; simp)
    -- Test pair (pF, pT) where x idx = true on both and fP9 pF ≠ fP9 pT
    let vExtra : Fin 9 := if idx = 2 then 4 else if idx = 3 then 1 else if idx = 6 then 4 else idx
    let pF : Fin 9 → Bool := fun j => decide (j = idx ∨ j = vExtra)
    let pT : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = idx ∨ j = vExtra)
    have hp_agree : ∀ i : Fin 9, i ≠ 0 → pF i = pT i := by
      intro i hi
      dsimp [pF, pT]
      simp [hi]
    have hp_idx : pF idx = true ∧ pT idx = true := by
      rcases hidxMem with rfl | rfl | rfl | rfl | rfl <;> decide
    have hp_f : fP9 pF ≠ fP9 pT := by
      rcases hidxMem with rfl | rfl | rfl | rfl | rfl <;> decide
    by_cases h0gS : 0 ∈ effInputs gS
    · -- Subcase 2: 0 ∈ effInputs gS and 10 ∈ effInputs gS
      have hop2 : gS.op = GateOp.and ∨ gS.op = GateOp.or := by
        rcases hgSfan.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          cases hi : gS.inputs with
          | nil => simp [effInputs, h, hi] at h0gS
          | cons a t =>
            simp [effInputs, h, hi] at h0gS hgS10
            omega
      have hpair : gS.inputs = [0, 10] ∨ gS.inputs = [10, 0] := by
        have heff_eq : effInputs gS = gS.inputs := by
          rcases hop2 with h | h <;> simp [effInputs, h]
        rw [heff_eq] at h0gS hgS10
        cases hi : gS.inputs with
        | nil => rw [hi] at h0gS; cases h0gS
        | cons a t =>
          cases t with
          | nil =>
            rw [hi] at h0gS hgS10
            simp only [List.mem_singleton] at h0gS hgS10
            omega
          | cons b r =>
            have hr : r = [] := by
              have hl := hgSfan.2
              rw [hi] at hl
              cases r with
              | nil => rfl
              | cons _ _ => simp at hl
            subst hr
            rw [hi] at h0gS hgS10
            have hcases : (a = 0 ∧ b = 10) ∨ (a = 10 ∧ b = 0) := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h0gS hgS10
              omega
            rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr rfl
      have hpre0 : ∀ x : Fin 9 → Bool, (run pre (initW x)).getD 0 false = x 0 := fun x =>
        (hrun_preserves pre (initW x) 0 (by rw [hinit_len]; omega)).trans (hinit_0 x)
      have hpre10 : ∀ x : Fin 9 → Bool, (run pre (initW x)).getD 10 false = (!x 0 || x idx) := fun x =>
        (hrun_preserves pre (initW x) 10 (by rw [hinit_len]; omega)).trans (hinit_10 x)
      rcases hop2 with hop | hop
      · -- AND(0, 10) = x0 && (!x0 || x idx) = x0 && x idx
        let otherV : Fin 9 := if idx = 1 then 4 else 1
        let qF : Fin 9 → Bool := fun j => decide (j = otherV)
        let qT : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = otherV)
        have hq_agree : ∀ i : Fin 9, i ≠ 0 → qF i = qT i := by
          intro i hi; dsimp [qF, qT]; simp [hi]
        have hq_idx : qF idx = false ∧ qT idx = false := by
          rcases hidxMem with rfl | rfl | rfl | rfl | rfl <;> decide
        have hq_f : fP9 qF ≠ fP9 qT := by
          rcases hidxMem with rfl | rfl | rfl | rfl | rfl <;> decide
        apply agree_of_same_gstar qF qT hq_agree _ hq_f
        have hboth_false : ∀ (x : Fin 9 → Bool), x idx = false →
            gS.op.eval (gS.inputs.map fun w => (run pre (initW x)).getD w false) = false := by
          intro x hxf
          rcases hpair with hp | hp
          · rw [hop, hp, List.map_cons, List.map_cons, List.map_nil]
            change ((run pre (initW x)).getD 0 false && ((run pre (initW x)).getD 10 false && true)) = false
            rw [hpre0 x, hpre10 x, hxf]
            cases x 0 <;> rfl
          · rw [hop, hp, List.map_cons, List.map_cons, List.map_nil]
            change ((run pre (initW x)).getD 10 false && ((run pre (initW x)).getD 0 false && true)) = false
            rw [hpre0 x, hpre10 x, hxf]
            cases x 0 <;> rfl
        exact (hboth_false qF hq_idx.1).trans (hboth_false qT hq_idx.2).symm
      · -- OR(0, 10) = x0 || (!x0 || x idx) = true
        let qF : Fin 9 → Bool := fun j => decide (j = 1)
        let qT : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 1)
        have hq_agree : ∀ i : Fin 9, i ≠ 0 → qF i = qT i := by
          intro i hi; dsimp [qF, qT]; simp [hi]
        have hq_f : fP9 qF ≠ fP9 qT := by decide
        apply agree_of_same_gstar qF qT hq_agree _ hq_f
        have hboth_true : ∀ (x : Fin 9 → Bool),
            gS.op.eval (gS.inputs.map fun w => (run pre (initW x)).getD w false) = true := by
          intro x
          rcases hpair with hp | hp
          · rw [hop, hp, List.map_cons, List.map_cons, List.map_nil]
            change ((run pre (initW x)).getD 0 false || ((run pre (initW x)).getD 10 false || false)) = true
            rw [hpre0 x, hpre10 x]
            cases x 0 <;> cases x idx <;> rfl
          · rw [hop, hp, List.map_cons, List.map_cons, List.map_nil]
            change ((run pre (initW x)).getD 10 false || ((run pre (initW x)).getD 0 false || false)) = true
            rw [hpre0 x, hpre10 x]
            cases x 0 <;> cases x idx <;> rfl
        exact (hboth_true qF).trans (hboth_true qT).symm
    · by_cases h9gS : 9 ∈ effInputs gS
      · -- Subcase 3: 9 ∈ effInputs gS and 10 ∈ effInputs gS
        have hop2 : gS.op = GateOp.and ∨ gS.op = GateOp.or := by
          rcases hgSfan.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            cases hi : gS.inputs with
            | nil => simp [effInputs, h, hi] at h9gS
            | cons a t =>
              simp [effInputs, h, hi] at h9gS hgS10
              omega
        have hpair : gS.inputs = [9, 10] ∨ gS.inputs = [10, 9] := by
          have heff_eq : effInputs gS = gS.inputs := by
            rcases hop2 with h | h <;> simp [effInputs, h]
          rw [heff_eq] at h9gS hgS10
          cases hi : gS.inputs with
          | nil => rw [hi] at h9gS; cases h9gS
          | cons a t =>
            cases t with
            | nil =>
              rw [hi] at h9gS hgS10
              simp only [List.mem_singleton] at h9gS hgS10
              omega
            | cons b r =>
              have hr : r = [] := by
                have hl := hgSfan.2
                rw [hi] at hl
                cases r with
                | nil => rfl
                | cons _ _ => simp at hl
              subst hr
              rw [hi] at h9gS hgS10
              have hcases : (a = 9 ∧ b = 10) ∨ (a = 10 ∧ b = 9) := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h9gS hgS10
                omega
              rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl rfl
              · exact Or.inr rfl
        have hpre9 : ∀ x : Fin 9 → Bool, (run pre (initW x)).getD 9 false = !x 0 := fun x =>
          (hrun_preserves pre (initW x) 9 (by rw [hinit_len]; omega)).trans (hinit_9 x)
        have hpre10 : ∀ x : Fin 9 → Bool, (run pre (initW x)).getD 10 false = (!x 0 || x idx) := fun x =>
          (hrun_preserves pre (initW x) 10 (by rw [hinit_len]; omega)).trans (hinit_10 x)
        rcases hop2 with hop | hop
        · -- AND(9, 10) = !x0 && (!x0 || x idx) = !x0 = AND(9, 9)
          let gAlt : Gate := ⟨GateOp.and, [9, 9]⟩
          let D0 : Circuit := ⟨pre ++ gAlt :: post, C.output⟩
          have hD0fan : FanInTwo D0 := by
            intro g hg
            change g ∈ pre ++ gAlt :: post at hg
            rw [List.mem_append, List.mem_cons] at hg
            rcases hg with hgp | rfl | hgq
            · exact hfan g (by rw [hsplit]; simp [hgp])
            · exact ⟨Or.inl rfl, by decide⟩
            · exact hfan g (by rw [hsplit]; simp [hgq])
          have hD0sz : D0.size ≤ 13 := by
            change (pre ++ gAlt :: post).length ≤ 13
            rw [hsz_len, hsplit] at hs
            rw [List.length_append, List.length_cons] at hs ⊢
            exact hs
          have hD0no10 : ∀ g ∈ D0.gates, 10 ∉ effInputs g := by
            intro g hg
            change g ∈ pre ++ gAlt :: post at hg
            rw [List.mem_append, List.mem_cons] at hg
            rcases hg with hgp | rfl | hgq
            · exact fun h10 => (hnoZ_mem g (hpre_noZ g hgp) 10 h10).2.2 rfl
            · decide
            · exact fun h10 => (hnoZ_mem g (hpost_noZ g hgq) 10 h10).2.2 rfl
          have hD0eq : ∀ x : Fin 9 → Bool, D0.eval (initW x) = fP9 x := by
            intro x
            rw [heval_run, show D0.gates = pre ++ gAlt :: post from rfl, hrun_append, hrun_cons]
            have hstepAlt : step (run pre (initW x)) gAlt = step (run pre (initW x)) gS := by
              dsimp [step]
              congr 2
              rw [hop]
              have hvalAlt : GateOp.and.eval (gAlt.inputs.map fun w => (run pre (initW x)).getD w false) = !x 0 := by
                change ((run pre (initW x)).getD 9 false && ((run pre (initW x)).getD 9 false && true)) = !x 0
                rw [hpre9 x]
                cases x 0 <;> rfl
              have hvalS : GateOp.and.eval (gS.inputs.map fun w => (run pre (initW x)).getD w false) = !x 0 := by
                rcases hpair with hp | hp
                · rw [hp]
                  change ((run pre (initW x)).getD 9 false && ((run pre (initW x)).getD 10 false && true)) = !x 0
                  rw [hpre9 x, hpre10 x]
                  cases x 0 <;> cases x idx <;> rfl
                · rw [hp]
                  change ((run pre (initW x)).getD 10 false && ((run pre (initW x)).getD 9 false && true)) = !x 0
                  rw [hpre9 x, hpre10 x]
                  cases x 0 <;> cases x idx <;> rfl
              exact hvalAlt.trans hvalS.symm
            rw [hstepAlt, ← hrun_cons, ← hrun_append, ← hsplit, ← heval_run]
            exact hagree x
          exact no_wire10_contra D0 hD0fan hD0sz hout_ne10 hD0no10 hD0eq
        · -- OR(9, 10) = !x0 || (!x0 || x idx) = true when x idx = true
          apply agree_of_same_gstar pF pT hp_agree _ hp_f
          have hboth_true : ∀ (x : Fin 9 → Bool), x idx = true →
              gS.op.eval (gS.inputs.map fun w => (run pre (initW x)).getD w false) = true := by
            intro x hxt
            rcases hpair with hp | hp
            · rw [hop, hp]
              change ((run pre (initW x)).getD 9 false || ((run pre (initW x)).getD 10 false || false)) = true
              rw [hpre9 x, hpre10 x, hxt]
              cases x 0 <;> rfl
            · rw [hop, hp]
              change ((run pre (initW x)).getD 10 false || ((run pre (initW x)).getD 9 false || false)) = true
              rw [hpre9 x, hpre10 x, hxt]
              cases x 0 <;> rfl
          exact (hboth_true pF hp_idx.1).trans (hboth_true pT hp_idx.2).symm
      · -- Subcase 1: 0 ∉ effInputs gS ∧ 9 ∉ effInputs gS
        apply agree_of_same_gstar pF pT hp_agree _ hp_f
        rw [heff gS, heff gS]
        congr 1
        apply List.map_congr_left
        intro a ha
        by_cases ha10 : a = 10
        · subst ha10
          have hpF10 : (run pre (initW pF)).getD 10 false = true := by
            rw [hrun_preserves pre (initW pF) 10 (by rw [hinit_len]; omega), hinit_10 pF, hp_idx.1]
            cases pF 0 <;> rfl
          have hpT10 : (run pre (initW pT)).getD 10 false = true := by
            rw [hrun_preserves pre (initW pT) 10 (by rw [hinit_len]; omega), hinit_10 pT, hp_idx.2]
            cases pT 0 <;> rfl
          exact hpF10.trans hpT10.symm
        · have ha0 : a ≠ 0 := fun h => h0gS (h ▸ ha)
          have ha9 : a ≠ 9 := fun h => h9gS (h ▸ ha)
          exact (hpre_eq pF pT hp_agree).2 a ha0 ha9 ha10
