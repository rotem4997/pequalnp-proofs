import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2598_314
    (p9_lower :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ (15 : ℕ) →
        ∃ (y : Fin (9 : ℕ) → Bool),
          C.eval (List.ofFn y) ≠
            (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) ||
             y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) ||
             y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) ||
             y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) ||
             y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) ||
             y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) ||
             y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) ||
             y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) ||
             y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) ||
             y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) ||
             y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) ||
             y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ))))
    (low_reads :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ (18 : ℕ) →
        have r : ℕ := C.gates.countP fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          if g.op.eval [Bool.false] then
            g.inputs.head? == Option.some (0 : ℕ) || g.inputs.head? == Option.some (10 : ℕ)
          else
            g.inputs.contains (0 : ℕ) || g.inputs.contains (10 : ℕ);
        (1 : ℕ) ≤ r → r ≤ (2 : ℕ) →
        ∃ (x : Fin (10 : ℕ) → Bool),
          C.eval (List.ofFn x ++ [!x (0 : Fin (10 : ℕ))]) ≠
            (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) ||
             x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
             x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) ||
             x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
             x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) ||
             x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
             x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
             x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
             x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
             x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
             x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
             x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
             x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
             x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
             x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hfan hsize
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  let p10 : (Fin 10 → Bool) → Bool := fun x5 =>
    x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 ||
    x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 4 && x5 9 ||
    x5 5 && x5 7 || x5 7 && x5 9 || x5 9 && x5 6 || x5 6 && x5 8 || x5 8 && x5 5
  let p9 : (Fin 9 → Bool) → Bool := fun y =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
    y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
    y 6 && y 8 || y 8 && y 5
  let reads010 : Gate → Bool := fun g =>
    if g.op.eval [false] then
      g.inputs.head? == some 0 || g.inputs.head? == some 10
    else
      g.inputs.contains 0 || g.inputs.contains 10
  let wstep : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wstep_pres : ∀ (gs : List Gate) (w : List Bool) (k : ℕ),
      k < w.length → (gs.foldl wstep w).getD k false = w.getD k false := by
    intro gs
    induction gs with
    | nil => intro w k _; rfl
    | cons g rest ih =>
      intro w k hk
      rw [List.foldl_cons, ih (wstep w g) k (by simp [wstep]; omega)]
      simp only [wstep]
      exact List.getD_append _ _ _ _ hk
  by_cases hr0 : (C.gates.filter reads010).length = 0
  · by_contra hno
    push Not at hno
    have hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = p10 x := hno
    have hnone : ∀ g ∈ C.gates, reads010 g = false := by
      intro g hg
      cases hrg : reads010 g with
      | false => rfl
      | true =>
        have hmem : g ∈ C.gates.filter reads010 := List.mem_filter.mpr ⟨hg, hrg⟩
        have hpos : 0 < (C.gates.filter reads010).length := List.length_pos_of_mem hmem
        omega
    by_cases hout0 : C.output = 0
    · have hval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = x 0 := by
        intro x
        change (C.gates.foldl wstep (List.ofFn x ++ [!x 0])).getD C.output false = x 0
        rw [hout0, wstep_pres C.gates _ 0 (by simp)]
        simp [List.getD_eq_getElem?_getD]
      let xe : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
      have h1 := (hval xe).symm.trans (hcomp xe)
      have h2 : xe 0 = false := by decide
      have h3 : p10 xe = true := by decide
      rw [h2, h3] at h1
      exact Bool.false_ne_true h1
    · by_cases hout10 : C.output = 10
      · have hval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = !x 0 := by
          intro x
          change (C.gates.foldl wstep (List.ofFn x ++ [!x 0])).getD C.output false = !x 0
          rw [hout10, wstep_pres C.gates _ 10 (by simp)]
          simp [List.getD_eq_getElem?_getD]
        let xz : Fin 10 → Bool := fun _ => false
        have h1 := (hval xz).symm.trans (hcomp xz)
        have h2 : (!xz 0) = true := by decide
        have h3 : p10 xz = false := by decide
        rw [h2, h3] at h1
        exact Bool.false_ne_true h1.symm
      · have hagree : ∀ (gs : List Gate) (w1 w2 : List Bool),
            (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
            (∀ g ∈ gs, reads010 g = false) →
            w1.length = w2.length → 11 ≤ w1.length →
            (∀ i : ℕ, i ≠ 0 → i ≠ 10 → w1.getD i false = w2.getD i false) →
            ∀ i : ℕ, i ≠ 0 → i ≠ 10 →
              (gs.foldl wstep w1).getD i false = (gs.foldl wstep w2).getD i false := by
          intro gs
          induction gs with
          | nil => intro w1 w2 _ _ _ _ hag i hi0 hi10; exact hag i hi0 hi10
          | cons g rest ih =>
            intro w1 w2 hfg hrg hlen h11 hag
            have hgf := hfg g List.mem_cons_self
            have hgr := hrg g List.mem_cons_self
            have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
              simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgf.1
            have heval : g.op.eval (g.inputs.map fun i => w1.getD i false) =
                g.op.eval (g.inputs.map fun i => w2.getD i false) := by
              rcases hgop with hop | hop | hop
              · simp [reads010, hop, andEval] at hgr
                have hmap : g.inputs.map (fun i => w1.getD i false) = g.inputs.map (fun i => w2.getD i false) := by
                  apply List.map_congr_left
                  intro a ha
                  have hne0 : a ≠ 0 := by intro h0; subst h0; exact hgr.1 ha
                  have hne10 : a ≠ 10 := by intro h10; subst h10; exact hgr.2 ha
                  exact hag a hne0 hne10
                rw [hmap]
              · simp [reads010, hop, orEval] at hgr
                have hmap : g.inputs.map (fun i => w1.getD i false) = g.inputs.map (fun i => w2.getD i false) := by
                  apply List.map_congr_left
                  intro a ha
                  have hne0 : a ≠ 0 := by intro h0; subst h0; exact hgr.1 ha
                  have hne10 : a ≠ 10 := by intro h10; subst h10; exact hgr.2 ha
                  exact hag a hne0 hne10
                rw [hmap]
              · simp only [reads010, hop, notEval] at hgr; rw [hop]
                cases hgin : g.inputs with
                | nil => rfl
                | cons a tl =>
                  simp only [hgin, List.head?_cons] at hgr
                  have hne0 : a ≠ 0 := by intro h0; subst h0; simp at hgr
                  have hne10 : a ≠ 10 := by intro h10; subst h10; simp at hgr
                  simp only [List.map_cons, notEval, List.headD_cons]
                  rw [hag a hne0 hne10]
            apply ih (wstep w1 g) (wstep w2 g)
              (fun g' hg' => hfg g' (List.mem_cons_of_mem _ hg'))
              (fun g' hg' => hrg g' (List.mem_cons_of_mem _ hg'))
              (by simp [wstep, hlen])
              (by simp [wstep]; omega)
            intro i hi0 hi10
            simp only [wstep]
            by_cases hlt : i < w1.length
            · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
              exact hag i hi0 hi10
            · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hlt),
                  List.getD_append_right _ _ _ _ (hlen ▸ Nat.le_of_not_lt hlt), hlen, heval]
        let x1 : Fin 10 → Bool := fun i => decide (i = 1)
        let x2 : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
        have hinit : ∀ i : ℕ, i ≠ 0 → i ≠ 10 →
            (List.ofFn x1 ++ [!x1 0]).getD i false = (List.ofFn x2 ++ [!x2 0]).getD i false := by
          intro i hi0 hi10
          by_cases hlt : i < 10
          · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
            have hne : (⟨i, hlt⟩ : Fin 10) ≠ 0 := by intro h; exact hi0 (congrArg Fin.val h)
            simp [x1, x2, hne]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        have heq := hagree C.gates (List.ofFn x1 ++ [!x1 0]) (List.ofFn x2 ++ [!x2 0])
          hfan hnone (by simp) (by simp) hinit C.output hout0 hout10
        have hc1 : C.eval (List.ofFn x1 ++ [!x1 0]) = false := by
          rw [hcomp x1]; decide
        have hc2 : C.eval (List.ofFn x2 ++ [!x2 0]) = true := by
          rw [hcomp x2]; decide
        change C.eval (List.ofFn x1 ++ [!x1 0]) = C.eval (List.ofFn x2 ++ [!x2 0]) at heq
        rw [hc1, hc2] at heq
        exact Bool.false_ne_true heq
  · by_cases hr2 : (C.gates.filter reads010).length ≤ 2
    · exact low_reads C hfan hsize
        (by rw [List.countP_eq_length_filter]; exact Nat.pos_of_ne_zero hr0)
        (by rw [List.countP_eq_length_filter]; exact hr2)
    · by_contra hno
      push Not at hno
      have hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = p10 x := hno
      let lift : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i =>
        ([false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] : List Bool).getD i.val false
      have hlift_iso : ∀ y : Fin 9 → Bool, p10 (lift y) = p9 y := by
        intro y
        have hall : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
            (false && b4 || b4 && b0 || b0 && b1 || b1 && b6 || b6 && false ||
             false && b7 || b4 && b3 || b0 && b5 || b1 && b2 || b6 && b8 ||
             b7 && b5 || b5 && b8 || b8 && b3 || b3 && b2 || b2 && b7) =
            (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 ||
             b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 ||
             b6 && b8 || b8 && b5) := by
          intro b0 b1 b2 b3 b4 b5 b6 b7 b8
          simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
          rw [Bool.and_comm b4 b3, Bool.and_comm b7 b5, Bool.and_comm b5 b8,
              Bool.and_comm b8 b3, Bool.and_comm b3 b2]
          ac_rfl
        exact hall (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
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
          env.getD 0 (Sum.inl false) = Sum.inl false →
          env.getD 10 (Sum.inl false) = Sum.inl true →
          (∀ y : Fin 9 → Bool, (wC y).length = env.length) →
          (∀ i : ℕ, symBd dgs.length (env.getD i (Sum.inl false))) →
          (∀ y : Fin 9 → Bool, ∀ i : ℕ,
            evalSym (dgs.foldl wstep (List.ofFn y)) (env.getD i (Sum.inl false)) = (wC y).getD i false) →
          let res := gs.foldl cstep (env, dgs)
          res.2.length + (gs.filter reads010).length ≤ dgs.length + gs.length ∧
          (∀ g ∈ res.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
          (∀ y : Fin 9 → Bool, ∀ i : ℕ,
            evalSym (res.2.foldl wstep (List.ofFn y)) (res.1.getD i (Sum.inl false)) =
              (gs.foldl wstep (wC y)).getD i false) := by
        intro gs
        induction gs with
        | nil =>
          intro env dgs wC _ hdgs _ _ _ _ _ heq
          exact ⟨by simp, hdgs, heq⟩
        | cons g rest ih =>
          intro env dgs wC hfg hdgs h11 h0 h10 hwlen hbd heq
          have hgf := hfg g List.mem_cons_self
          have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgf.1
          let st1 := cstep (env, dgs) g
          have hstep :
              st1.1.length = env.length + 1 ∧
              st1.1.getD 0 (Sum.inl false) = Sum.inl false ∧
              st1.1.getD 10 (Sum.inl false) = Sum.inl true ∧
              (st1.2.length + (if reads010 g then 1 else 0) ≤ dgs.length + 1) ∧
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
                (env ++ [v]).getD 0 (Sum.inl false) = Sum.inl false ∧
                (env ++ [v]).getD 10 (Sum.inl false) = Sum.inl true ∧
                (dgs.length + (if reads010 g then 1 else 0) ≤ dgs.length + 1) ∧
                (∀ g' ∈ dgs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
                (∀ i : ℕ, symBd dgs.length ((env ++ [v]).getD i (Sum.inl false))) ∧
                (∀ y : Fin 9 → Bool, ∀ i : ℕ,
                  evalSym (dgs.foldl wstep (List.ofFn y)) ((env ++ [v]).getD i (Sum.inl false)) =
                    (wstep (wC y) g).getD i false) := by
              intro v hvbd hveval
              refine ⟨by simp, ?_, ?_, by split_ifs <;> omega, hdgs, ?_, ?_⟩
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h0
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h10
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
                reads010 g = false →
                (∀ y : Fin 9 → Bool,
                  ng.op.eval (ng.inputs.map fun i => (dgs.foldl wstep (List.ofFn y)).getD i false) =
                    g.op.eval (g.inputs.map fun i => (wC y).getD i false)) →
                (env ++ [Sum.inr (9 + dgs.length)]).length = env.length + 1 ∧
                (env ++ [Sum.inr (9 + dgs.length)]).getD 0 (Sum.inl false) = Sum.inl false ∧
                (env ++ [Sum.inr (9 + dgs.length)]).getD 10 (Sum.inl false) = Sum.inl true ∧
                ((dgs ++ [ng]).length + (if reads010 g then 1 else 0) ≤ dgs.length + 1) ∧
                (∀ g' ∈ dgs ++ [ng], g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
                (∀ i : ℕ, symBd (dgs ++ [ng]).length ((env ++ [Sum.inr (9 + dgs.length)]).getD i (Sum.inl false))) ∧
                (∀ y : Fin 9 → Bool, ∀ i : ℕ,
                  evalSym ((dgs ++ [ng]).foldl wstep (List.ofFn y)) ((env ++ [Sum.inr (9 + dgs.length)]).getD i (Sum.inl false)) =
                    (wstep (wC y) g).getD i false) := by
              intro ng hng hnr hngeval
              refine ⟨by simp, ?_, ?_, by simp [hnr], ?_, ?_, ?_⟩
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h0
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h10
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
                        have hnr : reads010 g = false := by
                          have ha0 : a ≠ 0 := by intro h; subst h; rw [h0] at ha; cases ha
                          have ha10 : a ≠ 10 := by intro h; subst h; rw [h10] at ha; cases ha
                          have hb0 : b ≠ 0 := by intro h; subst h; rw [h0] at hb; cases hb
                          have hb10 : b ≠ 10 := by intro h; subst h; rw [h10] at hb; cases hb
                          simp [reads010, hop, hgin, andEval]
                          exact ⟨⟨ha0.symm, hb0.symm⟩, ha10.symm, hb10.symm⟩
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
                        have hnr : reads010 g = false := by
                          have ha0 : a ≠ 0 := by intro h; subst h; rw [h0] at ha; cases ha
                          have ha10 : a ≠ 10 := by intro h; subst h; rw [h10] at ha; cases ha
                          have hb0 : b ≠ 0 := by intro h; subst h; rw [h0] at hb; cases hb
                          have hb10 : b ≠ 10 := by intro h; subst h; rw [h10] at hb; cases hb
                          simp [reads010, hop, hgin, orEval]
                          exact ⟨⟨ha0.symm, hb0.symm⟩, ha10.symm, hb10.symm⟩
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
                  have hnr : reads010 g = false := by
                    have ha0 : a ≠ 0 := by intro h; subst h; rw [h0] at ha; cases ha
                    have ha10 : a ≠ 10 := by intro h; subst h; rw [h10] at ha; cases ha
                    simp [reads010, hop, hgin, notEval, ha0, ha10]
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
          rcases hstep with ⟨hslen, hs0, hs10, hssz, hsfan, hsbd, hseq⟩
          have hrec := ih st1.1 st1.2 (fun y => wstep (wC y) g)
            (fun g' hg' => hfg g' (List.mem_cons_of_mem _ hg'))
            hsfan (by omega) hs0 hs10
            (fun y => by simp [wstep, hwlen y, hslen])
            hsbd hseq
          rcases hrec with ⟨hsz', hfan', heq'⟩
          refine ⟨?_, hfan', heq'⟩
          change (rest.foldl cstep st1).2.length + ((g :: rest).filter reads010).length ≤ dgs.length + (g :: rest).length
          have hsz1 : (rest.foldl cstep st1).2.length + (rest.filter reads010).length ≤ st1.2.length + rest.length := hsz'
          cases hrg : reads010 g with
          | false =>
            simp only [List.filter_cons, hrg, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hssz ⊢
            omega
          | true =>
            simp only [List.filter_cons, hrg, ↓reduceIte, List.length_cons] at hssz ⊢
            omega
      let env0 : List (Sum Bool ℕ) :=
        [Sum.inl false, Sum.inr 4, Sum.inr 0, Sum.inr 1, Sum.inr 6,
         Sum.inr 7, Sum.inr 3, Sum.inr 5, Sum.inr 2, Sum.inr 8, Sum.inl true]
      have hres := hcomp_ind C.gates env0 [] (fun y => List.ofFn (lift y) ++ [!lift y 0])
        hfan (by simp) (by decide) (by decide) (by decide)
        (fun y => by simp [env0])
        (fun i => by
          by_cases hi : i < 11
          · interval_cases i <;> simp [env0, symBd]
          · rw [List.getD_eq_default _ _ (by simp [env0]; omega)]; trivial)
        (fun y i => by
          by_cases hi : i < 11
          · interval_cases i <;> simp [env0, evalSym, lift, List.getD_eq_getElem?_getD]
          · rw [List.getD_eq_default _ _ (by simp [env0]; omega),
                List.getD_eq_default _ _ (by simp; omega)]
            rfl)
      rcases hres with ⟨hsz, hfanD, heqD⟩
      let res := C.gates.foldl cstep (env0, [])
      have hEvalOut : ∀ y : Fin 9 → Bool,
          evalSym (res.2.foldl wstep (List.ofFn y)) (res.1.getD C.output (Sum.inl false)) = p9 y := by
        intro y
        have h1 := heqD y C.output
        have h2 := hcomp (lift y)
        rw [hlift_iso y] at h2
        exact h1.trans h2
      cases hout : res.1.getD C.output (Sum.inl false) with
      | inl b =>
        have h0' := hEvalOut (fun _ => false)
        have h1' := hEvalOut (fun _ => true)
        rw [hout] at h0' h1'
        have hp0 : p9 (fun _ => false) = false := by decide
        have hp1 : p9 (fun _ => true) = true := by decide
        simp only [evalSym, Sum.elim_inl, id_eq, hp0, hp1] at h0' h1'
        rw [h0'] at h1'
        exact Bool.false_ne_true h1'
      | inr outD =>
        let D : Circuit := ⟨res.2, outD⟩
        have hDsize : D.size ≤ 15 := by
          change (C.gates.foldl cstep (env0, [])).2.length ≤ 15
          change C.gates.length ≤ 18 at hsize
          simp only [List.length_nil, Nat.zero_add] at hsz
          omega
        obtain ⟨y, hy⟩ := p9_lower D hfanD hDsize
        have hDy := hEvalOut y
        rw [hout] at hDy
        exact hy hDy
