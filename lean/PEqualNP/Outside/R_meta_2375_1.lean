import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2375_1
    (h18 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10
      (fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (hNot : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [!x 0])).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true)
    (hAnd : ∀ (b : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [x 0 && (if b then x 1 else x 2)])).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true)
    (hOr : ∀ (b : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [x 0 || (if b then x 1 else x 2)])).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) =>
        x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) ||
        x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) ||
        x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) ||
        x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) ||
        x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) ||
        x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) =>
        (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro x1 x2 x3 x4 hx1_ok hx2_ok hx2_sz x8 x9 h10 h11 h12
  let f : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have eval_and : ∀ l, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l, PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have wires_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g rest ih =>
      intro ws
      rw [List.foldl_cons, ih]
      change (ws ++ [_]).length + rest.length = ws.length + (g :: rest).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have wires_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g rest ih =>
      intro ws i hi
      simp only [List.foldl_cons]
      have hi' : i < (step ws g).length := by simp only [step, List.length_append, List.length_singleton]; omega
      rw [ih (step ws g) i hi']
      exact List.getD_append _ _ _ _ hi
  have getD_snoc_end : ∀ {α : Type} (l : List α) (a d : α), (l ++ [a]).getD l.length d = a := by
    intro α l a d
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
    simp
  have f_nonconst : ∀ b : Bool, ¬ (∀ x : Fin 10 → Bool, f x = b) := by
    intro b hb
    have h0 : f (fun _ => false) = false := rfl
    have h1 : f (fun _ => true) = true := rfl
    rw [hb (fun _ => false)] at h0
    rw [hb (fun _ => true)] at h1
    exact Bool.noConfusion (h0.symm.trans h1)
  -- Constant and wire-copy elimination engine for degenerate first gate
  let evalSym : Bool ⊕ ℕ → List Bool → Bool :=
    fun s ws => Sum.elim id (fun k => ws.getD k false) s
  let elimGate : List (Bool ⊕ ℕ) → ℕ → PEqualNP.CircuitLowerBounds.Gate →
      (Bool ⊕ ℕ) × Option PEqualNP.CircuitLowerBounds.Gate := fun st outIdx g =>
    let ins := g.inputs.map (fun i => st.getD i (Sum.inl false))
    PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (Sum.inl false, none) (b, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inl false, none) (Sum.inr ka, none))
              (fun kb => (Sum.inr outIdx, some ⟨.and, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl false, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (b, none) (Sum.inl true, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inr ka, none) (Sum.inl true, none))
              (fun kb => (Sum.inr outIdx, some ⟨.or, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a _ => Sum.elim
          (fun ba => (Sum.inl (!ba), none))
          (fun ka => (Sum.inr outIdx, some ⟨.not, [ka]⟩)) a))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  have elimGate_ok : ∀ (st : List (Bool ⊕ ℕ)) (outIdx : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ (wsN wsO : List Bool), wsN.length = outIdx →
        (∀ i < st.length, evalSym (st.getD i (Sum.inl false)) wsN = wsO.getD i false) →
        wsO.length = st.length →
        let r := elimGate st outIdx g
        let wsN' := Option.elim r.2 wsN (fun g' => step wsN g')
        (Option.elim r.2 True (fun g' => g'.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2)) ∧
        evalSym r.1 wsN' = g.op.eval (g.inputs.map (fun i => wsO.getD i false))) := by
    intro st outIdx g hok wsN wsO hlenN hagree hlenO
    have hop := hok.1
    have hlen := hok.2
    have hval : ∀ i, evalSym (st.getD i (Sum.inl false)) wsN = wsO.getD i false := by
      intro i
      by_cases hi : i < st.length
      · exact hagree i hi
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
            List.getD_eq_default _ _ (by omega : wsO.length ≤ i)]
        rfl
    rcases hop with hop | hop | hop
    · cases hg : g.inputs with
      | nil =>
        simp only [elimGate, hop, hg, List.map_nil, eval_and, List.all_nil, Option.elim_none,
          evalSym, Sum.elim_inl]
        exact ⟨trivial, rfl⟩
      | cons i1 t1 =>
        cases t1 with
        | nil =>
          simp only [elimGate, hop, hg, List.map_cons, List.map_nil, eval_and, List.all_cons,
            List.all_nil, id, Bool.and_true, Option.elim_none]
          exact ⟨trivial, hval i1⟩
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            have h1 := hval i1
            have h2 := hval i2
            dsimp only [elimGate]
            rw [hop, hg]
            simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
            cases hs1 : st.getD i1 (Sum.inl false) with
            | inl b1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inl, id] at h1
              cases b1
              · simp only [Sum.elim_inl, Option.elim_none, evalSym, id, ← h1, Bool.false_and, and_self]
              · simp only [Sum.elim_inl, Option.elim_none, ← h1, Bool.true_and, true_and]; exact h2
            | inr k1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inr] at h1
              cases hs2 : st.getD i2 (Sum.inl false) with
              | inl b2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inl, id] at h2
                cases b2
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, id, ← h2, Bool.and_false, and_self]
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, ← h2, Bool.and_true, true_and]; exact h1
              | inr k2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inr] at h2
                simp only [Sum.elim_inr, Option.elim_some]
                refine ⟨⟨Or.inl rfl, by simp⟩, ?_⟩
                simp only [evalSym, Sum.elim_inr, step, ← hlenN, getD_snoc_end,
                  List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
                rw [h1, h2]
          | cons i3 t3 => rw [hg] at hlen; simp at hlen
    · cases hg : g.inputs with
      | nil =>
        simp only [elimGate, hop, hg, List.map_nil, eval_or, List.any_nil, Option.elim_none,
          evalSym, Sum.elim_inl]
        exact ⟨trivial, rfl⟩
      | cons i1 t1 =>
        cases t1 with
        | nil =>
          simp only [elimGate, hop, hg, List.map_cons, List.map_nil, eval_or, List.any_cons,
            List.any_nil, id, Bool.or_false, Option.elim_none]
          exact ⟨trivial, hval i1⟩
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            have h1 := hval i1
            have h2 := hval i2
            dsimp only [elimGate]
            rw [hop, hg]
            simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
            cases hs1 : st.getD i1 (Sum.inl false) with
            | inl b1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inl, id] at h1
              cases b1
              · simp only [Sum.elim_inl, Option.elim_none, ← h1, Bool.false_or, true_and]; exact h2
              · simp only [Sum.elim_inl, Option.elim_none, evalSym, id, ← h1, Bool.true_or, and_self]
            | inr k1 =>
              rw [hs1] at h1
              simp only [evalSym, Sum.elim_inr] at h1
              cases hs2 : st.getD i2 (Sum.inl false) with
              | inl b2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inl, id] at h2
                cases b2
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, ← h2, Bool.or_false, true_and]; exact h1
                · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, id, ← h2, Bool.or_true, and_self]
              | inr k2 =>
                rw [hs2] at h2
                simp only [evalSym, Sum.elim_inr] at h2
                simp only [Sum.elim_inr, Option.elim_some]
                refine ⟨⟨Or.inr (Or.inl rfl), by simp⟩, ?_⟩
                simp only [evalSym, Sum.elim_inr, step, ← hlenN, getD_snoc_end,
                  List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
                rw [h1, h2]
          | cons i3 t3 => rw [hg] at hlen; simp at hlen
    · change g.op = .not at hop
      cases hg : g.inputs with
      | nil =>
        simp only [elimGate, hop, hg, List.map_nil, eval_not, List.headD_nil, Option.elim_none,
          evalSym, Sum.elim_inl]
        exact ⟨trivial, rfl⟩
      | cons i1 t1 =>
        have h1 := hval i1
        dsimp only [elimGate]
        rw [hop, hg]
        simp only [List.map_cons, eval_not, List.headD_cons]
        cases hs1 : st.getD i1 (Sum.inl false) with
        | inl b1 =>
          rw [hs1] at h1
          simp only [evalSym, Sum.elim_inl, id] at h1
          simp only [Sum.elim_inl, Option.elim_none, evalSym, id, ← h1, and_self]
        | inr k1 =>
          rw [hs1] at h1
          simp only [evalSym, Sum.elim_inr] at h1
          simp only [Sum.elim_inr, Option.elim_some]
          refine ⟨⟨Or.inr (Or.inr rfl), by simp⟩, ?_⟩
          simp only [evalSym, Sum.elim_inr, step, ← hlenN, getD_snoc_end,
            List.map_cons, eval_not, List.headD_cons]
          rw [h1]
  let elimStep : (List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) →
      PEqualNP.CircuitLowerBounds.Gate →
      (List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) := fun acc g =>
    let r := elimGate acc.1 (10 + acc.2.length) g
    (acc.1 ++ [r.1], Option.elim r.2 acc.2 (fun g' => acc.2 ++ [g']))
  have elimRun_ok : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st0 : List (Bool ⊕ ℕ)) (acc0 : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ acc0, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ s ∈ st0, Sum.elim (fun _ => True) (fun k => k < 10 + acc0.length) s) →
      let res := gs.foldl elimStep (st0, acc0)
      (∃ sfx, res.1 = st0 ++ sfx ∧ sfx.length = gs.length) ∧
      res.2.length ≤ acc0.length + gs.length ∧
      (∀ g ∈ res.2, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ (wsN0 wsO0 : List Bool), wsN0.length = 10 → wsO0.length = st0.length →
        (∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (acc0.foldl step wsN0) = wsO0.getD i false) →
        ∀ i < res.1.length, evalSym (res.1.getD i (Sum.inl false)) (res.2.foldl step wsN0) =
          (gs.foldl step wsO0).getD i false) := by
    intro gs
    induction gs with
    | nil =>
      intro st0 acc0 _ hacc0 _
      refine ⟨⟨[], by simp, rfl⟩, by simp, hacc0, ?_⟩
      intro wsN0 wsO0 _ _ hagree i hi
      exact hagree i hi
    | cons g rest ih =>
      intro st0 acc0 hgs hacc0 hst0
      have hg_ok := hgs g List.mem_cons_self
      have hrest_ok : ∀ g' ∈ rest, g'.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
      let r := elimGate st0 (10 + acc0.length) g
      let st1 := st0 ++ [r.1]
      let acc1 := Option.elim r.2 acc0 (fun g' => acc0 ++ [g'])
      have hacc1_len : acc1.length ≤ acc0.length + 1 := by
        dsimp only [acc1]
        cases hr2 : r.2 with
        | none => simp
        | some g' => simp
      have hacc1_ok : ∀ g' ∈ acc1, g'.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 := by
        dsimp only [acc1]
        cases hr2 : r.2 with
        | none => exact hacc0
        | some g' =>
          have hdummy := elimGate_ok st0 (10 + acc0.length) g hg_ok
            (List.replicate (10 + acc0.length) false)
            (List.ofFn (fun i : Fin st0.length => evalSym (st0.getD i.val (Sum.inl false)) (List.replicate (10 + acc0.length) false)))
            (by simp)
            (fun i hi => by symm; rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn])
            (by simp)
          have hg'_ok : g'.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 := by
            have := hdummy.1
            change Option.elim r.2 True _ at this
            rw [hr2] at this
            exact this
          intro h hh
          simp only [Option.elim_some, List.mem_append, List.mem_singleton] at hh
          rcases hh with hh | rfl
          · exact hacc0 h hh
          · exact hg'_ok
      have hst1_bnd : ∀ s ∈ st1, Sum.elim (fun _ => True) (fun k => k < 10 + acc1.length) s := by
        intro s hs
        simp only [st1, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · have h := hst0 s hs
          cases s with
          | inl _ => trivial
          | inr k =>
            have hle : acc0.length ≤ acc1.length := by
              dsimp only [acc1]; cases r.2 <;> simp
            simp only [Sum.elim_inr] at h ⊢; omega
        · have hr1_bnd : Sum.elim (fun _ => True) (fun k => k < 10 + acc1.length) r.1 := by
            have hst_get : ∀ i, Sum.elim (fun _ => True) (fun k => k < 10 + acc0.length) (st0.getD i (Sum.inl false)) := by
              intro i
              by_cases hi : i < st0.length
              · rw [List.getD_eq_getElem _ _ hi]
                exact hst0 _ (List.getElem_mem hi)
              · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; trivial
            have hle : acc0.length ≤ acc1.length := by
              dsimp only [acc1]; cases r.2 <;> simp
            have mono : ∀ s : Bool ⊕ ℕ, Sum.elim (fun _ => True) (fun k => k < 10 + acc0.length) s →
                Sum.elim (fun _ => True) (fun k => k < 10 + acc1.length) s := by
              intro s hs; cases s with
              | inl _ => trivial
              | inr k => simp only [Sum.elim_inr] at hs ⊢; omega
            rcases hg_ok.1 with hop | hop | hop
            · cases hg : g.inputs with
              | nil => simp only [r, elimGate, hop, hg, List.map_nil, Sum.elim_inl]
              | cons i1 t1 => cases t1 with
                | nil =>
                  simp only [r, elimGate, hop, hg, List.map_cons, List.map_nil]
                  exact mono _ (hst_get i1)
                | cons i2 t2 =>
                  have h1 := hst_get i1
                  have h2 := hst_get i2
                  dsimp only [r, acc1, elimGate]
                  rw [hop, hg]
                  simp only [List.map_cons]
                  cases hs1 : st0.getD i1 (Sum.inl false) with
                  | inl b1 =>
                    cases b1
                    · simp only [Sum.elim_inl]
                    · simp only [Sum.elim_inl, Option.elim_none]; exact h2
                  | inr k1 =>
                    cases hs2 : st0.getD i2 (Sum.inl false) with
                    | inl b2 =>
                      cases b2
                      · simp only [Sum.elim_inr, Sum.elim_inl]
                      · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]; rw [hs1] at h1; exact h1
                    | inr k2 =>
                      simp only [Sum.elim_inr, Option.elim_some, List.length_append, List.length_singleton]
                      omega
            · cases hg : g.inputs with
              | nil => simp only [r, elimGate, hop, hg, List.map_nil, Sum.elim_inl]
              | cons i1 t1 => cases t1 with
                | nil =>
                  simp only [r, elimGate, hop, hg, List.map_cons, List.map_nil]
                  exact mono _ (hst_get i1)
                | cons i2 t2 =>
                  have h1 := hst_get i1
                  have h2 := hst_get i2
                  dsimp only [r, acc1, elimGate]
                  rw [hop, hg]
                  simp only [List.map_cons]
                  cases hs1 : st0.getD i1 (Sum.inl false) with
                  | inl b1 =>
                    cases b1
                    · simp only [Sum.elim_inl, Option.elim_none]; exact h2
                    · simp only [Sum.elim_inl]
                  | inr k1 =>
                    cases hs2 : st0.getD i2 (Sum.inl false) with
                    | inl b2 =>
                      cases b2
                      · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]; rw [hs1] at h1; exact h1
                      · simp only [Sum.elim_inr, Sum.elim_inl]
                    | inr k2 =>
                      simp only [Sum.elim_inr, Option.elim_some, List.length_append, List.length_singleton]
                      omega
            · change g.op = .not at hop
              cases hg : g.inputs with
              | nil => simp only [r, elimGate, hop, hg, List.map_nil, Sum.elim_inl]
              | cons i1 t1 =>
                dsimp only [r, acc1, elimGate]
                rw [hop, hg]
                simp only [List.map_cons]
                cases hs1 : st0.getD i1 (Sum.inl false) with
                | inl b1 => simp only [Sum.elim_inl]
                | inr k1 =>
                  simp only [Sum.elim_inr, Option.elim_some, List.length_append, List.length_singleton]
                  omega
          exact hr1_bnd
      obtain ⟨⟨sfx, hsfx, hsfx_len⟩, hlen2, hok2, hsem2⟩ := ih st1 acc1 hrest_ok hacc1_ok hst1_bnd
      refine ⟨⟨r.1 :: sfx, by simpa [elimStep, st1, acc1, r] using hsfx, by simp [hsfx_len]⟩,
              by simp only [List.foldl_cons, elimStep, List.length_cons]; change (rest.foldl elimStep (st1, acc1)).2.length ≤ acc0.length + (rest.length + 1); omega,
              hok2, ?_⟩
      intro wsN0 wsO0 hlenN0 hlenO0 hagree0 i hi
      have hlen_acc0 : (acc0.foldl step wsN0).length = 10 + acc0.length := by rw [wires_len, hlenN0]
      have hstep_sem := (elimGate_ok st0 (10 + acc0.length) g hg_ok (acc0.foldl step wsN0) wsO0 hlen_acc0 hagree0 hlenO0).2
      have hfold_acc1 : acc1.foldl step wsN0 = Option.elim r.2 (acc0.foldl step wsN0) (fun g' => step (acc0.foldl step wsN0) g') := by
        dsimp only [acc1]
        cases r.2 with
        | none => rfl
        | some g' => simp only [Option.elim_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hagree1 : ∀ j < st1.length, evalSym (st1.getD j (Sum.inl false)) (acc1.foldl step wsN0) = (step wsO0 g).getD j false := by
        intro j hj
        simp only [st1, List.length_append, List.length_singleton] at hj
        by_cases hj0 : j < st0.length
        · rw [List.getD_append _ _ _ _ hj0, List.getD_append _ _ _ _ (by omega : j < wsO0.length)]
          have hs_bnd := hst0 (st0.getD j (Sum.inl false)) (by rw [List.getD_eq_getElem _ _ hj0]; exact List.getElem_mem hj0)
          rw [hfold_acc1]
          have hpres : evalSym (st0.getD j (Sum.inl false))
              (Option.elim r.2 (acc0.foldl step wsN0) (fun g' => step (acc0.foldl step wsN0) g')) =
              evalSym (st0.getD j (Sum.inl false)) (acc0.foldl step wsN0) := by
            cases r.2 with
            | none => rfl
            | some g' =>
              simp only [Option.elim_some]
              cases hsj : st0.getD j (Sum.inl false) with
              | inl b => rfl
              | inr k =>
                rw [hsj] at hs_bnd
                simp only [evalSym, Sum.elim_inr]
                exact List.getD_append _ _ _ _ (by rw [hlen_acc0]; exact hs_bnd)
          rw [hpres]
          exact hagree0 j hj0
        · have hjeq : j = st0.length := by omega
          subst hjeq
          rw [getD_snoc_end, hfold_acc1]
          dsimp only [step]
          rw [← hlenO0, getD_snoc_end]
          exact hstep_sem
      exact hsem2 wsN0 (step wsO0 g) hlenN0 (by simp [step, st1, hlenO0]) hagree1 i hi
  -- Helper: degenerate first gate contradicts h18
  have degen_elim : ∀ (sym10 : Bool ⊕ ℕ),
      (Sum.elim (fun _ => True) (fun k => k < 10) sym10) →
      (∀ x : Fin 10 → Bool,
        ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x)) =
          List.ofFn x ++ [evalSym sym10 (List.ofFn x)]) →
      ∃ (x13 : Fin 10 → Bool), f x13 = false ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = true ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = true := by
    intro sym10 hsym10_bnd hx1_eq
    apply Classical.byContradiction
    intro hno
    have hcomp : ∀ x : Fin 10 → Bool,
        ((x2.wires (List.ofFn x ++ [evalSym sym10 (List.ofFn x)])).getD x3 false &&
         (x2.wires (List.ofFn x ++ [evalSym sym10 (List.ofFn x)])).getD x4 false) = f x := by
      intro x
      cases hfx : f x with
      | true =>
        have h := h12 x hfx
        change (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x))).getD x3 false = true ∧
          (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x))).getD x4 false = true at h
        rw [hx1_eq x] at h
        rw [h.1, h.2]; rfl
      | false =>
        cases h3 : (x2.wires (List.ofFn x ++ [evalSym sym10 (List.ofFn x)])).getD x3 false with
        | false => rfl
        | true =>
          cases h4 : (x2.wires (List.ofFn x ++ [evalSym sym10 (List.ofFn x)])).getD x4 false with
          | false => rfl
          | true =>
            exfalso
            apply hno
            refine ⟨x, hfx, ?_, ?_⟩
            · rw [hx1_eq x]; exact h3
            · rw [hx1_eq x]; exact h4
    let gsFull : List PEqualNP.CircuitLowerBounds.Gate := x2.gates ++ [⟨.and, [x3, x4]⟩]
    let st0 : List (Bool ⊕ ℕ) := (List.finRange 10).map (fun i => Sum.inr i.val) ++ [sym10]
    have hst0_len : st0.length = 11 := by simp [st0]
    have hst0_bnd : ∀ s ∈ st0, Sum.elim (fun _ => True) (fun k => k < 10 + ([] : List PEqualNP.CircuitLowerBounds.Gate).length) s := by
      intro s hs
      simp only [st0, List.mem_append, List.mem_map, List.mem_singleton] at hs
      rcases hs with ⟨i, _, rfl⟩ | rfl
      · simpa using i.isLt
      · simpa using hsym10_bnd
    have hgsFull_ok : ∀ g ∈ gsFull, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      simp only [gsFull, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hx2_ok g hg
      · exact ⟨Or.inl rfl, by simp⟩
    let res := gsFull.foldl elimStep (st0, [])
    obtain ⟨⟨sfx, hsfx, hsfx_len⟩, hlen_res, hok_res, hsem_res⟩ :=
      elimRun_ok gsFull st0 [] hgsFull_ok (fun _ h => List.not_mem_nil h |>.elim) hst0_bnd
    let outPos : ℕ := 11 + x2.gates.length
    have hout_lt : outPos < res.1.length := by
      rw [hsfx, List.length_append, hst0_len, hsfx_len]
      simp [gsFull, outPos]
    have hval_out : ∀ x : Fin 10 → Bool, evalSym (res.1.getD outPos (Sum.inl false)) (res.2.foldl step (List.ofFn x)) = f x := by
      intro x
      let w0 := List.ofFn x ++ [evalSym sym10 (List.ofFn x)]
      have hw0_len : w0.length = st0.length := by simp [w0, hst0_len]
      have hagree0 : ∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (([] : List PEqualNP.CircuitLowerBounds.Gate).foldl step (List.ofFn x)) = w0.getD i false := by
        intro i hi
        rw [hst0_len] at hi
        by_cases hi10 : i < 10
        · have hst_i : st0.getD i (Sum.inl false) = Sum.inr i := by
            dsimp only [st0]
            rw [List.getD_append _ _ _ _ (by simp [hi10]),
                List.getD_eq_getElem _ _ (by simp [hi10]),
                List.getElem_map, List.getElem_finRange]
            rfl
          rw [hst_i]
          simp only [List.foldl_nil, evalSym, Sum.elim_inr, w0]
          exact (List.getD_append _ _ _ _ (by simp [hi10])).symm
        · have hieq : i = 10 := by omega
          subst hieq
          have hst10 : st0.getD 10 (Sum.inl false) = sym10 := by
            have hl10 : ((List.finRange 10).map fun i => (Sum.inr i.val : Bool ⊕ ℕ)).length = 10 := by simp
            dsimp only [st0]
            simpa only [hl10] using getD_snoc_end ((List.finRange 10).map fun i => (Sum.inr i.val : Bool ⊕ ℕ)) sym10 (Sum.inl false)
          rw [hst10]
          simp only [List.foldl_nil, w0]
          simpa only [List.length_ofFn] using (getD_snoc_end (List.ofFn x) (evalSym sym10 (List.ofFn x)) false).symm
      have hsem := hsem_res (List.ofFn x) w0 (by simp) hw0_len hagree0 outPos hout_lt
      rw [hsem]
      have hfold_full : gsFull.foldl step w0 = step (x2.gates.foldl step w0) ⟨.and, [x3, x4]⟩ := by
        simp [gsFull, List.foldl_append]
      rw [hfold_full]
      have hlen_x2 : (x2.gates.foldl step w0).length = outPos := by
        rw [wires_len]; simp [w0, outPos]
      dsimp only [step]
      rw [← hlen_x2, getD_snoc_end]
      simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
      exact hcomp x
    cases hout_sym : res.1.getD outPos (Sum.inl false) with
    | inl b =>
      apply f_nonconst b
      intro x
      have hx := hval_out x
      rw [hout_sym] at hx
      exact hx.symm
    | inr k =>
      apply h18
      refine ⟨⟨res.2, k⟩, hok_res, ?_, ?_⟩
      · change res.2.length ≤ 18
        have hgs_len : gsFull.length = x2.gates.length + 1 := by simp [gsFull]
        have hx2_len : x2.gates.length ≤ 17 := hx2_sz
        have hlen_res' : res.2.length ≤ gsFull.length := by
          simpa only [res, List.length_nil, zero_add] using hlen_res
        omega
      · intro x
        have hx := hval_out x
        rw [hout_sym] at hx
        exact hx
  -- Automorphism machinery for Petersen graph
  let E15 : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  have hf_iff : ∀ x : Fin 10 → Bool, f x = true ↔ ∃ e ∈ E15, x e.1 = true ∧ x e.2 = true := by
    intro x
    simp only [f, E15, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  have aut_of_bij : ∀ (π πinv : Fin 10 → Fin 10),
      (∀ i, πinv (π i) = i) → (∀ i, π (πinv i) = i) →
      (∀ e ∈ E15, (π e.1, π e.2) ∈ E15 ∨ (π e.2, π e.1) ∈ E15) →
      (∀ e ∈ E15, (πinv e.1, πinv e.2) ∈ E15 ∨ (πinv e.2, πinv e.1) ∈ E15) →
      ∀ x, f (x ∘ π) = f x := by
    intro π πinv _ h2 he1 he2 x
    apply Bool.eq_iff_iff.mpr
    rw [hf_iff, hf_iff]
    constructor
    · rintro ⟨e, he, h1e, h2e⟩
      rcases he1 e he with h | h
      · exact ⟨(π e.1, π e.2), h, h1e, h2e⟩
      · exact ⟨(π e.2, π e.1), h, h2e, h1e⟩
    · rintro ⟨e, he, h1e, h2e⟩
      rcases he2 e he with h | h
      · exact ⟨(πinv e.1, πinv e.2), h, by simpa only [Function.comp, h2] using h1e, by simpa only [Function.comp, h2] using h2e⟩
      · exact ⟨(πinv e.2, πinv e.1), h, by simpa only [Function.comp, h2] using h2e, by simpa only [Function.comp, h2] using h1e⟩
  let mkP : List (Fin 10) → Fin 10 → Fin 10 := fun l i => l.getD i.val 0
  let rot  := mkP [1,2,3,4,0, 6,7,8,9,5]
  let roti := mkP [4,0,1,2,3, 9,5,6,7,8]
  let swp  := mkP [5,7,9,6,8, 0,2,4,1,3]
  let swpi := mkP [5,8,6,9,7, 0,3,1,4,2]
  let s3   := mkP [0,4,3,8,5, 1,9,2,6,7]
  let s3i  := mkP [0,5,7,2,1, 4,8,9,3,6]
  have hrot_1 : ∀ i, roti (rot i) = i := by decide
  have hrot_2 : ∀ i, rot (roti i) = i := by decide
  have hrot_f : ∀ x, f (x ∘ rot) = f x := aut_of_bij rot roti hrot_1 hrot_2 (by decide) (by decide)
  have hswp_1 : ∀ i, swpi (swp i) = i := by decide
  have hswp_2 : ∀ i, swp (swpi i) = i := by decide
  have hswp_f : ∀ x, f (x ∘ swp) = f x := aut_of_bij swp swpi hswp_1 hswp_2 (by decide) (by decide)
  have hs3_1 : ∀ i, s3i (s3 i) = i := by decide
  have hs3_2 : ∀ i, s3 (s3i i) = i := by decide
  have hs3_f : ∀ x, f (x ∘ s3) = f x := aut_of_bij s3 s3i hs3_1 hs3_2 (by decide) (by decide)
  have aut_comp : ∀ (p1 p1i p2 p2i : Fin 10 → Fin 10),
      (∀ i, p1i (p1 i) = i) → (∀ i, p1 (p1i i) = i) → (∀ x, f (x ∘ p1) = f x) →
      (∀ i, p2i (p2 i) = i) → (∀ i, p2 (p2i i) = i) → (∀ x, f (x ∘ p2) = f x) →
      (∀ i, (p2i ∘ p1i) ((p1 ∘ p2) i) = i) ∧ (∀ i, (p1 ∘ p2) ((p2i ∘ p1i) i) = i) ∧
      (∀ x, f (x ∘ (p1 ∘ p2)) = f x) := by
    intro p1 p1i p2 p2i h1a h1b h1f h2a h2b h2f
    refine ⟨fun i => by simp [h1a, h2a], fun i => by simp [h2b, h1b], fun x => ?_⟩
    calc f (x ∘ (p1 ∘ p2)) = f ((x ∘ p1) ∘ p2) := rfl
      _ = f (x ∘ p1) := h2f (x ∘ p1)
      _ = f x := h1f x
  have aut_pow : ∀ (p pi : Fin 10 → Fin 10),
      (∀ i, pi (p i) = i) → (∀ i, p (pi i) = i) → (∀ x, f (x ∘ p) = f x) →
      ∀ n : ℕ, (∀ i, (pi^[n]) ((p^[n]) i) = i) ∧ (∀ i, (p^[n]) ((pi^[n]) i) = i) ∧
        (∀ x, f (x ∘ (p^[n])) = f x) := by
    intro p pi ha hb hf n
    induction n with
    | zero => exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    | succ k ih =>
      have hc := aut_comp p pi (p^[k]) (pi^[k]) ha hb hf ih.1 ih.2.1 ih.2.2
      refine ⟨fun i => ?_, fun i => ?_, fun x => ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih.1 (p i), ha i]
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih.2.1 (pi i), hb i]
      · have hfn : (p^[k + 1]) = p ∘ (p^[k]) := Function.iterate_succ' p k
        rw [hfn]
        exact hc.2.2 x
  have ex_aut_v : ∀ u : Fin 10, ∃ (π πinv : Fin 10 → Fin 10),
      (∀ i, πinv (π i) = i) ∧ (∀ i, π (πinv i) = i) ∧ (∀ x, f (x ∘ π) = f x) ∧ π 0 = u := by
    intro u
    have hrotp := aut_pow rot roti hrot_1 hrot_2 hrot_f
    fin_cases u
    · exact ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
    · exact ⟨rot^[1], roti^[1], (hrotp 1).1, (hrotp 1).2.1, (hrotp 1).2.2, rfl⟩
    · exact ⟨rot^[2], roti^[2], (hrotp 2).1, (hrotp 2).2.1, (hrotp 2).2.2, rfl⟩
    · exact ⟨rot^[3], roti^[3], (hrotp 3).1, (hrotp 3).2.1, (hrotp 3).2.2, rfl⟩
    · exact ⟨rot^[4], roti^[4], (hrotp 4).1, (hrotp 4).2.1, (hrotp 4).2.2, rfl⟩
    · exact ⟨swp, swpi, hswp_1, hswp_2, hswp_f, rfl⟩
    · have c := aut_comp (rot^[1]) (roti^[1]) swp swpi (hrotp 1).1 (hrotp 1).2.1 (hrotp 1).2.2 hswp_1 hswp_2 hswp_f
      exact ⟨(rot^[1]) ∘ swp, swpi ∘ (roti^[1]), c.1, c.2.1, c.2.2, rfl⟩
    · have c := aut_comp (rot^[2]) (roti^[2]) swp swpi (hrotp 2).1 (hrotp 2).2.1 (hrotp 2).2.2 hswp_1 hswp_2 hswp_f
      exact ⟨(rot^[2]) ∘ swp, swpi ∘ (roti^[2]), c.1, c.2.1, c.2.2, rfl⟩
    · have c := aut_comp (rot^[3]) (roti^[3]) swp swpi (hrotp 3).1 (hrotp 3).2.1 (hrotp 3).2.2 hswp_1 hswp_2 hswp_f
      exact ⟨(rot^[3]) ∘ swp, swpi ∘ (roti^[3]), c.1, c.2.1, c.2.2, rfl⟩
    · have c := aut_comp (rot^[4]) (roti^[4]) swp swpi (hrotp 4).1 (hrotp 4).2.1 (hrotp 4).2.2 hswp_1 hswp_2 hswp_f
      exact ⟨(rot^[4]) ∘ swp, swpi ∘ (roti^[4]), c.1, c.2.1, c.2.2, rfl⟩
  have ex_aut_pair : ∀ (u v : Fin 10), u ≠ v →
      (∃ (π πinv : Fin 10 → Fin 10),
        (∀ i, πinv (π i) = i) ∧ (∀ i, π (πinv i) = i) ∧ (∀ x, f (x ∘ π) = f x) ∧ π 0 = u ∧ π 1 = v) ∨
      (∃ (π πinv : Fin 10 → Fin 10),
        (∀ i, πinv (π i) = i) ∧ (∀ i, π (πinv i) = i) ∧ (∀ x, f (x ∘ π) = f x) ∧ π 0 = u ∧ π 2 = v) := by
    intro u v huv
    obtain ⟨p1, p1i, hp1a, hp1b, hp1f, hp10⟩ := ex_aut_v u
    have hs3p := aut_pow s3 s3i hs3_1 hs3_2 hs3_f
    have hv'0 : p1i v ≠ 0 := by
      intro h0
      apply huv
      calc u = p1 0 := hp10.symm
        _ = p1 (p1i v) := by rw [h0]
        _ = v := hp1b v
    cases hv' : p1i v with
    | mk val isLt =>
      have hv_eq : p1 ⟨val, isLt⟩ = v := by rw [← hv', hp1b v]
      have hval_ne : val ≠ 0 := by intro h0; apply hv'0; apply Fin.ext; rw [hv']; exact h0
      have mk_case : ∀ (k : ℕ) (t : Fin 10), (s3^[k]) 0 = 0 → (s3^[k]) t = ⟨val, isLt⟩ →
          ∃ (π πinv : Fin 10 → Fin 10),
            (∀ i, πinv (π i) = i) ∧ (∀ i, π (πinv i) = i) ∧ (∀ x, f (x ∘ π) = f x) ∧ π 0 = u ∧ π t = v := by
        intro k t h0 ht
        have c := aut_comp p1 p1i (s3^[k]) (s3i^[k]) hp1a hp1b hp1f (hs3p k).1 (hs3p k).2.1 (hs3p k).2.2
        exact ⟨p1 ∘ (s3^[k]), (s3i^[k]) ∘ p1i, c.1, c.2.1, c.2.2,
          by simp [Function.comp, h0, hp10], by simp [Function.comp, ht, hv_eq]⟩
      have hfin : (⟨val, isLt⟩ : Fin 10) = 1 ∨ (⟨val, isLt⟩ : Fin 10) = 4 ∨ (⟨val, isLt⟩ : Fin 10) = 5 ∨
          (⟨val, isLt⟩ : Fin 10) = 2 ∨ (⟨val, isLt⟩ : Fin 10) = 3 ∨ (⟨val, isLt⟩ : Fin 10) = 8 ∨
          (⟨val, isLt⟩ : Fin 10) = 6 ∨ (⟨val, isLt⟩ : Fin 10) = 9 ∨ (⟨val, isLt⟩ : Fin 10) = 7 := by
        omega
      rcases hfin with h | h | h | h | h | h | h | h | h
      · exact Or.inl (mk_case 0 1 rfl h.symm)
      · exact Or.inl (mk_case 1 1 rfl (by rw [h]; rfl))
      · exact Or.inl (mk_case 2 1 rfl (by rw [h]; rfl))
      · exact Or.inr (mk_case 0 2 rfl h.symm)
      · exact Or.inr (mk_case 1 2 rfl (by rw [h]; rfl))
      · exact Or.inr (mk_case 2 2 rfl (by rw [h]; rfl))
      · exact Or.inr (mk_case 3 2 rfl (by rw [h]; rfl))
      · exact Or.inr (mk_case 4 2 rfl (by rw [h]; rfl))
      · exact Or.inr (mk_case 5 2 rfl (by rw [h]; rfl))
  -- Helper: transport through an automorphism π to a fixed first-gate child
  have transport : ∀ (π πinv : Fin 10 → Fin 10) (g0 : (Fin 10 → Bool) → Bool),
      (∀ i, πinv (π i) = i) → (∀ i, π (πinv i) = i) → (∀ x, f (x ∘ π) = f x) →
      (∀ y : Fin 10 → Bool,
        ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (y ∘ πinv))) =
          List.ofFn (y ∘ πinv) ++ [g0 y]) →
      (∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [g0 x])).getD p false;
        (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
        (∀ x, f x = true → w x u = true ∧ w x v = true) →
        ∃ x, f x = false ∧ w x u = true ∧ w x v = true) →
      ∃ (x13 : Fin 10 → Bool), f x13 = false ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = true ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = true := by
    intro π πinv g0 h1 h2 hpf hg0 hchild
    let remap : ℕ → ℕ := fun k => if hk : k < 10 then (πinv ⟨k, hk⟩).val else k
    let mapGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => ⟨g.op, g.inputs.map remap⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨x2.gates.map mapGate, 0⟩
    have hD_ok : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      simp only [D, List.mem_map] at hg
      rcases hg with ⟨g', hg', rfl⟩
      have h' := hx2_ok g' hg'
      exact ⟨h'.1, by simpa [mapGate] using h'.2⟩
    have hD_sz : D.size ≤ 17 := by
      change (x2.gates.map mapGate).length ≤ 17
      rw [List.length_map]
      exact hx2_sz
    have hwire_eq : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wsA wsB : List Bool),
        wsA.length = wsB.length → 10 ≤ wsA.length →
        (∀ p, wsA.getD (remap p) false = wsB.getD p false) →
        ∀ p, ((gs.map mapGate).foldl step wsA).getD (remap p) false = (gs.foldl step wsB).getD p false := by
      intro gs
      induction gs with
      | nil => intro wsA wsB _ _ hag p; exact hag p
      | cons g rest ih =>
        intro wsA wsB hlen h10l hag p
        simp only [List.map_cons, List.foldl_cons]
        have hstep_val : (mapGate g).op.eval ((mapGate g).inputs.map (fun i => wsA.getD i false)) =
            g.op.eval (g.inputs.map (fun i => wsB.getD i false)) := by
          dsimp only [mapGate]
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro q _
          exact hag q
        apply ih (step wsA (mapGate g)) (step wsB g)
          (by simp [step, hlen]) (by simp [step]; omega)
        intro q
        by_cases hq : q < 10
        · have hrq : remap q < 10 := by dsimp only [remap]; rw [dif_pos hq]; exact (πinv ⟨q, hq⟩).isLt
          dsimp only [step]
          rw [List.getD_append _ _ _ _ (by omega : remap q < wsA.length),
              List.getD_append _ _ _ _ (by omega : q < wsB.length)]
          exact hag q
        · have hrq : remap q = q := by dsimp only [remap]; rw [dif_neg hq]
          rw [hrq]
          by_cases hql : q < wsA.length
          · dsimp only [step]
            rw [List.getD_append _ _ _ _ hql, List.getD_append _ _ _ _ (by omega : q < wsB.length)]
            simpa only [hrq] using hag q
          · by_cases hqe : q = wsA.length
            · dsimp only [step]
              rw [hqe, getD_snoc_end, hlen, getD_snoc_end]
              exact hstep_val
            · dsimp only [step]
              rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp [hlen]; omega)]
    have hD_eval : ∀ (y : Fin 10 → Bool) (p : ℕ),
        (D.wires (List.ofFn y ++ [g0 y])).getD (remap p) false =
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (y ∘ πinv)))).getD p false := by
      intro y p
      rw [hg0 y]
      apply hwire_eq x2.gates (List.ofFn y ++ [g0 y]) (List.ofFn (y ∘ πinv) ++ [g0 y]) (by simp) (by simp)
      intro q
      by_cases hq : q < 10
      · have hrq : remap q = (πinv ⟨q, hq⟩).val := by dsimp only [remap]; rw [dif_pos hq]
        rw [hrq, List.getD_append _ _ _ _ (by simp [(πinv ⟨q, hq⟩).isLt]),
            List.getD_eq_getElem _ _ (by simp [(πinv ⟨q, hq⟩).isLt]), List.getElem_ofFn,
            List.getD_append _ _ _ _ (by simp [hq]),
            List.getD_eq_getElem _ _ (by simp [hq]), List.getElem_ofFn]
        rfl
      · have hrq : remap q = q := by dsimp only [remap]; rw [dif_neg hq]
        rw [hrq]
        by_cases hq10 : q = 10
        · subst hq10
          have hA : (List.ofFn y ++ [g0 y]).getD 10 false = g0 y := by
            simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn y) (g0 y) false
          have hB : (List.ofFn (y ∘ πinv) ++ [g0 y]).getD 10 false = g0 y := by
            simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn (y ∘ πinv)) (g0 y) false
          rw [hA, hB]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    have hpinv_f : ∀ y, f (y ∘ πinv) = f y := by
      intro y
      have hc : (y ∘ πinv) ∘ π = y := by funext i; simp [Function.comp, h1]
      rw [← hpf (y ∘ πinv), hc]
    have hinv_comp : ∀ x : Fin 10 → Bool, (x ∘ π) ∘ πinv = x := by
      intro x; funext i; simp [Function.comp, h2]
    obtain ⟨y, hfy, hy3, hy4⟩ := hchild D (remap x3) (remap x4) hD_ok hD_sz
      (by rcases h10 with ⟨x, hx3, hx4⟩; exact ⟨x ∘ π, by dsimp only; rw [hD_eval, hinv_comp]; exact hx3, by dsimp only; rw [hD_eval, hinv_comp]; exact hx4⟩)
      (by rcases h11 with ⟨x, hx3, hx4⟩; exact ⟨x ∘ π, by dsimp only; rw [hD_eval, hinv_comp]; exact hx3, by dsimp only; rw [hD_eval, hinv_comp]; exact hx4⟩)
      (by intro y hfy; dsimp only; rw [hD_eval, hD_eval]; exact h12 (y ∘ πinv) (by change f (y ∘ πinv) = true; rw [hpinv_f]; exact hfy))
    refine ⟨y ∘ πinv, by rw [hpinv_f]; exact hfy, ?_, ?_⟩
    · rw [← hD_eval y x3]; exact hy3
    · rw [← hD_eval y x4]; exact hy4
  -- Case split on the first gate x1
  have hx1_prop := hx1_ok x1 List.mem_cons_self
  have h1step : ∀ x : Fin 10 → Bool,
      ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x)) =
        List.ofFn x ++ [x1.op.eval (x1.inputs.map (fun i => (List.ofFn x).getD i false))] := fun _ => rfl
  have hgetD_in : ∀ (x : Fin 10 → Bool) (k : ℕ),
      (List.ofFn x).getD k false = if hk : k < 10 then x ⟨k, hk⟩ else false := by
    intro x k
    by_cases hk : k < 10
    · rw [dif_pos hk, List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
    · rw [dif_neg hk, List.getD_eq_default _ _ (by simp; omega)]
  rcases hx1_prop.1 with hop | hop | hop
  · -- x1.op = .and
    cases hg : x1.inputs with
    | nil =>
      exact degen_elim (Sum.inl true) trivial (fun x => by
        rw [h1step, hop, hg]; simp only [List.map_nil, eval_and, List.all_nil, evalSym, Sum.elim_inl, id])
    | cons u t1 =>
      cases t1 with
      | nil =>
        by_cases hu : u < 10
        · exact degen_elim (Sum.inr u) hu (fun x => by
            rw [h1step, hop, hg]
            simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true, evalSym, Sum.elim_inr])
        · exact degen_elim (Sum.inl false) trivial (fun x => by
            rw [h1step, hop, hg]
            simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true, evalSym, Sum.elim_inl]
            rw [hgetD_in, dif_neg hu])
      | cons v t2 =>
        cases t2 with
        | nil =>
          by_cases hu : u < 10
          · by_cases hv : v < 10
            · by_cases huv : u = v
              · subst huv
                exact degen_elim (Sum.inr u) hu (fun x => by
                  rw [h1step, hop, hg]
                  simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_self, evalSym, Sum.elim_inr])
              · have hne : (⟨u, hu⟩ : Fin 10) ≠ ⟨v, hv⟩ := fun h => huv (congrArg Fin.val h)
                rcases ex_aut_pair ⟨u, hu⟩ ⟨v, hv⟩ hne with ⟨π, πinv, h1, h2, hpf, hp0, hp1⟩ | ⟨π, πinv, h1, h2, hpf, hp0, hp2⟩
                · refine transport π πinv (fun y => y 0 && y 1) h1 h2 hpf (fun y => ?_) (hAnd true)
                  rw [h1step, hop, hg]
                  simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true,
                    hgetD_in, dif_pos hu, dif_pos hv, Function.comp]
                  have hu0 : πinv ⟨u, hu⟩ = 0 := by rw [← hp0, h1]
                  have hv1 : πinv ⟨v, hv⟩ = 1 := by rw [← hp1, h1]
                  rw [hu0, hv1]
                · refine transport π πinv (fun y => y 0 && y 2) h1 h2 hpf (fun y => ?_) (hAnd false)
                  rw [h1step, hop, hg]
                  simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true,
                    hgetD_in, dif_pos hu, dif_pos hv, Function.comp]
                  have hu0 : πinv ⟨u, hu⟩ = 0 := by rw [← hp0, h1]
                  have hv2 : πinv ⟨v, hv⟩ = 2 := by rw [← hp2, h1]
                  rw [hu0, hv2]
            · exact degen_elim (Sum.inl false) trivial (fun x => by
                rw [h1step, hop, hg]
                simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true, evalSym, Sum.elim_inl]
                rw [hgetD_in x v, dif_neg hv, Bool.and_false])
          · exact degen_elim (Sum.inl false) trivial (fun x => by
              rw [h1step, hop, hg]
              simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true, evalSym, Sum.elim_inl]
              rw [hgetD_in x u, dif_neg hu, Bool.false_and])
        | cons w t3 => have := hx1_prop.2; rw [hg] at this; simp at this
  · -- x1.op = .or
    cases hg : x1.inputs with
    | nil =>
      exact degen_elim (Sum.inl false) trivial (fun x => by
        rw [h1step, hop, hg]; simp only [List.map_nil, eval_or, List.any_nil, evalSym, Sum.elim_inl, id])
    | cons u t1 =>
      cases t1 with
      | nil =>
        by_cases hu : u < 10
        · exact degen_elim (Sum.inr u) hu (fun x => by
            rw [h1step, hop, hg]
            simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false, evalSym, Sum.elim_inr])
        · exact degen_elim (Sum.inl false) trivial (fun x => by
            rw [h1step, hop, hg]
            simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false, evalSym, Sum.elim_inl]
            rw [hgetD_in, dif_neg hu])
      | cons v t2 =>
        cases t2 with
        | nil =>
          by_cases hu : u < 10
          · by_cases hv : v < 10
            · by_cases huv : u = v
              · subst huv
                exact degen_elim (Sum.inr u) hu (fun x => by
                  rw [h1step, hop, hg]
                  simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_self, evalSym, Sum.elim_inr])
              · have hne : (⟨u, hu⟩ : Fin 10) ≠ ⟨v, hv⟩ := fun h => huv (congrArg Fin.val h)
                rcases ex_aut_pair ⟨u, hu⟩ ⟨v, hv⟩ hne with ⟨π, πinv, h1, h2, hpf, hp0, hp1⟩ | ⟨π, πinv, h1, h2, hpf, hp0, hp2⟩
                · refine transport π πinv (fun y => y 0 || y 1) h1 h2 hpf (fun y => ?_) (hOr true)
                  rw [h1step, hop, hg]
                  simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false,
                    hgetD_in, dif_pos hu, dif_pos hv, Function.comp]
                  have hu0 : πinv ⟨u, hu⟩ = 0 := by rw [← hp0, h1]
                  have hv1 : πinv ⟨v, hv⟩ = 1 := by rw [← hp1, h1]
                  rw [hu0, hv1]
                · refine transport π πinv (fun y => y 0 || y 2) h1 h2 hpf (fun y => ?_) (hOr false)
                  rw [h1step, hop, hg]
                  simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false,
                    hgetD_in, dif_pos hu, dif_pos hv, Function.comp]
                  have hu0 : πinv ⟨u, hu⟩ = 0 := by rw [← hp0, h1]
                  have hv2 : πinv ⟨v, hv⟩ = 2 := by rw [← hp2, h1]
                  rw [hu0, hv2]
            · exact degen_elim (Sum.inr u) hu (fun x => by
                rw [h1step, hop, hg]
                simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false, evalSym, Sum.elim_inr]
                rw [hgetD_in x v, dif_neg hv, Bool.or_false])
          · by_cases hv : v < 10
            · exact degen_elim (Sum.inr v) hv (fun x => by
                rw [h1step, hop, hg]
                simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false, evalSym, Sum.elim_inr]
                rw [hgetD_in x u, dif_neg hu, Bool.false_or])
            · exact degen_elim (Sum.inl false) trivial (fun x => by
                rw [h1step, hop, hg]
                simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false, evalSym, Sum.elim_inl]
                rw [hgetD_in x u, dif_neg hu, hgetD_in x v, dif_neg hv]; rfl)
        | cons w t3 => have := hx1_prop.2; rw [hg] at this; simp at this
  · -- x1.op = .not
    cases hg : x1.inputs with
    | nil =>
      exact degen_elim (Sum.inl true) trivial (fun x => by
        rw [h1step, hop, hg]; simp only [List.map_nil, eval_not, List.headD_nil, evalSym, Sum.elim_inl, id]; rfl)
    | cons u t1 =>
      by_cases hu : u < 10
      · obtain ⟨π, πinv, h1, h2, hpf, hp0⟩ := ex_aut_v ⟨u, hu⟩
        refine transport π πinv (fun y => !y 0) h1 h2 hpf (fun y => ?_) hNot
        rw [h1step, hop, hg]
        simp only [List.map_cons, eval_not, List.headD_cons, hgetD_in, dif_pos hu, Function.comp]
        have hu0 : πinv ⟨u, hu⟩ = 0 := by rw [← hp0, h1]
        rw [hu0]
      · exact degen_elim (Sum.inl true) trivial (fun x => by
          rw [h1step, hop, hg]
          simp only [List.map_cons, eval_not, List.headD_cons, evalSym, Sum.elim_inl, id]
          rw [hgetD_in x u, dif_neg hu]; rfl)
