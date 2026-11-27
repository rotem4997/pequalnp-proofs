import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4291_1
    (h_line : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
      IsAO2 (N + N) D →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) D (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
        (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) D x = false) →
      Fintype.card { e : Fin N × Fin N //
        I e.1 e.2 ∧ lineSingle D (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = true } ≤ 38 * D.size)
    (h_point : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
      IsAO2 (N + N) D →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) D (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
        (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) D x = false) →
      Fintype.card { e : Fin N × Fin N //
        I e.1 e.2 ∧ lineSingle D (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = true } ≤ 38 * D.size)
    (h_dbl : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
      IsAO2 (N + N) D →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) D (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
        (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) D x = false) →
      Fintype.card { e : Fin N × Fin N //
        I e.1 e.2 ∧
        lineSingle D (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = false ∧
        lineSingle D (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = false } ≤ 24 * D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.false (x12 + x20) ∧ x22 ∈ x19 Bool.false (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.false (x12 + x20) = x19 Bool.false x23 ∪ x19 Bool.false x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  have hmono_eval : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) →
        circuitFun n C x = true → circuitFun n C y = true := by
    intro n C hmono x y hxy hcx
    let ws (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hfold : ∀ (gs : List Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        w1.length = w2.length →
        (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
        ∀ i : ℕ, (gs.foldl ws w1).getD i false = true → (gs.foldl ws w2).getD i false = true := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ hle i hi; exact hle i hi
      | cons g gs ih =>
        intro w1 w2 hm hlen hle
        have hg := hm g List.mem_cons_self
        have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
        have hbit : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
            g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
          rcases hop' with hop | hop
          · rw [hop]
            intro h1
            change (g.inputs.map fun i => w1.getD i false).all id = true at h1
            change (g.inputs.map fun i => w2.getD i false).all id = true
            rw [List.all_eq_true] at h1 ⊢
            intro b hb
            rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
            exact hle j (h1 (w1.getD j false) (List.mem_map.mpr ⟨j, hj, rfl⟩))
          · rw [hop]
            intro h1
            change (g.inputs.map fun i => w1.getD i false).any id = true at h1
            change (g.inputs.map fun i => w2.getD i false).any id = true
            rw [List.any_eq_true] at h1 ⊢
            rcases h1 with ⟨b, hb, hbt⟩
            rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
            exact ⟨w2.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hle j hbt⟩
        apply ih (ws w1 g) (ws w2 g) (fun g' hg' => hm g' (List.mem_cons_of_mem g hg'))
        · simp [ws, hlen]
        · intro i hi
          dsimp only [ws] at hi ⊢
          by_cases hlt : i < w1.length
          · have hlt2 : i < w2.length := hlen ▸ hlt
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
            exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
          · by_cases heq : i = w1.length
            · subst heq
              have h1' : (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).getD w1.length false =
                  g.op.eval (g.inputs.map fun i => w1.getD i false) := by
                simp [List.getD_eq_getElem?_getD]
              have h2' : (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).getD w1.length false =
                  g.op.eval (g.inputs.map fun i => w2.getD i false) := by
                rw [hlen]; simp [List.getD_eq_getElem?_getD]
              rw [h1'] at hi
              rw [h2']
              exact hbit hi
            · have hge1 : (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).length ≤ i := by
                simp; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1] at hi
              exact Bool.noConfusion hi
    have hinit : ∀ i : ℕ, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      intro i hi
      by_cases hlt : i < n
      · have hlt1 : i < (List.ofFn x).length := by simp [hlt]
        have hlt2 : i < (List.ofFn y).length := by simp [hlt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt1, Option.getD_some, List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2, Option.getD_some, List.getElem_ofFn]
        exact hxy ⟨i, hlt⟩ hi
      · have hge1 : (List.ofFn x).length ≤ i := by simp; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1] at hi
        exact Bool.noConfusion hi
    exact hfold C.gates (List.ofFn x) (List.ofFn y) hmono (by simp) hinit C.output hcx
  have hnorm : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      C.eval (List.ofFn (fun _ : Fin n => false)) = false →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro n C hmono hCfalse
    let wireStep (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let evalGates (gs : List Gate) (x : List Bool) : List Bool :=
      gs.foldl wireStep x
    have evalGates_append : ∀ (gs₁ gs₂ : List Gate) (x : List Bool),
        evalGates (gs₁ ++ gs₂) x = evalGates gs₂ (evalGates gs₁ x) :=
      fun _ _ _ => List.foldl_append
    have evalGates_append_singleton : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
        evalGates (gs ++ [g]) x = wireStep (evalGates gs x) g := by
      intro gs g x; rw [evalGates_append]; rfl
    have evalGates_length : ∀ (gs : List Gate) (x : List Bool),
        (evalGates gs x).length = x.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro x; simp [evalGates]
      | cons g gs ih =>
        intro x; change (evalGates gs (wireStep x g)).length = x.length + (gs.length + 1)
        rw [ih]; simp [wireStep]; omega
    have getD_append_left : ∀ {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α), i < l₁.length →
        (l₁ ++ l₂).getD i d = l₁.getD i d := by
      intro α l₁ l₂ i d hi; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have getD_append_singleton_self : ∀ {α : Type} (l : List α) (a d : α),
        (l ++ [a]).getD l.length d = a := by
      intro α l a d; simp [List.getD_eq_getElem?_getD]
    have getD_of_le : ∀ {α : Type} (l : List α) (i : ℕ) (d : α), l.length ≤ i →
        l.getD i d = d := by
      intro α l i d hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    let repVal (outWires : List Bool) : Bool ⊕ ℕ → Bool :=
      Sum.elim id (fun k => outWires.getD k false)
    let repBound (bound : ℕ) : Bool ⊕ ℕ → Prop :=
      Sum.elim (fun _ => True) (fun k => k < bound)
    have repBound_mono : ∀ {b₁ b₂ : ℕ} {r : Bool ⊕ ℕ}, b₁ ≤ b₂ → repBound b₁ r → repBound b₂ r := by
      intro b₁ b₂ r h hr
      cases r with
      | inl _ => trivial
      | inr k => exact Nat.lt_of_lt_of_le hr h
    have repVal_append : ∀ (w₁ w₂ : List Bool) (r : Bool ⊕ ℕ), repBound w₁.length r →
        repVal (w₁ ++ w₂) r = repVal w₁ r := by
      intro w₁ w₂ r hr
      cases r with
      | inl _ => rfl
      | inr k => exact getD_append_left w₁ w₂ k false hr
    let combineAnd (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ) : (Bool ⊕ ℕ) × List Gate :=
      Sum.elim
        (fun b1 => cond b1 (r2, outGates) (Sum.inl false, outGates))
        (fun k1 => Sum.elim
          (fun b2 => cond b2 (Sum.inr k1, outGates) (Sum.inl false, outGates))
          (fun k2 => (Sum.inr (n + outGates.length), outGates ++ [Gate.mk GateOp.and [k1, k2]]))
          r2)
        r1
    let combineOr (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ) : (Bool ⊕ ℕ) × List Gate :=
      Sum.elim
        (fun b1 => cond b1 (Sum.inl true, outGates) (r2, outGates))
        (fun k1 => Sum.elim
          (fun b2 => cond b2 (Sum.inl true, outGates) (Sum.inr k1, outGates))
          (fun k2 => (Sum.inr (n + outGates.length), outGates ++ [Gate.mk GateOp.or [k1, k2]]))
          r2)
        r1
    let stepGate (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
      let getR := fun i => st.1.getD i (Sum.inl false)
      let res : (Bool ⊕ ℕ) × List Gate :=
        GateOp.casesOn g.op
          (List.casesOn g.inputs (Sum.inl true, st.2) fun i l1 =>
            List.casesOn l1 (getR i, st.2) fun j l2 =>
              List.casesOn l2 (combineAnd st.2 (getR i) (getR j)) fun _ _ => (Sum.inl false, st.2))
          (List.casesOn g.inputs (Sum.inl false, st.2) fun i l1 =>
            List.casesOn l1 (getR i, st.2) fun j l2 =>
              List.casesOn l2 (combineOr st.2 (getR i) (getR j)) fun _ _ => (Sum.inl false, st.2))
          (Sum.inl false, st.2)
          (fun _ => (Sum.inl false, st.2))
          (Sum.inl false, st.2)
      (st.1 ++ [res.1], res.2)
    let initState : List (Bool ⊕ ℕ) × List Gate :=
      (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ)), [])
    let Inv (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) : Prop :=
      st.1.length = n + gs.length ∧
      st.2.length ≤ gs.length ∧
      IsAO2 n ⟨st.2, 0⟩ ∧
      (∀ w : ℕ, repBound (n + st.2.length) (st.1.getD w (Sum.inl false))) ∧
      (∀ (x : Fin n → Bool) (w : ℕ),
        (evalGates gs (List.ofFn x)).getD w false =
          repVal (evalGates st.2 (List.ofFn x)) (st.1.getD w (Sum.inl false)))
    have isAO2_change_output : ∀ (gs : List Gate) (o₁ o₂ : ℕ), IsAO2 n ⟨gs, o₁⟩ → IsAO2 n ⟨gs, o₂⟩ :=
      fun _ _ _ h => h
    have isAO2_append_singleton : ∀ (gs : List Gate) (op : GateOp) (k1 k2 : ℕ),
        IsAO2 n ⟨gs, 0⟩ → (op = GateOp.and ∨ op = GateOp.or) →
        k1 < n + gs.length → k2 < n + gs.length →
        IsAO2 n ⟨gs ++ [Gate.mk op [k1, k2]], 0⟩ := by
      intro gs op k1 k2 h hop hk1 hk2
      rcases h with ⟨hao, hrb, hlen⟩
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hao g hg
        · exact hop
      · intro j hj w hw
        have hj' : j < gs.length + 1 := by simpa using hj
        by_cases hlt : j < gs.length
        · have hga : gateAt ⟨gs ++ [Gate.mk op [k1, k2]], 0⟩ j = gateAt ⟨gs, 0⟩ j :=
            getD_append_left gs [Gate.mk op [k1, k2]] j ⟨GateOp.or, []⟩ hlt
          rw [hga] at hw; exact hrb j hlt w hw
        · have heq : j = gs.length := by omega
          subst heq
          have hga : gateAt ⟨gs ++ [Gate.mk op [k1, k2]], 0⟩ gs.length = Gate.mk op [k1, k2] :=
            getD_append_singleton_self gs (Gate.mk op [k1, k2]) ⟨GateOp.or, []⟩
          rw [hga] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hk1
          · exact hk2
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hlen g hg
        · rfl
    have combineAnd_spec : ∀ (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ),
        IsAO2 n ⟨outGates, 0⟩ →
        repBound (n + outGates.length) r1 →
        repBound (n + outGates.length) r2 →
        let res := combineAnd outGates r1 r2
        (outGates.length ≤ res.2.length ∧ res.2.length ≤ outGates.length + 1) ∧
        IsAO2 n ⟨res.2, 0⟩ ∧
        repBound (n + res.2.length) res.1 ∧
        (∀ x : Fin n → Bool,
          (∃ tail : List Bool, evalGates res.2 (List.ofFn x) = evalGates outGates (List.ofFn x) ++ tail) ∧
          repVal (evalGates res.2 (List.ofFn x)) res.1 =
            (repVal (evalGates outGates (List.ofFn x)) r1 && repVal (evalGates outGates (List.ofFn x)) r2)) := by
      intro outGates r1 r2 hao hr1 hr2
      cases r1 with
      | inl b1 =>
        cases b1 with
        | false =>
          refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, trivial, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
        | true =>
          refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, hr2, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
      | inr k1 =>
        cases r2 with
        | inl b2 =>
          cases b2 with
          | false =>
            refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, trivial, ?_⟩
            intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
          | true =>
            refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, hr1, ?_⟩
            intro x; exact ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩
        | inr k2 =>
          refine ⟨⟨by simp [combineAnd], by simp [combineAnd]⟩, ?_, ?_, ?_⟩
          · exact isAO2_append_singleton outGates GateOp.and k1 k2 hao (Or.inl rfl) hr1 hr2
          · change n + outGates.length < n + (outGates ++ [Gate.mk GateOp.and [k1, k2]]).length; simp
          · intro x
            have hstep : evalGates (outGates ++ [Gate.mk GateOp.and [k1, k2]]) (List.ofFn x) =
                evalGates outGates (List.ofFn x) ++
                  [(evalGates outGates (List.ofFn x)).getD k1 false &&
                   (evalGates outGates (List.ofFn x)).getD k2 false] := by
              rw [evalGates_append_singleton]
              change evalGates outGates (List.ofFn x) ++
                [((evalGates outGates (List.ofFn x)).getD k1 false &&
                  ((evalGates outGates (List.ofFn x)).getD k2 false && true))] = _
              rw [Bool.and_true]
            refine ⟨⟨[(evalGates outGates (List.ofFn x)).getD k1 false &&
                      (evalGates outGates (List.ofFn x)).getD k2 false], hstep⟩, ?_⟩
            change (evalGates (outGates ++ [Gate.mk GateOp.and [k1, k2]]) (List.ofFn x)).getD
              (n + outGates.length) false =
              ((evalGates outGates (List.ofFn x)).getD k1 false &&
               (evalGates outGates (List.ofFn x)).getD k2 false)
            rw [hstep]
            have hlen : (evalGates outGates (List.ofFn x)).length = n + outGates.length := by
              rw [evalGates_length, List.length_ofFn]
            rw [← hlen]; exact getD_append_singleton_self _ _ false
    have combineOr_spec : ∀ (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ),
        IsAO2 n ⟨outGates, 0⟩ →
        repBound (n + outGates.length) r1 →
        repBound (n + outGates.length) r2 →
        let res := combineOr outGates r1 r2
        (outGates.length ≤ res.2.length ∧ res.2.length ≤ outGates.length + 1) ∧
        IsAO2 n ⟨res.2, 0⟩ ∧
        repBound (n + res.2.length) res.1 ∧
        (∀ x : Fin n → Bool,
          (∃ tail : List Bool, evalGates res.2 (List.ofFn x) = evalGates outGates (List.ofFn x) ++ tail) ∧
          repVal (evalGates res.2 (List.ofFn x)) res.1 =
            (repVal (evalGates outGates (List.ofFn x)) r1 || repVal (evalGates outGates (List.ofFn x)) r2)) := by
      intro outGates r1 r2 hao hr1 hr2
      cases r1 with
      | inl b1 =>
        cases b1 with
        | true =>
          refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, trivial, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
        | false =>
          refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, hr2, ?_⟩
          intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
      | inr k1 =>
        cases r2 with
        | inl b2 =>
          cases b2 with
          | true =>
            refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, trivial, ?_⟩
            intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
          | false =>
            refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, hao, hr1, ?_⟩
            intro x; exact ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩
        | inr k2 =>
          refine ⟨⟨by simp [combineOr], by simp [combineOr]⟩, ?_, ?_, ?_⟩
          · exact isAO2_append_singleton outGates GateOp.or k1 k2 hao (Or.inr rfl) hr1 hr2
          · change n + outGates.length < n + (outGates ++ [Gate.mk GateOp.or [k1, k2]]).length; simp
          · intro x
            have hstep : evalGates (outGates ++ [Gate.mk GateOp.or [k1, k2]]) (List.ofFn x) =
                evalGates outGates (List.ofFn x) ++
                  [(evalGates outGates (List.ofFn x)).getD k1 false ||
                   (evalGates outGates (List.ofFn x)).getD k2 false] := by
              rw [evalGates_append_singleton]
              change evalGates outGates (List.ofFn x) ++
                [((evalGates outGates (List.ofFn x)).getD k1 false ||
                  ((evalGates outGates (List.ofFn x)).getD k2 false || false))] = _
              rw [Bool.or_false]
            refine ⟨⟨[(evalGates outGates (List.ofFn x)).getD k1 false ||
                      (evalGates outGates (List.ofFn x)).getD k2 false], hstep⟩, ?_⟩
            change (evalGates (outGates ++ [Gate.mk GateOp.or [k1, k2]]) (List.ofFn x)).getD
              (n + outGates.length) false =
              ((evalGates outGates (List.ofFn x)).getD k1 false ||
               (evalGates outGates (List.ofFn x)).getD k2 false)
            rw [hstep]
            have hlen : (evalGates outGates (List.ofFn x)).length = n + outGates.length := by
              rw [evalGates_length, List.length_ofFn]
            rw [← hlen]; exact getD_append_singleton_self _ _ false
    have inv_step_aux : ∀ (pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
        (res : (Bool ⊕ ℕ) × List Gate),
        Inv pre st →
        (st.2.length ≤ res.2.length ∧ res.2.length ≤ st.2.length + 1) →
        IsAO2 n ⟨res.2, 0⟩ →
        repBound (n + res.2.length) res.1 →
        (∀ x : Fin n → Bool,
          ∃ tail : List Bool, evalGates res.2 (List.ofFn x) = evalGates st.2 (List.ofFn x) ++ tail) →
        (∀ x : Fin n → Bool,
          repVal (evalGates res.2 (List.ofFn x)) res.1 =
            g.op.eval (g.inputs.map fun i => (evalGates pre (List.ofFn x)).getD i false)) →
        Inv (pre ++ [g]) (st.1 ++ [res.1], res.2) := by
      intro pre st g res hinv hlen_b hao hrb htail hval
      rcases hinv with ⟨h1, h2, _, h4, h5⟩
      rcases hlen_b with ⟨hlen_le, hlen_step⟩
      refine ⟨?_, ?_, hao, ?_, ?_⟩
      · simp [h1]; omega
      · simp; omega
      · intro w
        by_cases hw : w < st.1.length
        · rw [getD_append_left st.1 [res.1] w (Sum.inl false) hw]
          exact repBound_mono (by dsimp only; omega) (h4 w)
        · by_cases heq : w = st.1.length
          · subst heq; rw [getD_append_singleton_self]; exact hrb
          · have hge : (st.1 ++ [res.1]).length ≤ w := by simp; omega
            rw [getD_of_le _ _ _ hge]; trivial
      · intro x w
        have hprelen : (evalGates pre (List.ofFn x)).length = n + pre.length := by
          rw [evalGates_length, List.length_ofFn]
        have houtlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
          rw [evalGates_length, List.length_ofFn]
        rw [evalGates_append_singleton]; dsimp only [wireStep]
        by_cases hw : w < n + pre.length
        · have hw1 : w < (evalGates pre (List.ofFn x)).length := by omega
          have hw2 : w < st.1.length := by omega
          rw [getD_append_left _ _ w false hw1, getD_append_left _ _ w (Sum.inl false) hw2]
          obtain ⟨tail, htx⟩ := htail x
          rw [htx, repVal_append _ tail _ (by rw [houtlen]; exact h4 w)]
          exact h5 x w
        · by_cases heq : w = n + pre.length
          · subst heq
            have h1' : (evalGates pre (List.ofFn x)).length = n + pre.length := hprelen
            rw [← h1', getD_append_singleton_self, h1', ← h1, getD_append_singleton_self]
            exact (hval x).symm
          · have hge1 : (evalGates pre (List.ofFn x) ++
                [g.op.eval (g.inputs.map fun i => (evalGates pre (List.ofFn x)).getD i false)]).length ≤ w := by
              rw [List.length_append, List.length_singleton, hprelen]; omega
            have hge2 : (st.1 ++ [res.1]).length ≤ w := by simp [h1]; omega
            rw [getD_of_le _ _ false hge1, getD_of_le _ _ (Sum.inl false) hge2]; rfl
    have inv_step : ∀ (pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate),
        (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        Inv pre st →
        Inv (pre ++ [g]) (stepGate st g) := by
      intro pre st g hg hinvFull
      rcases hg with ⟨hop, hlen⟩
      have hinv := hinvFull
      rcases hinv with ⟨h1, h2, h3, h4, h5⟩
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
      rcases hop' with hop | hop
      · cases hins : g.inputs with
        | nil =>
          have hst : stepGate st g = (st.1 ++ [Sum.inl true], st.2) := by
            dsimp only [stepGate]; rw [hop, hins]
          rw [hst]
          refine inv_step_aux pre st g (Sum.inl true, st.2) hinvFull
            ⟨Nat.le_refl _, Nat.le_succ _⟩ h3 trivial (fun _ => ⟨[], by simp⟩) ?_
          intro x; rw [hop, hins]; rfl
        | cons i rest =>
          cases rest with
          | nil =>
            have hst : stepGate st g = (st.1 ++ [st.1.getD i (Sum.inl false)], st.2) := by
              dsimp only [stepGate]; rw [hop, hins]
            rw [hst]
            refine inv_step_aux pre st g (st.1.getD i (Sum.inl false), st.2) hinvFull
              ⟨Nat.le_refl _, Nat.le_succ _⟩ h3 (h4 i) (fun _ => ⟨[], by simp⟩) ?_
            intro x; rw [hop, hins]
            change repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) =
              ((evalGates pre (List.ofFn x)).getD i false && true)
            rw [Bool.and_true]; exact (h5 x i).symm
          | cons j rest2 =>
            cases rest2 with
            | nil =>
              have hst : stepGate st g =
                  (st.1 ++ [(combineAnd st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).1],
                   (combineAnd st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).2) := by
                dsimp only [stepGate]; rw [hop, hins]
              rw [hst]
              have hc := combineAnd_spec st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))
                h3 (h4 i) (h4 j)
              rcases hc with ⟨hc1, hc2, hc3, hc4⟩
              refine inv_step_aux pre st g _ hinvFull hc1 hc2 hc3 (fun x => (hc4 x).1) ?_
              intro x; rw [(hc4 x).2, hop, hins]
              change (repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) &&
                repVal (evalGates st.2 (List.ofFn x)) (st.1.getD j (Sum.inl false))) =
                ((evalGates pre (List.ofFn x)).getD i false &&
                 ((evalGates pre (List.ofFn x)).getD j false && true))
              rw [Bool.and_true, h5 x i, h5 x j]
            | cons k rest3 => simp [hins] at hlen
      · cases hins : g.inputs with
        | nil =>
          have hst : stepGate st g = (st.1 ++ [Sum.inl false], st.2) := by
            dsimp only [stepGate]; rw [hop, hins]
          rw [hst]
          refine inv_step_aux pre st g (Sum.inl false, st.2) hinvFull
            ⟨Nat.le_refl _, Nat.le_succ _⟩ h3 trivial (fun _ => ⟨[], by simp⟩) ?_
          intro x; rw [hop, hins]; rfl
        | cons i rest =>
          cases rest with
          | nil =>
            have hst : stepGate st g = (st.1 ++ [st.1.getD i (Sum.inl false)], st.2) := by
              dsimp only [stepGate]; rw [hop, hins]
            rw [hst]
            refine inv_step_aux pre st g (st.1.getD i (Sum.inl false), st.2) hinvFull
              ⟨Nat.le_refl _, Nat.le_succ _⟩ h3 (h4 i) (fun _ => ⟨[], by simp⟩) ?_
            intro x; rw [hop, hins]
            change repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) =
              ((evalGates pre (List.ofFn x)).getD i false || false)
            rw [Bool.or_false]; exact (h5 x i).symm
          | cons j rest2 =>
            cases rest2 with
            | nil =>
              have hst : stepGate st g =
                  (st.1 ++ [(combineOr st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).1],
                   (combineOr st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).2) := by
                dsimp only [stepGate]; rw [hop, hins]
              rw [hst]
              have hc := combineOr_spec st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))
                h3 (h4 i) (h4 j)
              rcases hc with ⟨hc1, hc2, hc3, hc4⟩
              refine inv_step_aux pre st g _ hinvFull hc1 hc2 hc3 (fun x => (hc4 x).1) ?_
              intro x; rw [(hc4 x).2, hop, hins]
              change (repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) ||
                repVal (evalGates st.2 (List.ofFn x)) (st.1.getD j (Sum.inl false))) =
                ((evalGates pre (List.ofFn x)).getD i false ||
                 ((evalGates pre (List.ofFn x)).getD j false || false))
              rw [Bool.or_false, h5 x i, h5 x j]
            | cons k rest3 => simp [hins] at hlen
    have inv_init : Inv [] initState := by
      refine ⟨by simp [initState], by simp [initState], ?_, ?_, ?_⟩
      · refine ⟨by intro g hg; simp [initState] at hg,
                by intro j hj; simp [initState] at hj,
                by intro g hg; simp [initState] at hg⟩
      · intro w; dsimp only [initState]
        by_cases hw : w < n
        · have hlt : w < (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length := by simp [hw]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
          simpa [repBound] using hw
        · have hge : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by simp; omega
          rw [getD_of_le _ _ _ hge]; trivial
      · intro x w; dsimp only [initState, evalGates]; rw [List.foldl_nil]
        by_cases hw : w < n
        · have hlt2 : w < (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length := by simp [hw]
          have hget : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).getD w (Sum.inl false) = Sum.inr w := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2, Option.getD_some, List.getElem_ofFn]
          rw [hget]; rfl
        · have hge1 : (List.ofFn x).length ≤ w := by simp; omega
          have hge2 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by simp; omega
          rw [getD_of_le _ _ _ hge1, getD_of_le _ _ _ hge2]; rfl
    have inv_foldl : ∀ (rest pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
        (∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        Inv pre st → Inv (pre ++ rest) (rest.foldl stepGate st) := by
      intro rest
      induction rest with
      | nil => intro pre st _ hinv; simpa using hinv
      | cons g rest ih =>
        intro pre st hm hinv
        have hg := hm g (by simp)
        have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hm g' (by simp [hg'])
        have hstep := inv_step pre st g hg hinv
        simpa [List.append_assoc] using ih (pre ++ [g]) (stepGate st g) hrest hstep
    let st := C.gates.foldl stepGate initState
    have hinv : Inv C.gates st := by simpa using inv_foldl C.gates [] initState hmono inv_init
    rcases hinv with ⟨_, hsz, hao, _, hev⟩
    cases hr : st.1.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | true =>
        have h0 := hev (fun _ : Fin n => Bool.false) C.output
        rw [hr] at h0; simp only [repVal] at h0
        have hc : C.eval (List.ofFn (fun _ : Fin n => Bool.false)) = Bool.true := h0
        rw [hCfalse] at hc; exact Bool.noConfusion hc
      | false =>
        refine ⟨⟨st.2, n + st.2.length⟩, isAO2_change_output st.2 0 _ hao, hsz, ?_⟩
        intro x
        have hx := hev x C.output; rw [hr] at hx; simp only [repVal] at hx
        have hlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
          rw [evalGates_length, List.length_ofFn]
        have hout : Circuit.eval ⟨st.2, n + st.2.length⟩ (List.ofFn x) = Bool.false := by
          change (evalGates st.2 (List.ofFn x)).getD (n + st.2.length) false = false
          rw [← hlen]; exact getD_of_le _ _ false (Nat.le_refl _)
        exact hout.trans hx.symm
    | inr k =>
      refine ⟨⟨st.2, k⟩, isAO2_change_output st.2 0 k hao, hsz, ?_⟩
      intro x
      have hx := hev x C.output; rw [hr] at hx; simp only [repVal] at hx
      exact hx.symm
  intro q N I instI hq hN hcard huniq s out W n2 e hout hbase hstep hinc_acc hsound_max _
  let pickA (k : Fin s) : ℕ := Classical.choose (hstep k.val k.isLt)
  let pickB (k : Fin s) : ℕ := Classical.choose (Classical.choose_spec (hstep k.val k.isLt))
  have hpick : ∀ k : Fin s, Max.max (pickA k) (pickB k) < n2 + k.val ∧
      W (n2 + k.val) ∈ [W (pickA k) ∪ W (pickB k), W (pickA k), ∅, W (pickA k) ∩ W (pickB k)] :=
    fun k => Classical.choose_spec (Classical.choose_spec (hstep k.val k.isLt))
  let mkGate (k : Fin s) : Gate :=
    let a := pickA k
    let b := pickB k
    if W (n2 + k.val) = W a ∪ W b then Gate.mk GateOp.or [a, b]
    else if W (n2 + k.val) = W a then Gate.mk GateOp.or [a]
    else if W (n2 + k.val) = ∅ then Gate.mk GateOp.or []
    else Gate.mk GateOp.and [a, b]
  let C : Circuit := ⟨List.ofFn mkGate, out⟩
  have hCsz : C.size = s := by change (List.ofFn mkGate).length = s; simp
  have hCmono : Monotone2 C := by
    intro g hg
    rcases List.mem_ofFn.mp hg with ⟨k, rfl⟩
    dsimp only [mkGate]
    by_cases h1 : W (n2 + k.val) = W (pickA k) ∪ W (pickB k)
    · rw [if_pos h1]; exact ⟨by simp, by simp⟩
    · rw [if_neg h1]
      by_cases h2 : W (n2 + k.val) = W (pickA k)
      · rw [if_pos h2]; exact ⟨by simp, by simp⟩
      · rw [if_neg h2]
        by_cases h3 : W (n2 + k.val) = ∅
        · rw [if_pos h3]; exact ⟨by simp, by simp⟩
        · rw [if_neg h3]; exact ⟨by simp, by simp⟩
  let ws (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hCsem : ∀ (x : Fin (N + N) → Bool),
      let xP : Fin N → Bool := fun p => x (Fin.castAdd N p)
      let xL : Fin N → Bool := fun l => x (Fin.natAdd N l)
      ∀ (m : ℕ) (hm : m ≤ s),
        ((C.gates.take m).foldl ws (List.ofFn x)).length = N + N + m ∧
        ∀ w < N + N + m, ((C.gates.take m).foldl ws (List.ofFn x)).getD w false = true ↔ (xP, xL) ∈ W w := by
    intro x xP xL m
    induction m with
    | zero =>
      intro _
      simp only [List.take_zero, List.foldl_nil, List.length_ofFn, Nat.add_zero]
      refine ⟨trivial, ?_⟩
      intro w hw
      have hlt : w < (List.ofFn x).length := by simp [hw]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
      by_cases hwn : w < N
      · have hbi := (hbase ⟨w, hwn⟩).1
        rw [hbi]
        have hcast : (⟨w, hw⟩ : Fin (N + N)) = Fin.castAdd N ⟨w, hwn⟩ := by ext; rfl
        rw [hcast]
        rfl
      · have hwl : w - N < N := by omega
        have hbi := (hbase ⟨w - N, hwl⟩).2
        have heqw : N + (w - N) = w := by omega
        rw [heqw] at hbi
        rw [hbi]
        have hnat : (⟨w, hw⟩ : Fin (N + N)) = Fin.natAdd N ⟨w - N, hwl⟩ := by
          ext; simp; omega
        rw [hnat]
        rfl
    | succ m ih =>
      intro hms
      have hmlt : m < s := Nat.lt_of_succ_le hms
      rcases ih (Nat.le_of_succ_le hms) with ⟨ihlen, ihval⟩
      have hmlt_len : m < C.gates.length := by change m < (List.ofFn mkGate).length; simp [hmlt]
      have htake : C.gates.take (m + 1) = C.gates.take m ++ [C.gates[m]] := List.take_succ_eq_append_getElem hmlt_len
      have hgm : C.gates[m] = mkGate ⟨m, hmlt⟩ := by
        change (List.ofFn mkGate)[m] = mkGate ⟨m, hmlt⟩
        simp only [List.getElem_ofFn]
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hgm]
      dsimp only [ws]
      refine ⟨by rw [List.length_append, List.length_singleton, ihlen]; omega, ?_⟩
      intro w hw
      by_cases hwold : w < N + N + m
      · have hw1 : w < ((C.gates.take m).foldl ws (List.ofFn x)).length := ihlen ▸ hwold
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw1]
        simpa [List.getD_eq_getElem?_getD] using ihval w hwold
      · have hweq : w = N + N + m := by omega
        subst hweq
        have hget : (((C.gates.take m).foldl ws (List.ofFn x)) ++
            [(mkGate ⟨m, hmlt⟩).op.eval ((mkGate ⟨m, hmlt⟩).inputs.map fun i =>
              ((C.gates.take m).foldl ws (List.ofFn x)).getD i false)]).getD (N + N + m) false =
            (mkGate ⟨m, hmlt⟩).op.eval ((mkGate ⟨m, hmlt⟩).inputs.map fun i =>
              ((C.gates.take m).foldl ws (List.ofFn x)).getD i false) := by
          rw [← ihlen]; simp [List.getD_eq_getElem?_getD]
        rw [hget]
        rcases hpick ⟨m, hmlt⟩ with ⟨hmax, hmem⟩
        have ha : pickA ⟨m, hmlt⟩ < N + N + m := lt_of_le_of_lt (le_max_left _ _) hmax
        have hb : pickB ⟨m, hmlt⟩ < N + N + m := lt_of_le_of_lt (le_max_right _ _) hmax
        have hva := ihval (pickA ⟨m, hmlt⟩) ha
        have hvb := ihval (pickB ⟨m, hmlt⟩) hb
        dsimp only [mkGate]
        by_cases h1 : W (n2 + m) = W (pickA ⟨m, hmlt⟩) ∪ W (pickB ⟨m, hmlt⟩)
        · rw [if_pos h1]
          change (((C.gates.take m).foldl ws (List.ofFn x)).getD (pickA ⟨m, hmlt⟩) false ||
            (((C.gates.take m).foldl ws (List.ofFn x)).getD (pickB ⟨m, hmlt⟩) false || false)) = true ↔ _
          rw [Bool.or_false, Bool.or_eq_true, hva, hvb]
          change (xP, xL) ∈ W (pickA ⟨m, hmlt⟩) ∨ (xP, xL) ∈ W (pickB ⟨m, hmlt⟩) ↔ (xP, xL) ∈ W (n2 + m)
          rw [h1]; rfl
        · rw [if_neg h1]
          by_cases h2 : W (n2 + m) = W (pickA ⟨m, hmlt⟩)
          · rw [if_pos h2]
            change (((C.gates.take m).foldl ws (List.ofFn x)).getD (pickA ⟨m, hmlt⟩) false || false) = true ↔ _
            rw [Bool.or_false, hva]
            change (xP, xL) ∈ W (pickA ⟨m, hmlt⟩) ↔ (xP, xL) ∈ W (n2 + m)
            rw [h2]
          · rw [if_neg h2]
            by_cases h3 : W (n2 + m) = ∅
            · rw [if_pos h3]
              change false = true ↔ (xP, xL) ∈ W (n2 + m)
              rw [h3]; simp
            · rw [if_neg h3]
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
              have h4 : W (n2 + m) = W (pickA ⟨m, hmlt⟩) ∩ W (pickB ⟨m, hmlt⟩) := by
                rcases hmem with hm1 | hm2 | hm3 | hm4
                · exact absurd hm1 h1
                · exact absurd hm2 h2
                · exact absurd hm3 h3
                · exact hm4
              change (((C.gates.take m).foldl ws (List.ofFn x)).getD (pickA ⟨m, hmlt⟩) false &&
                (((C.gates.take m).foldl ws (List.ofFn x)).getD (pickB ⟨m, hmlt⟩) false && true)) = true ↔ _
              rw [Bool.and_true, Bool.and_eq_true, hva, hvb]
              change (xP, xL) ∈ W (pickA ⟨m, hmlt⟩) ∧ (xP, xL) ∈ W (pickB ⟨m, hmlt⟩) ↔ (xP, xL) ∈ W (n2 + m)
              rw [h4]; rfl
  have hCeval : ∀ x : Fin (N + N) → Bool,
      circuitFun (N + N) C x = true ↔ ((fun p => x (Fin.castAdd N p)), (fun l => x (Fin.natAdd N l))) ∈ W out := by
    intro x
    have htake_all : C.gates.take s = C.gates := by
      apply List.take_of_length_le
      change (List.ofFn mkGate).length ≤ s
      simp
    have hres := (hCsem x s (Nat.le_refl s)).2 out hout
    rw [htake_all] at hres
    exact hres
  have hCpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true := by
    intro p l hpl
    rw [hCeval]
    have hp_eq : (fun p' : Fin N => decide (Fin.castAdd N p' = Fin.castAdd N p ∨ Fin.castAdd N p' = Fin.natAdd N l)) = e p := by
      funext p'
      have hne : Fin.castAdd N p' ≠ Fin.natAdd N l := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      simp only [hne, or_false, Fin.castAdd_inj, e]
    have hl_eq : (fun l' : Fin N => decide (Fin.natAdd N l' = Fin.castAdd N p ∨ Fin.natAdd N l' = Fin.natAdd N l)) = e l := by
      funext l'
      have hne : Fin.natAdd N l' ≠ Fin.castAdd N p := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      simp only [hne, false_or, Fin.natAdd_inj, e]
    rw [hp_eq, hl_eq]
    exact hinc_acc p l hpl
  have hCsound : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false := by
    intro x hcardL hnoedge
    rw [Bool.eq_false_iff]
    intro hct
    let xL : Fin N → Bool := fun l => x (Fin.natAdd N l)
    let xMax : Fin (N + N) → Bool :=
      Fin.addCases (fun p => decide (¬∃ l : Fin N, I p l ∧ xL l = true)) xL
    have hle : ∀ i : Fin (N + N), x i = true → xMax i = true := by
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro p hp
        dsimp only [xMax]
        rw [Fin.addCases_left]
        refine decide_eq_true ?_
        rintro ⟨l, hpl, hl⟩
        exact hnoedge ⟨p, l, hpl, hp, hl⟩
      · intro l hl
        dsimp only [xMax]
        rw [Fin.addCases_right]
        exact hl
    have hmt : circuitFun (N + N) C xMax = true := hmono_eval (N + N) C hCmono x xMax hle hct
    rw [hCeval] at hmt
    have h1 : (fun p : Fin N => xMax (Fin.castAdd N p)) =
        fun p : Fin N => decide (¬∃ l : Fin N, I p l ∧ xL l = true) := by
      funext p; dsimp only [xMax]; rw [Fin.addCases_left]
    have h2 : (fun l : Fin N => xMax (Fin.natAdd N l)) = xL := by
      funext l; dsimp only [xMax]; rw [Fin.addCases_right]
    rw [h1, h2] at hmt
    exact hsound_max xL hcardL hmt
  have hCfalse : C.eval (List.ofFn (fun _ : Fin (N + N) => false)) = false := by
    apply hCsound (fun _ => false)
    · have hempty : IsEmpty { l : Fin N // (false : Bool) = true } :=
        ⟨fun a => Bool.noConfusion a.2⟩
      rw [Fintype.card_eq_zero]
      exact Nat.zero_le q
    · rintro ⟨_, _, _, hp, _⟩; exact Bool.noConfusion hp
  obtain ⟨D, hDao, hDsz, hDev⟩ := hnorm (N + N) C hCmono hCfalse
  have hDfun : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) D x = circuitFun (N + N) C x := hDev
  have hDpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) D (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true :=
    fun p l hpl => by rw [hDfun]; exact hCpos p l hpl
  have hDsound : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) D x = false :=
    fun x hc hn => by rw [hDfun]; exact hCsound x hc hn
  let E_all := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2
  let E_line := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ lineSingle D (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = true
  let E_point := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ lineSingle D (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = true
  let E_dbl := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧
    lineSingle D (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = false ∧
    lineSingle D (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val) = false
  have h1 : E_line.card ≤ 38 * D.size := by
    rw [← Fintype.card_subtype]
    exact h_line q N I D hq hN hcard huniq hDao hDpos hDsound
  have h2 : E_point.card ≤ 38 * D.size := by
    rw [← Fintype.card_subtype]
    exact h_point q N I D hq hN hcard huniq hDao hDpos hDsound
  have h3 : E_dbl.card ≤ 24 * D.size := by
    rw [← Fintype.card_subtype]
    exact h_dbl q N I D hq hN hcard huniq hDao hDpos hDsound
  have hEcard : E_all.card = N * (q + 1) := by
    have heq : E_all = Finset.univ.biUnion (fun l : Fin N =>
        (Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))) := by
      ext pl
      rcases pl with ⟨p, l⟩
      simp only [E_all, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro hpl; exact ⟨l, p, hpl, rfl, rfl⟩
      · rintro ⟨l', p', hpl', rfl, rfl⟩; exact hpl'
    rw [heq, Finset.card_biUnion]
    · have hsum : (Finset.univ.sum fun l : Fin N =>
          ((Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))).card) =
          Finset.univ.sum fun _ : Fin N => q + 1 := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
        rw [← Fintype.card_subtype]
        exact hcard l
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    · intro l1 _ l2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro pl hmem1 hmem2
      rcases Finset.mem_image.mp hmem1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp hmem2 with ⟨p2, _, hmem2'⟩
      exact hne (Prod.mk.inj hmem2').2.symm
  have hsub : E_all ⊆ E_line ∪ (E_point ∪ E_dbl) := by
    intro e he
    have hI : I e.1 e.2 := (Finset.mem_filter.mp he).2
    cases hl : lineSingle D (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val)
    · cases hp : lineSingle D (N + N) (fun w => decide (w < N)) e.1.val (N + e.2.val)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hl, hp⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hp⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hl⟩)
  have hcov : E_all.card ≤ E_line.card + (E_point.card + E_dbl.card) := by
    calc E_all.card
        ≤ (E_line ∪ (E_point ∪ E_dbl)).card := Finset.card_le_card hsub
      _ ≤ E_line.card + (E_point ∪ E_dbl).card := Finset.card_union_le _ _
      _ ≤ E_line.card + (E_point.card + E_dbl.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
  have hmul : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
