import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_4604_1
    (h_search : ∃ (n : ℕ) (L : Fin n → Finset (Fin n)) (C : Circuit),
      (∀ i : Fin n, i ∈ L i) ∧
      (∀ i j : Fin n, i ≠ j → (L i ∩ L j).card ≤ 1) ∧
      Monotone2 C ∧
      (∀ p l : Fin n, p ∈ L l →
        circuitFun (n + n) C (fun w => decide (w = Fin.castAdd n p ∨ w = Fin.natAdd n l)) = true) ∧
      (∀ A : Finset (Fin n),
        circuitFun (n + n) C (fun w => Fin.addCases (fun p => decide (p ∈ A)) (fun l => decide (∀ p ∈ A, p ∉ L l)) w) = false) ∧
      C.size + 1 < (Finset.univ.sum fun l => (L l).card) + n)
    (h_bridge : ∀ (n : ℕ) (L : Fin n → Finset (Fin n)) (C : Circuit),
      Monotone2 C →
      (∀ p l : Fin n, p ∈ L l →
        circuitFun (n + n) C (fun w => decide (w = Fin.castAdd n p ∨ w = Fin.natAdd n l)) = true) →
      (∀ A : Finset (Fin n),
        circuitFun (n + n) C (fun w => Fin.addCases (fun p => decide (p ∈ A)) (fun l => decide (∀ p ∈ A, p ∉ L l)) w) = false) →
      ∀ x : Fin (n + n) → Bool,
        circuitFun (n + n) C x = decide (∃ p l : Fin n, p ∈ L l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) :
    ∃ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), x4 ∈ x2 x4) ∧ (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x2 x4 ∩ x2 x5).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ (∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x5 ∈ x2 x6 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true)) ∧ x3.size + (1 : ℕ) < (PEqualNP.HeptadCover.incidences x2).card + x1 := by
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
      intro gs g x
      rw [evalGates_append]
      rfl
    have evalGates_length : ∀ (gs : List Gate) (x : List Bool),
        (evalGates gs x).length = x.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro x; simp [evalGates]
      | cons g gs ih =>
        intro x
        change (evalGates gs (wireStep x g)).length = x.length + (gs.length + 1)
        rw [ih]; simp [wireStep]; omega
    have getD_append_left : ∀ {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α), i < l₁.length →
        (l₁ ++ l₂).getD i d = l₁.getD i d := by
      intro α l₁ l₂ i d hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have getD_append_singleton_self : ∀ {α : Type} (l : List α) (a d : α),
        (l ++ [a]).getD l.length d = a := by
      intro α l a d
      simp [List.getD_eq_getElem?_getD]
    have getD_of_le : ∀ {α : Type} (l : List α) (i : ℕ) (d : α), l.length ≤ i →
        l.getD i d = d := by
      intro α l i d hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
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
          rw [hga] at hw
          exact hrb j hlt w hw
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
          · change n + outGates.length < n + (outGates ++ [Gate.mk GateOp.and [k1, k2]]).length
            simp
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
            rw [← hlen]
            exact getD_append_singleton_self _ _ false
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
          · change n + outGates.length < n + (outGates ++ [Gate.mk GateOp.or [k1, k2]]).length
            simp
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
            rw [← hlen]
            exact getD_append_singleton_self _ _ false
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
          · subst heq
            rw [getD_append_singleton_self]
            exact hrb
          · have hge : (st.1 ++ [res.1]).length ≤ w := by simp; omega
            rw [getD_of_le _ _ _ hge]
            trivial
      · intro x w
        have hprelen : (evalGates pre (List.ofFn x)).length = n + pre.length := by
          rw [evalGates_length, List.length_ofFn]
        have houtlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
          rw [evalGates_length, List.length_ofFn]
        rw [evalGates_append_singleton]
        dsimp only [wireStep]
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
            rw [getD_of_le _ _ false hge1, getD_of_le _ _ (Sum.inl false) hge2]
            rfl
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
            intro x
            rw [hop, hins]
            change repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) =
              ((evalGates pre (List.ofFn x)).getD i false && true)
            rw [Bool.and_true]
            exact (h5 x i).symm
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
              intro x
              rw [(hc4 x).2, hop, hins]
              change (repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) &&
                repVal (evalGates st.2 (List.ofFn x)) (st.1.getD j (Sum.inl false))) =
                ((evalGates pre (List.ofFn x)).getD i false &&
                 ((evalGates pre (List.ofFn x)).getD j false && true))
              rw [Bool.and_true, h5 x i, h5 x j]
            | cons k rest3 =>
              simp [hins] at hlen
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
            intro x
            rw [hop, hins]
            change repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) =
              ((evalGates pre (List.ofFn x)).getD i false || false)
            rw [Bool.or_false]
            exact (h5 x i).symm
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
              intro x
              rw [(hc4 x).2, hop, hins]
              change (repVal (evalGates st.2 (List.ofFn x)) (st.1.getD i (Sum.inl false)) ||
                repVal (evalGates st.2 (List.ofFn x)) (st.1.getD j (Sum.inl false))) =
                ((evalGates pre (List.ofFn x)).getD i false ||
                 ((evalGates pre (List.ofFn x)).getD j false || false))
              rw [Bool.or_false, h5 x i, h5 x j]
            | cons k rest3 =>
              simp [hins] at hlen
    have inv_init : Inv [] initState := by
      refine ⟨by simp [initState], by simp [initState], ?_, ?_, ?_⟩
      · refine ⟨by intro g hg; simp [initState] at hg,
                by intro j hj; simp [initState] at hj,
                by intro g hg; simp [initState] at hg⟩
      · intro w
        dsimp only [initState]
        by_cases hw : w < n
        · have hlt : w < (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length := by
            simp [hw]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
          simpa [repBound] using hw
        · have hge : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by
            simp; omega
          rw [getD_of_le _ _ _ hge]
          trivial
      · intro x w
        dsimp only [initState, evalGates]
        rw [List.foldl_nil]
        by_cases hw : w < n
        · have hlt2 : w < (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length := by
            simp [hw]
          have hget : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).getD w (Sum.inl false) = Sum.inr w := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2, Option.getD_some, List.getElem_ofFn]
          rw [hget]
          rfl
        · have hge1 : (List.ofFn x).length ≤ w := by simp; omega
          have hge2 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by
            simp; omega
          rw [getD_of_le _ _ _ hge1, getD_of_le _ _ _ hge2]
          rfl
    have inv_foldl : ∀ (rest pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
        (∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        Inv pre st →
        Inv (pre ++ rest) (rest.foldl stepGate st) := by
      intro rest
      induction rest with
      | nil => intro pre st _ hinv; simpa using hinv
      | cons g rest ih =>
        intro pre st hm hinv
        have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hm g (by simp)
        have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hm g' (by simp [hg'])
        have hstep : Inv (pre ++ [g]) (stepGate st g) := inv_step pre st g hg hinv
        have hrec := ih (pre ++ [g]) (stepGate st g) hrest hstep
        simpa [List.append_assoc] using hrec
    let st := C.gates.foldl stepGate initState
    have hinv : Inv C.gates st := by
      simpa using inv_foldl C.gates [] initState hmono inv_init
    rcases hinv with ⟨_, hsz, hao, _, hev⟩
    cases hr : st.1.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | true =>
        have h0 := hev (fun _ : Fin n => Bool.false) C.output
        rw [hr] at h0
        simp only [repVal] at h0
        have hc : C.eval (List.ofFn (fun _ : Fin n => Bool.false)) = Bool.true := h0
        rw [hCfalse] at hc
        exact Bool.noConfusion hc
      | false =>
        refine ⟨⟨st.2, n + st.2.length⟩, isAO2_change_output st.2 0 _ hao, hsz, ?_⟩
        intro x
        have hx := hev x C.output
        rw [hr] at hx
        simp only [repVal] at hx
        have hlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
          rw [evalGates_length, List.length_ofFn]
        have hout : Circuit.eval ⟨st.2, n + st.2.length⟩ (List.ofFn x) = Bool.false := by
          change (evalGates st.2 (List.ofFn x)).getD (n + st.2.length) false = false
          rw [← hlen]
          exact getD_of_le _ _ false (Nat.le_refl _)
        exact hout.trans hx.symm
    | inr k =>
      refine ⟨⟨st.2, k⟩, isAO2_change_output st.2 0 k hao, hsz, ?_⟩
      intro x
      have hx := hev x C.output
      rw [hr] at hx
      simp only [repVal] at hx
      exact hx.symm
  obtain ⟨n, L, C, hdiag, hc4, hmono, hpos, hneg, hsmall⟩ := h_search
  have hfun : ∀ x : Fin (n + n) → Bool,
      circuitFun (n + n) C x =
        decide (∃ p l : Fin n, p ∈ L l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) :=
    h_bridge n L C hmono hpos hneg
  have hCfalse : C.eval (List.ofFn (fun _ : Fin (n + n) => false)) = false := by
    have h0 := hfun (fun _ : Fin (n + n) => false)
    change C.eval (List.ofFn (fun _ : Fin (n + n) => false)) = _ at h0
    rw [h0]
    refine decide_eq_false ?_
    rintro ⟨_, _, _, hp, _⟩
    exact Bool.noConfusion hp
  obtain ⟨D, hDao, hDsz, hDev⟩ := hnorm (n + n) C hmono hCfalse
  have hinc : (incidences L).card = Finset.univ.sum (fun l : Fin n => (L l).card) := by
    have heq : incidences L = Finset.univ.biUnion (fun l : Fin n => (L l).image (fun p => (p, l))) := by
      ext pl
      rcases pl with ⟨p, l⟩
      change (p, l) ∈ Finset.univ.filter (fun pl : Fin n × Fin n => pl.1 ∈ L pl.2) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · intro hp
        exact ⟨l, p, hp, rfl, rfl⟩
      · rintro ⟨l', p', hp', rfl, rfl⟩
        exact hp'
    rw [heq, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro l _
      exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)
    · intro l1 _ l2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro pl h1 h2
      rcases Finset.mem_image.mp h1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨p2, _, h2'⟩
      exact hne (Prod.mk.inj h2').2.symm
  refine ⟨n, L, D, hdiag, hc4, hDao, ?_, ?_⟩
  · intro x
    change D.eval (List.ofFn x) = _
    rw [hDev x]
    exact hfun x
  · rw [hinc]
    omega
