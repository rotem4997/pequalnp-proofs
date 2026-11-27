import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket PEqualNP.MinimumComplex

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5234_2
    (h_p9 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MinimumComplex.Strict 9 C → C.size ≤ 15 → C.output + 1 = 9 + C.size →
      PEqualNP.NotBracket.notCount C ≤ 2 →
      ∃ (y : Fin 9 → Bool), C.eval (List.ofFn y) ≠
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
         y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
         y 6 && y 8 || y 8 && y 5))
    (h_not0 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MinimumComplex.Strict 11 D → PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D →
      D.size = 17 → D.output = 27 → PEqualNP.NotBracket.notCount D = 0 →
      (∀ j < D.size, 11 + j ≠ D.output → ∃ g ∈ D.gates, 11 + j ∈ g.inputs) →
      (∀ g ∈ D.gates, (0 ∈ g.inputs ∨ 2 ∈ g.inputs) → g.op = GateOp.or) →
      (D.gates.countP fun g => g.inputs.contains 0) = 1 →
      (D.gates.countP fun g => g.inputs.contains 2) = 1 →
      (∀ v : Fin 10, 1 ≤ (D.gates.countP fun g => g.inputs.contains v.val) ∧
        (D.gates.countP fun g => g.inputs.contains v.val) ≤ 2) →
      ∃ (x : Fin 10 → Bool), D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (h_not1 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MinimumComplex.Strict 11 D → 17 ≤ D.size → D.size ≤ 18 →
      D.output + 1 = 11 + D.size → PEqualNP.NotBracket.notCount D = 1 →
      (∀ j < D.size, 11 + j ≠ D.output → ∃ g ∈ D.gates, 11 + j ∈ g.inputs) →
      (D.size = 17 → ∀ g ∈ D.gates, (0 ∈ g.inputs ∨ 2 ∈ g.inputs) → g.op = GateOp.or) →
      (gateAt D (D.size - 1)).op ≠ GateOp.not →
      (D.gates.countP fun g => g.inputs.contains 0) + 16 ≤ D.size →
      (D.gates.countP fun g => g.inputs.contains 2) + 16 ≤ D.size →
      (∀ v : Fin 10, 1 ≤ (D.gates.countP fun g => g.inputs.contains v.val) ∧
        (D.gates.countP fun g => g.inputs.contains v.val) + 15 ≤ D.size) →
      ∃ (x : Fin 10 → Bool), D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (h_not2 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MinimumComplex.Strict 11 D → 17 ≤ D.size → D.size ≤ 18 →
      D.output + 1 = 11 + D.size → PEqualNP.NotBracket.notCount D = 2 →
      (∀ j < D.size, 11 + j ≠ D.output → ∃ g ∈ D.gates, 11 + j ∈ g.inputs) →
      (D.size = 17 → ∀ g ∈ D.gates, (0 ∈ g.inputs ∨ 2 ∈ g.inputs) → g.op = GateOp.or) →
      (gateAt D (D.size - 1)).op ≠ GateOp.not →
      (D.gates.countP fun g => g.inputs.contains 0) + 16 ≤ D.size →
      (D.gates.countP fun g => g.inputs.contains 2) + 16 ≤ D.size →
      (∀ v : Fin 10, 1 ≤ (D.gates.countP fun g => g.inputs.contains v.val) ∧
        (D.gates.countP fun g => g.inputs.contains v.val) + 15 ≤ D.size) →
      ∃ (x : Fin 10 → Bool), D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  let p10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

  let p9 : (Fin 9 → Bool) → Bool := fun y =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
    y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
    y 6 && y 8 || y 8 && y 5

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl

  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl

  have eval_not (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl

  let isNot (g : Gate) : Bool :=
    @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)

  have isNot_eq (g : Gate) : (isNot g = true) ↔ g.op = GateOp.not := by
    dsimp only [isNot]
    exact @decide_eq_true_iff (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)

  have filter_part (gs : List Gate) :
      gs.length = (gs.filter isNot).length + (gs.filter fun g => !isNot g).length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.filter_cons]
      cases isNot g <;> simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        List.length_cons] <;> omega

  have wires_start (gs : List Gate) (w : List Bool) :
      ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      rw [List.foldl_cons]
      obtain ⟨t, ht, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hlen]⟩
      rw [ht]; simp [step]

  have wires_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    obtain ⟨t, ht, hlen⟩ := wires_start gs w
    rw [ht, List.length_append, hlen]

  have wires_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wires_start gs w
    rw [ht, List.getD_append _ _ _ _ hi]

  have getD_snoc_end {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    simp [List.getD_eq_getElem?_getD]

  let evalSym (s : Bool ⊕ ℕ) (w : List Bool) : Bool :=
    Sum.elim id (fun k => w.getD k false) s

  let elimNot (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    List.casesOn vs (Sum.inl (Sum.inl true)) (fun v _ =>
      Sum.elim (fun b => Sum.inl (Sum.inl (!b))) (fun k => Sum.inr ⟨GateOp.not, [k]⟩) v)

  let elimAnd (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    List.casesOn vs (Sum.inl (Sum.inl true)) (fun v1 t1 =>
      List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
        List.casesOn t2
          (Sum.elim
            (fun b1 => Bool.casesOn b1 (Sum.inl (Sum.inl false)) (Sum.inl v2))
            (fun k1 => Sum.elim
              (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inl false)) (Sum.inl (Sum.inr k1)))
              (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨GateOp.and, [k1, k2]⟩)
              v2)
            v1)
          (fun _ _ => Sum.inl (Sum.inl false))))

  let elimOr (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    List.casesOn vs (Sum.inl (Sum.inl false)) (fun v1 t1 =>
      List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
        List.casesOn t2
          (Sum.elim
            (fun b1 => Bool.casesOn b1 (Sum.inl v2) (Sum.inl (Sum.inl true)))
            (fun k1 => Sum.elim
              (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inr k1)) (Sum.inl (Sum.inl true)))
              (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨GateOp.or, [k1, k2]⟩)
              v2)
            v1)
          (fun _ _ => Sum.inl (Sum.inl false))))

  let elimGate (op : GateOp) (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
    GateOp.casesOn op
      (elimAnd vs) (elimOr vs) (elimNot vs) (fun _ => Sum.inl (Sum.inl false)) (Sum.inl (Sum.inl false))

  let elimStep (n' : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate :=
    let vs := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    Sum.elim
      (fun sym => (acc.1 ++ [sym], acc.2))
      (fun ng => (acc.1 ++ [Sum.inr (n' + acc.2.length)], acc.2 ++ [ng]))
      (elimGate g.op vs)

  have elimGate_spec (op : GateOp)
      (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (m : ℕ)
      (hbd : ∀ s ∈ vs, ∀ k, s = Sum.inr k → k < m) :
      (∀ sym, elimGate op vs = Sum.inl sym →
        (∀ w : List Bool, evalSym sym w = op.eval (vs.map fun s => evalSym s w)) ∧
        (∀ k, sym = Sum.inr k → Sum.inr k ∈ vs)) ∧
      (∀ ng, elimGate op vs = Sum.inr ng →
        ng.op = op ∧ StrictGate m ng ∧
        (∀ w : List Bool, ng.op.eval (ng.inputs.map fun i => w.getD i false) =
          op.eval (vs.map fun s => evalSym s w))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases vs with
      | nil =>
        exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
          fun ng hng => by cases hng⟩
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          exact ⟨fun sym hs => by
            cases hs
            exact ⟨fun _ => by simp [eval_and], fun k hk => by subst hk; exact List.mem_singleton_self _⟩,
            fun ng hng => by cases hng⟩
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => simp at hlen
          | nil =>
            cases v1 with
            | inl b1 =>
              cases v2 with
              | inl b2 =>
                cases b1 <;> cases b2 <;>
                  exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
                    fun ng hng => by cases hng⟩
              | inr k2 =>
                cases b1 with
                | false =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
                    fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by
                    cases hs
                    exact ⟨fun _ => by simp [evalSym, eval_and],
                      fun k hk => by cases hk; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩,
                    fun ng hng => by cases hng⟩
            | inr k1 =>
              cases v2 with
              | inl b2 =>
                cases b2 with
                | false =>
                  exact ⟨fun sym hs => by
                    cases hs; exact ⟨fun _ => by simp [evalSym, eval_and], fun k hk => by cases hk⟩,
                    fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by
                    cases hs
                    exact ⟨fun _ => by simp [evalSym, eval_and],
                      fun k hk => by cases hk; exact List.mem_cons_self ..⟩,
                    fun ng hng => by cases hng⟩
              | inr k2 =>
                by_cases hk : k1 = k2
                · subst hk
                  refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimAnd, Sum.elim_inr, ↓reduceIte] at hs; cases hs
                    exact ⟨fun _ => by simp [evalSym, eval_and],
                      fun k hk' => by cases hk'; exact List.mem_cons_self ..⟩
                  · simp only [elimGate, elimAnd, Sum.elim_inr, ↓reduceIte] at hng; cases hng
                · refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimAnd, Sum.elim_inr, hk, ↓reduceIte] at hs; cases hs
                  · simp only [elimGate, elimAnd, Sum.elim_inr, hk, ↓reduceIte] at hng; cases hng
                    refine ⟨rfl, Or.inl ⟨Or.inl rfl, rfl, by simp [hk], ?_⟩,
                      fun _ => by simp [evalSym, eval_and]⟩
                    intro i hi
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl
                    · exact hbd (Sum.inr i) (List.mem_cons_self ..) i rfl
                    · exact hbd (Sum.inr i) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) i rfl
    · cases vs with
      | nil =>
        exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
          fun ng hng => by cases hng⟩
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          exact ⟨fun sym hs => by
            cases hs
            exact ⟨fun _ => by simp [eval_or], fun k hk => by subst hk; exact List.mem_singleton_self _⟩,
            fun ng hng => by cases hng⟩
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => simp at hlen
          | nil =>
            cases v1 with
            | inl b1 =>
              cases v2 with
              | inl b2 =>
                cases b1 <;> cases b2 <;>
                  exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
                    fun ng hng => by cases hng⟩
              | inr k2 =>
                cases b1 with
                | false =>
                  exact ⟨fun sym hs => by
                    cases hs
                    exact ⟨fun _ => by simp [evalSym, eval_or],
                      fun k hk => by cases hk; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩,
                    fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
                    fun ng hng => by cases hng⟩
            | inr k1 =>
              cases v2 with
              | inl b2 =>
                cases b2 with
                | false =>
                  exact ⟨fun sym hs => by
                    cases hs
                    exact ⟨fun _ => by simp [evalSym, eval_or],
                      fun k hk => by cases hk; exact List.mem_cons_self ..⟩,
                    fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by
                    cases hs; exact ⟨fun _ => by simp [evalSym, eval_or], fun k hk => by cases hk⟩,
                    fun ng hng => by cases hng⟩
              | inr k2 =>
                by_cases hk : k1 = k2
                · subst hk
                  refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimOr, Sum.elim_inr, ↓reduceIte] at hs; cases hs
                    exact ⟨fun _ => by simp [evalSym, eval_or],
                      fun k hk' => by cases hk'; exact List.mem_cons_self ..⟩
                  · simp only [elimGate, elimOr, Sum.elim_inr, ↓reduceIte] at hng; cases hng
                · refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimOr, Sum.elim_inr, hk, ↓reduceIte] at hs; cases hs
                  · simp only [elimGate, elimOr, Sum.elim_inr, hk, ↓reduceIte] at hng; cases hng
                    refine ⟨rfl, Or.inl ⟨Or.inr rfl, rfl, by simp [hk], ?_⟩,
                      fun _ => by simp [evalSym, eval_or]⟩
                    intro i hi
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl
                    · exact hbd (Sum.inr i) (List.mem_cons_self ..) i rfl
                    · exact hbd (Sum.inr i) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) i rfl
    · cases vs with
      | nil =>
        exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
          fun ng hng => by cases hng⟩
      | cons v1 t1 =>
        cases v1 with
        | inl b1 =>
          exact ⟨fun sym hs => by cases hs; exact ⟨fun _ => rfl, fun k hk => by cases hk⟩,
            fun ng hng => by cases hng⟩
        | inr k1 =>
          refine ⟨(fun sym hs => by cases hs), fun ng hng => ?_⟩
          cases hng
          refine ⟨rfl, Or.inr ⟨rfl, rfl, ?_⟩, fun _ => rfl⟩
          intro i hi
          simp only [List.mem_singleton] at hi
          subst hi
          exact hbd (Sum.inr i) (List.mem_cons_self ..) i rfl

  have elimGate_false_in (op : GateOp) (vs : List (Bool ⊕ ℕ))
      (h : ((op = GateOp.and ∨ op = GateOp.or) ∧ vs.length = 2 ∧ Sum.inl false ∈ vs) ∨
        (op = GateOp.not ∧ vs = [Sum.inl false])) :
      ∃ sym, elimGate op vs = Sum.inl sym := by
    rcases h with ⟨hop, hlen2, hmem⟩ | ⟨rfl, rfl⟩
    · cases vs with
      | nil => cases hlen2
      | cons v1 t1 =>
        cases t1 with
        | nil => cases hlen2
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => cases hlen2
          | nil =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hop with rfl | rfl
            · rcases hmem with rfl | rfl
              · exact ⟨Sum.inl false, rfl⟩
              · cases v1 with
                | inl b1 => cases b1 <;> exact ⟨Sum.inl false, rfl⟩
                | inr k1 => exact ⟨Sum.inl false, rfl⟩
            · rcases hmem with rfl | rfl
              · exact ⟨v2, rfl⟩
              · cases v1 with
                | inl b1 => cases b1 <;> exact ⟨_, rfl⟩
                | inr k1 => exact ⟨Sum.inr k1, rfl⟩
    · exact ⟨Sum.inl true, rfl⟩

  have elimRun_spec (n' : ℕ) (gs : List Gate)
      (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (st0 : List (Bool ⊕ ℕ)) (ngs0 : List Gate)
      (hstr0 : ∀ j (hj : j < ngs0.length), StrictGate (n' + j) ngs0[j])
      (hbd0 : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n' + ngs0.length) :
      let res := gs.foldl (elimStep n') (st0, ngs0)
      (∃ stT, res.1 = st0 ++ stT ∧ stT.length = gs.length) ∧
      (∀ j (hj : j < res.2.length), StrictGate (n' + j) res.2[j]) ∧
      (∀ s ∈ res.1, ∀ k, s = Sum.inr k → k < n' + res.2.length) ∧
      (res.2.filter isNot).length ≤ (ngs0.filter isNot).length + (gs.filter isNot).length ∧
      (res.2.filter fun g => !isNot g).length ≤
        (ngs0.filter fun g => !isNot g).length + (gs.filter fun g => !isNot g).length ∧
      (∀ (wIn w0 : List Bool), wIn.length = n' → w0.length = st0.length →
        (∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD i false) →
        ∀ i < res.1.length,
          evalSym (res.1.getD i (Sum.inl false)) (res.2.foldl step wIn) = (gs.foldl step w0).getD i false) := by
    induction gs generalizing st0 ngs0 with
    | nil =>
      refine ⟨⟨[], by simp, rfl⟩, hstr0, hbd0, by simp, by simp, ?_⟩
      intro wIn w0 _ _ hagree i hi
      exact hagree i hi
    | cons g gs ih =>
      have hg := hfan g (List.mem_cons_self ..)
      have hgs : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
        fun a ha => hfan a (List.mem_cons_of_mem g ha)
      let vs := g.inputs.map fun i => st0.getD i (Sum.inl false)
      have hvs_len : vs.length ≤ 2 := by simp [vs, hg.2]
      have hvs_bd : ∀ s ∈ vs, ∀ k, s = Sum.inr k → k < n' + ngs0.length := by
        intro s hs k hk
        simp only [vs, List.mem_map] at hs
        obtain ⟨idx, _, rfl⟩ := hs
        by_cases hi : idx < st0.length
        · have hmem : st0.getD idx (Sum.inl false) ∈ st0 := by
            rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
          exact hbd0 _ hmem k hk
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hk; cases hk
      have hspec := elimGate_spec g.op hg.1 vs hvs_len (n' + ngs0.length) hvs_bd
      cases heg : elimGate g.op vs with
      | inl sym =>
        have hstep : elimStep n' (st0, ngs0) g = (st0 ++ [sym], ngs0) := by
          dsimp only [elimStep]
          change Sum.elim
            (fun s => (st0 ++ [s], ngs0))
            (fun ng => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng]))
            (elimGate g.op vs) = _
          rw [heg]; rfl
        have hbd1 : ∀ s ∈ st0 ++ [sym], ∀ k, s = Sum.inr k → k < n' + ngs0.length := by
          intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h1
          · exact hbd0 s h1 k hk
          · simp only [List.mem_singleton] at h1; rw [h1] at hk
            exact hvs_bd (Sum.inr k) ((hspec.1 sym heg).2 k hk) k rfl
        rw [List.foldl_cons, hstep]
        obtain ⟨⟨stT, hst, hsl⟩, hstr', hbd', hn1, hn2, hsem⟩ := ih hgs (st0 ++ [sym]) ngs0 hstr0 hbd1
        refine ⟨⟨sym :: stT, by rw [hst]; simp, by simp [hsl]⟩, hstr', hbd', ?_, ?_, ?_⟩
        · simp only [List.filter_cons]
          cases isNot g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
        · simp only [List.filter_cons]
          cases isNot g <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            List.length_cons] <;> omega
        · intro wIn w0 hwIn hw0 hagree
          rw [List.foldl_cons]
          apply hsem wIn (step w0 g) hwIn (by simp [step, hw0])
          intro i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          by_cases hilt : i < st0.length
          · unfold step
            rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w0.length)]
            exact hagree i hilt
          · have hieq : i = st0.length := by omega
            subst hieq
            rw [getD_snoc_end, (hspec.1 sym heg).1 (ngs0.foldl step wIn)]
            simp only [step]
            rw [← hw0, getD_snoc_end]
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro idx _
            change evalSym (st0.getD idx (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD idx false
            by_cases hidx : idx < st0.length
            · exact hagree idx hidx
            · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hidx),
                List.getD_eq_default _ _ (by omega : w0.length ≤ idx)]
              rfl
      | inr ng =>
        have hstep : elimStep n' (st0, ngs0) g = (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng]) := by
          dsimp only [elimStep]
          change Sum.elim
            (fun s => (st0 ++ [s], ngs0))
            (fun ng' => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng']))
            (elimGate g.op vs) = _
          rw [heg]; rfl
        obtain ⟨hng_op, hng_str, hng_ev⟩ := hspec.2 ng heg
        have hstr1 : ∀ j (hj : j < (ngs0 ++ [ng]).length), StrictGate (n' + j) (ngs0 ++ [ng])[j] := by
          intro j hj
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hjlt : j < ngs0.length
          · rw [List.getElem_append_left hjlt]
            exact hstr0 j hjlt
          · have hjeq : j = ngs0.length := by omega
            subst hjeq
            rw [List.getElem_append_right (Nat.le_refl _)]
            simpa only [Nat.sub_self, List.getElem_cons_zero] using hng_str
        have hbd1 : ∀ s ∈ st0 ++ [Sum.inr (n' + ngs0.length)], ∀ k, s = Sum.inr k → k < n' + (ngs0 ++ [ng]).length := by
          intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h1
          · have := hbd0 s h1 k hk; simp; omega
          · simp only [List.mem_singleton] at h1; rw [h1] at hk; cases hk; simp
        rw [List.foldl_cons, hstep]
        obtain ⟨⟨stT, hst, hsl⟩, hstr', hbd', hn1, hn2, hsem⟩ :=
          ih hgs (st0 ++ [Sum.inr (n' + ngs0.length)]) (ngs0 ++ [ng]) hstr1 hbd1
        have hisNot_eq : isNot ng = isNot g := by
          dsimp only [isNot]
          rw [hng_op]
        have hfil1 : ((ngs0 ++ [ng]).filter isNot).length =
            (ngs0.filter isNot).length + (if isNot g then 1 else 0) := by
          rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil, hisNot_eq]
          cases isNot g <;> rfl
        have hfil2 : ((ngs0 ++ [ng]).filter fun a => !isNot a).length =
            (ngs0.filter fun a => !isNot a).length + (if !isNot g then 1 else 0) := by
          rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil, hisNot_eq]
          cases isNot g <;> rfl
        refine ⟨⟨Sum.inr (n' + ngs0.length) :: stT, by rw [hst]; simp, by simp [hsl]⟩,
          hstr', hbd', ?_, ?_, ?_⟩
        · rw [hfil1] at hn1
          simp only [List.filter_cons]
          cases hb : isNot g <;>
            simp only [hb, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hn1 ⊢ <;> omega
        · rw [hfil2] at hn2
          simp only [List.filter_cons]
          cases hb : isNot g <;>
            simp only [hb, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              List.length_cons] at hn2 ⊢ <;> omega
        · intro wIn w0 hwIn hw0 hagree
          rw [List.foldl_cons]
          apply hsem wIn (step w0 g) hwIn (by simp [step, hw0])
          intro i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          have hfold : (ngs0 ++ [ng]).foldl step wIn = step (ngs0.foldl step wIn) ng := by
            rw [List.foldl_append]; rfl
          rw [hfold]
          by_cases hilt : i < st0.length
          · unfold step
            rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w0.length)]
            have hprev := hagree i hilt
            have hmem : st0.getD i (Sum.inl false) ∈ st0 := by
              rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_mem hilt
            cases hs : st0.getD i (Sum.inl false) with
            | inl b => rw [hs] at hprev; exact hprev
            | inr k =>
              have hk : k < (ngs0.foldl step wIn).length := by
                rw [wires_len, hwIn]; exact hbd0 _ hmem k hs
              simp only [evalSym, Sum.elim_inr]
              rw [hs] at hprev
              exact (List.getD_append _ _ _ _ hk).trans hprev
          · have hieq : i = st0.length := by omega
            subst hieq
            rw [getD_snoc_end]
            simp only [evalSym, Sum.elim_inr, step]
            have hlen_w : (ngs0.foldl step wIn).length = n' + ngs0.length := by
              rw [wires_len, hwIn]
            rw [← hlen_w, getD_snoc_end, hng_ev (ngs0.foldl step wIn), ← hw0, getD_snoc_end]
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro idx _
            change evalSym (st0.getD idx (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD idx false
            by_cases hidx : idx < st0.length
            · exact hagree idx hidx
            · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hidx),
                List.getD_eq_default _ _ (by omega : w0.length ≤ idx)]
              rfl

  have elimGate_const_in (op : GateOp) (vs : List (Bool ⊕ ℕ)) (b : Bool)
      (h : ((op = GateOp.and ∨ op = GateOp.or) ∧ vs.length = 2 ∧ Sum.inl b ∈ vs) ∨
        (op = GateOp.not ∧ vs = [Sum.inl b])) :
      ∃ sym, elimGate op vs = Sum.inl sym := by
    cases b
    · exact elimGate_false_in op vs h
    · rcases h with ⟨hop, hlen, hm⟩ | ⟨rfl, rfl⟩
      · obtain ⟨a, c, rfl⟩ : ∃ a c, vs = [a,c] := by
          cases vs with
          | nil => simp at hlen
          | cons a rest =>
            cases rest with
            | nil => simp at hlen
            | cons c tail =>
              obtain rfl : tail = [] := by simpa using hlen
              exact ⟨a,c,rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hop with rfl | rfl
        · rcases hm with h | h
          · subst a
            exact ⟨c, rfl⟩
          · subst c
            cases a with
            | inl a => cases a <;> exact ⟨_, rfl⟩
            | inr a => exact ⟨_, rfl⟩
        · rcases hm with h | h
          · subst a
            exact ⟨Sum.inl true, rfl⟩
          · subst c
            cases a with
            | inl a => cases a <;> exact ⟨_, rfl⟩
            | inr a => exact ⟨_, rfl⟩
      · exact ⟨Sum.inl false, rfl⟩


  have elimRun_drop (n' : ℕ) (gs : List Gate)
      (hshape : ∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1))
      (st0 : List (Bool ⊕ ℕ)) (ngs0 : List Gate) (v : ℕ) (b : Bool)
      (hv_lt : v < st0.length) (hv_false : st0.getD v (Sum.inl false) = Sum.inl b) :
      (gs.foldl (elimStep n') (st0, ngs0)).2.length +
        gs.countP (fun g => g.inputs.contains v) ≤ ngs0.length + gs.length := by
    induction gs generalizing st0 ngs0 with
    | nil => simp
    | cons g gs ih =>
      have hg := hshape g (List.mem_cons_self ..)
      have hgs : ∀ a ∈ gs, ((a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length = 2) ∨
          (a.op = GateOp.not ∧ a.inputs.length = 1) :=
        fun a ha => hshape a (List.mem_cons_of_mem g ha)
      let vs := g.inputs.map fun i => st0.getD i (Sum.inl false)
      by_cases hcv : g.inputs.contains v = true
      · have hv_mem : v ∈ g.inputs := List.contains_iff_mem.mp hcv
        have hfalse_in : ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ vs.length = 2 ∧ Sum.inl b ∈ vs) ∨
            (g.op = GateOp.not ∧ vs = [Sum.inl b]) := by
          rcases hg with ⟨hop, hlen2⟩ | ⟨hop, hlen1⟩
          · refine Or.inl ⟨hop, by simp [vs, hlen2], ?_⟩
            rw [← hv_false]
            exact List.mem_map_of_mem hv_mem
          · refine Or.inr ⟨hop, ?_⟩
            cases hin : g.inputs with
            | nil => simp [hin] at hlen1
            | cons a rest =>
              cases rest with
              | cons _ _ => simp [hin] at hlen1
              | nil =>
                simp only [hin, List.mem_singleton] at hv_mem
                subst hv_mem
                simp only [vs, hin, List.map_cons, List.map_nil, hv_false]
        obtain ⟨sym, hsym⟩ := elimGate_const_in g.op vs b hfalse_in
        have hstep : elimStep n' (st0, ngs0) g = (st0 ++ [sym], ngs0) := by
          dsimp only [elimStep]
          change Sum.elim
            (fun s => (st0 ++ [s], ngs0))
            (fun ng => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng]))
            (elimGate g.op vs) = _
          rw [hsym]; rfl
        have hv_lt1 : v < (st0 ++ [sym]).length := by simp; omega
        have hv_false1 : (st0 ++ [sym]).getD v (Sum.inl false) = Sum.inl b := by
          rw [List.getD_append _ _ _ _ hv_lt, hv_false]
        have hrec := ih hgs (st0 ++ [sym]) ngs0 hv_lt1 hv_false1
        rw [List.foldl_cons, hstep, List.length_cons]
        simp only [List.countP_cons, hcv, ↓reduceIte]
        omega
      · have hcvf : g.inputs.contains v = false := Bool.eq_false_iff.mpr hcv
        cases heg : elimGate g.op vs with
        | inl sym =>
          have hstep : elimStep n' (st0, ngs0) g = (st0 ++ [sym], ngs0) := by
            dsimp only [elimStep]
            change Sum.elim
              (fun s => (st0 ++ [s], ngs0))
              (fun ng => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng]))
              (elimGate g.op vs) = _
            rw [heg]; rfl
          have hrec := ih hgs (st0 ++ [sym]) ngs0 (by simp; omega)
            (by rw [List.getD_append _ _ _ _ hv_lt, hv_false])
          rw [List.foldl_cons, hstep, List.length_cons]
          simp only [List.countP_cons, hcvf, Bool.false_eq_true, ↓reduceIte]
          omega
        | inr ng =>
          have hstep : elimStep n' (st0, ngs0) g = (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng]) := by
            dsimp only [elimStep]
            change Sum.elim
              (fun s => (st0 ++ [s], ngs0))
              (fun ng' => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng']))
              (elimGate g.op vs) = _
            rw [heg]; rfl
          have hrec := ih hgs (st0 ++ [Sum.inr (n' + ngs0.length)]) (ngs0 ++ [ng]) (by simp; omega)
            (by rw [List.getD_append _ _ _ _ hv_lt, hv_false])
          simp only [List.length_append, List.length_cons, List.length_nil] at hrec
          rw [List.foldl_cons, hstep, List.length_cons]
          simp only [List.countP_cons, hcvf, Bool.false_eq_true, ↓reduceIte]
          omega

  have truncStrict (n' : ℕ) (ngs : List Gate) (k : ℕ)
      (hstr : ∀ j (hj : j < ngs.length), StrictGate (n' + j) ngs[j])
      (hlo : n' ≤ k) (hhi : k < n' + ngs.length) :
      let E : Circuit := ⟨ngs.take (k - n' + 1), k⟩
      Strict n' E ∧ E.size ≤ ngs.length ∧ E.output + 1 = n' + E.size ∧
      notCount E ≤ (ngs.filter isNot).length ∧
      (E.gates.filter fun g => !isNot g).length ≤ (ngs.filter fun g => !isNot g).length ∧
      (∀ w : List Bool, w.length = n' → E.eval w = (ngs.foldl step w).getD k false) := by
    let m := k - n' + 1
    have hm_le : m ≤ ngs.length := by omega
    have htake_len : (ngs.take m).length = m := List.length_take_of_le hm_le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      change j < (ngs.take m).length at hj
      have hj_lt : j < ngs.length := lt_of_lt_of_le hj (htake_len.le.trans hm_le)
      rw [List.getElem_take]
      exact hstr j hj_lt
    · change (ngs.take m).length ≤ ngs.length
      exact htake_len.le.trans hm_le
    · change k + 1 = n' + (ngs.take m).length
      rw [htake_len]; omega
    · change ((ngs.take m).filter isNot).length ≤ (ngs.filter isNot).length
      conv_rhs => rw [← List.take_append_drop m ngs, List.filter_append, List.length_append]
      omega
    · change ((ngs.take m).filter fun g => !isNot g).length ≤ (ngs.filter fun g => !isNot g).length
      conv_rhs => rw [← List.take_append_drop m ngs, List.filter_append, List.length_append]
      omega
    · intro w hw
      change ((ngs.take m).foldl step w).getD k false = (ngs.foldl step w).getD k false
      conv_rhs => rw [← List.take_append_drop m ngs, List.foldl_append]
      symm
      apply wires_getD_lt (ngs.drop m) ((ngs.take m).foldl step w) k
      rw [wires_len, hw, htake_len]
      omega

  have compactLength (n : ℕ) (gs : List Gate) (trace : List (Bool ⊕ ℕ))
      (prefixGates : List Gate) :
      ((gs.foldl (elimStep n) (trace, prefixGates)).2).length ≤
        prefixGates.length + gs.countP (fun g => !g.inputs.isEmpty) := by
    induction gs generalizing trace prefixGates with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, List.countP_cons]
      generalize he : elimGate g.op (g.inputs.map fun i => trace.getD i (Sum.inl false)) = out
      cases out with
      | inl s =>
        simpa only [elimStep, he, Sum.elim_inl] using
          (ih (trace ++ [s]) prefixGates).trans (by omega)
      | inr gate =>
        have nonempty : g.inputs.isEmpty = false := by
          cases hh : g.inputs with
          | nil =>
            rw [hh] at he
            generalize g.op = op at he
            cases op <;> simp [elimGate, elimAnd, elimOr, elimNot] at he
          | cons _ _ => rfl
        simp only [elimStep, he, Sum.elim_inr, nonempty, Bool.not_false, ↓reduceIte]
        have := ih (trace ++ [Sum.inr (n+prefixGates.length)]) (prefixGates ++ [gate])
        simp only [elimStep, List.length_append, List.length_singleton] at this
        omega

  have absorbing (g : Gate) (st : List (Bool ⊕ ℕ)) (v : ℕ) (hv : v ∈ g.inputs)
      (zero : st.getD v (Sum.inl false) = Sum.inl false)
      (h : (g.op = GateOp.and ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1)) :
      ∃ b : Bool, elimGate g.op (g.inputs.map fun i => st.getD i (Sum.inl false)) = Sum.inl (Sum.inl b) := by
    rcases h with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · obtain ⟨a, c, he⟩ : ∃ a c, g.inputs = [a,c] := by
        cases h : g.inputs with
        | nil => simp [h] at hlen
        | cons a rest =>
          cases rest with
          | nil => simp [h] at hlen
          | cons c tail =>
            obtain rfl : tail = [] := by simpa [h] using hlen
            exact ⟨a,c,rfl⟩
      rw [he] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [hop, he]
      rcases hv with rfl | rfl
      · rw [List.map_cons, zero]
        exact ⟨false, rfl⟩
      · rw [List.map_cons, List.map_cons, List.map_nil, zero]
        cases h : st.getD a (Sum.inl false) with
        | inl a => cases a <;> exact ⟨false,rfl⟩
        | inr a => exact ⟨false,rfl⟩
    · obtain ⟨i, he⟩ : ∃ i, g.inputs = [i] := by
        cases h : g.inputs with
        | nil => simp [h] at hlen
        | cons a rest =>
          obtain rfl : rest = [] := by simpa [h] using hlen
          exact ⟨a,rfl⟩
      rw [he, List.mem_singleton] at hv
      subst i
      rw [hop, he, List.map_cons, List.map_nil, zero]
      exact ⟨true,rfl⟩

  have compactTrace (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
      ∃ suffix : List (Bool ⊕ ℕ), (gs.foldl (elimStep n) acc).1 = acc.1 ++ suffix ∧
        suffix.length = gs.length := by
    induction gs generalizing acc with
    | nil => simp
    | cons g gs ih =>
      rcases acc with ⟨trace, gl⟩
      obtain ⟨suffix, htrace, hlen⟩ := ih (elimStep n (trace, gl) g)
      rw [List.foldl_cons, htrace]
      dsimp only [elimStep]
      cases elimGate g.op (g.inputs.map fun i => trace.getD i (Sum.inl false)) with
      | inl y => exact ⟨y :: suffix, by simp only [Sum.elim_inl, List.append_assoc, List.singleton_append], by simp [hlen]⟩
      | inr ng => exact ⟨Sum.inr (n+gl.length) :: suffix, by simp only [Sum.elim_inr, List.append_assoc, List.singleton_append], by simp [hlen]⟩

  have compactDropAfter (n : ℕ) (pre tail : List Gate) (g : Gate) (v : ℕ)
      (st : List (Bool ⊕ ℕ)) (seed : List Gate) (hv : v < st.length)
      (zero : st.getD v (Sum.inl false) = Sum.inl false) (read : v ∈ g.inputs)
      (absorb : (g.op = GateOp.and ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1))
      (hshape : ∀ g ∈ tail, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1)) :
      let res := (pre ++ g :: tail).foldl (elimStep n) (st, seed)
      (∃ b : Bool, res.1.getD (st.length + pre.length) (Sum.inl false) = Sum.inl b) ∧
      (∀ r ∈ tail, st.length + pre.length ∈ r.inputs →
        res.2.length + 2 ≤ seed.length + (pre ++ g :: tail).length) := by
    let stage := pre.foldl (elimStep n) (st, seed)
    obtain ⟨suf, hsuf, hlen⟩ := compactTrace n pre (st, seed)
    change stage.1 = st ++ suf at hsuf
    have stlen : stage.1.length = st.length + pre.length := by rw [hsuf, List.length_append, hlen]
    have zero' : stage.1.getD v (Sum.inl false) = Sum.inl false := by
      rwa [hsuf, List.getD_append _ _ _ _ hv]
    obtain ⟨b, hb⟩ := absorbing g stage.1 v read zero' absorb
    have force : elimStep n stage g = (stage.1 ++ [Sum.inl b], stage.2) := by
      dsimp only [elimStep]
      rw [hb]
      rfl
    have runEq : (pre ++ g :: tail).foldl (elimStep n) (st, seed) =
        tail.foldl (elimStep n) (stage.1 ++ [Sum.inl b], stage.2) := by
      rw [List.foldl_append, List.foldl_cons]
      change tail.foldl (elimStep n) (elimStep n stage g) = _
      rw [force]
    dsimp only
    rw [runEq]
    have prior : stage.1.length < (stage.1 ++ [Sum.inl b]).length := by simp
    have const : (stage.1 ++ [Sum.inl b]).getD stage.1.length (Sum.inl false) = Sum.inl b := getD_snoc_end _ _ _
    constructor
    · obtain ⟨more, hmore, _⟩ := compactTrace n tail (stage.1 ++ [Sum.inl b], stage.2)
      refine ⟨b, ?_⟩
      rw [← stlen]
      rw [hmore, List.getD_append _ _ _ _ prior, const]
    · intro r hr hread
      have used : 1 ≤ tail.countP (fun a => a.inputs.contains stage.1.length) :=
        List.countP_pos_iff.mpr ⟨r, hr, List.contains_iff_mem.mpr (stlen.symm ▸ hread)⟩
      have drop := elimRun_drop n tail hshape (stage.1 ++ [Sum.inl b]) stage.2 stage.1.length b prior const
      have preSize : stage.2.length ≤ seed.length + pre.length :=
        (compactLength n pre st seed).trans (Nat.add_le_add_left List.countP_le_length _)
      simp only [List.length_append, List.length_cons]
      omega


  let binaryCount (C : Circuit) : ℕ :=
    (C.gates.filter fun g => !isNot g).length

  have normalize (x1 : Circuit) (hFan1 : FanInTwo x1)
      (hOutHi1 : x1.output < 11 + x1.size)
      (hcomp : ∀ x : Fin 10 → Bool, x1.eval (List.ofFn x ++ [x 0 || x 2]) = p10 x) :
      ∃ D : Circuit, Strict 11 D ∧ 11 ≤ D.output ∧ D.output + 1 = 11 + D.size ∧
        notCount D ≤ notCount x1 ∧ binaryCount D ≤ binaryCount x1 ∧ D.size ≤ x1.gates.countP (fun g => !g.inputs.isEmpty) ∧
        ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = p10 x := by
    let st11 : List (Bool ⊕ ℕ) := (List.range 11).map Sum.inr
    have hst11_len : st11.length = 11 := by simp [st11]
    have hst11_bd : ∀ s ∈ st11, ∀ k, s = Sum.inr k → k < 11 + ([] : List Gate).length := by
      intro s hs k hk
      simp only [st11, List.mem_map, List.mem_range] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      cases hk; simpa using hi
    obtain ⟨⟨stT0, hst0, hsl0⟩, hstr_res0, hbd_res0, hn1_res0, hn2_res0, hsem_res0⟩ :=
      elimRun_spec 11 x1.gates hFan1 st11 [] (fun _ hj => by simp at hj) hst11_bd
    set res0 := x1.gates.foldl (elimStep 11) (st11, [])
    have hres0_len : res0.1.length = 11 + x1.size := by
      rw [hst0, List.length_append, hst11_len, hsl0]; rfl
    have hres0_eval (x : Fin 10 → Bool) :
        evalSym (res0.1.getD x1.output (Sum.inl false))
          (res0.2.foldl step (List.ofFn x ++ [x 0 || x 2])) = p10 x := by
      rw [← hcomp x]
      let w0 := List.ofFn x ++ [x 0 || x 2]
      have hw0_len : w0.length = 11 := by simp [w0]
      refine hsem_res0 w0 w0 hw0_len (hw0_len.trans hst11_len.symm) ?_ x1.output (by omega)
      intro i hi
      rw [hst11_len] at hi
      have hget : st11.getD i (Sum.inl false) = Sum.inr i := by
        rw [List.getD_eq_getElem _ _ (by rw [hst11_len]; exact hi)]
        simp [st11]
      rw [hget]
      rfl
    have hTargetSing : ∀ u : Fin 10, p10 (fun i => decide (i = u)) = false := by decide
    cases hsym0 : res0.1.getD x1.output (Sum.inl false) with
    | inl b =>
      have h1 := hres0_eval (fun _ => false)
      have h2 := hres0_eval (fun i => decide (i = 0 ∨ i = 1))
      rw [hsym0] at h1 h2
      have hne : p10 (fun _ => false) ≠ p10 (fun i => decide (i = 0 ∨ i = 1)) := by decide
      exact (hne (h1.symm.trans h2)).elim
    | inr k0 =>
      have hk0_mem : res0.1.getD x1.output (Sum.inl false) ∈ res0.1 := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
      have hk0_hi : k0 < 11 + res0.2.length := hbd_res0 _ hk0_mem k0 hsym0
      by_cases hk0_lo : k0 < 11
      · by_cases hk0_10 : k0 < 10
        · let u : Fin 10 := ⟨k0, hk0_10⟩
          have hev := hres0_eval (fun i => decide (i = u))
          rw [hsym0, hTargetSing u] at hev
          simp only [evalSym, Sum.elim_inr] at hev
          rw [wires_getD_lt res0.2 _ k0 (by rw [List.length_append, List.length_ofFn]; omega)] at hev
          rw [List.getD_append _ _ false k0 (by rw [List.length_ofFn]; exact hk0_10),
            List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk0_10)] at hev
          simp only [List.getElem_ofFn, decide_eq_false_iff_not] at hev
          exact (hev rfl).elim
        · have hk0_eq : k0 = 10 := by omega
          have hev := hres0_eval (fun i => decide (i = 0))
          rw [hsym0, hk0_eq, hTargetSing 0] at hev
          simp only [evalSym, Sum.elim_inr] at hev
          rw [wires_getD_lt res0.2 _ 10 (by simp)] at hev
          simp [List.getD_eq_getElem?_getD] at hev
      · obtain ⟨hDStrict, hDSize_le0, hDOut, hDNot0, hDNonNot0, hDEval0⟩ :=
          truncStrict 11 res0.2 k0 hstr_res0 (Nat.le_of_not_lt hk0_lo) hk0_hi
        set D : Circuit := ⟨res0.2.take (k0 - 11 + 1), k0⟩
        have hDEval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = p10 x := by
          intro x
          rw [hDEval0 _ (by simp)]
          have hev := hres0_eval x
          rw [hsym0] at hev
          exact hev
        have hDNot : notCount D ≤ notCount x1 := by
          have h1 : (res0.2.filter isNot).length ≤ notCount x1 := by
            change (res0.2.filter isNot).length ≤ (x1.gates.filter isNot).length; simpa using hn1_res0
          exact hDNot0.trans h1
        have hDNonNot : (D.gates.filter fun g => !isNot g).length ≤
            (x1.gates.filter fun g => !isNot g).length := by
          have h1 : (res0.2.filter fun g => !isNot g).length ≤
              (x1.gates.filter fun g => !isNot g).length := by simpa using hn2_res0
          exact hDNonNot0.trans h1
        have hPartD : D.size = notCount D + (D.gates.filter fun g => !isNot g).length :=
          filter_part D.gates
        have hPartX1 : x1.size = notCount x1 + (x1.gates.filter fun g => !isNot g).length :=
          filter_part x1.gates
        have hcompact := compactLength 11 x1.gates st11 []
        change res0.2.length ≤ 0 + _ at hcompact
        exact ⟨D, hDStrict, Nat.le_of_not_lt hk0_lo, hDOut, hDNot, hDNonNot, by omega, hDEval⟩

  have noReadAgree : ∀ (gs : List Gate) (v : ℕ) (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ g ∈ gs, v ∉ g.inputs) →
      (∀ i, i ≠ v → w1.getD i false = w2.getD i false) →
      ∀ i, i ≠ v → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
    intro gs v
    induction gs with
    | nil => intro w1 w2 _ _ hag i hi; exact hag i hi
    | cons g gs ih =>
      intro w1 w2 hwlen hno hag
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (step w1 g) (step w2 g) (by simp [step, hwlen])
        (fun a ha => hno a (List.mem_cons_of_mem g ha))
      intro i hi
      have hgv : v ∉ g.inputs := hno g (List.mem_cons_self ..)
      have hmap_eq : g.inputs.map (fun idx => w1.getD idx false) =
          g.inputs.map (fun idx => w2.getD idx false) := by
        apply List.map_congr_left
        intro idx hidx
        exact hag idx (fun heq => hgv (heq ▸ hidx))
      by_cases hilt : i < w1.length
      · simp only [step]
        rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w2.length)]
        exact hag i hi
      · by_cases hieq : i = w1.length
        · subst hieq
          simp only [step]
          rw [getD_snoc_end, hmap_eq, hwlen, getD_snoc_end]
        · simp only [step]
          rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]


  let Candidate (D : Circuit) : Prop :=
    Strict 11 D ∧ 11 ≤ D.output ∧ D.output + 1 = 11 + D.size ∧ notCount D ≤ 2 ∧ binaryCount D ≤ 17 ∧
      D.size ≤ 18 ∧ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = p10 x

  have strictShape {n : ℕ} {D : Circuit} (hDStrict : Strict n D) :
      ∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    rcases hDStrict j hj with ⟨hop, hlen2, _, _⟩ | ⟨hop, hlen1, _⟩
    · exact Or.inl ⟨hop, hlen2⟩
    · exact Or.inr ⟨hop, hlen1⟩

  have strictFan {n : ℕ} {D : Circuit} (strict : Strict n D) : FanInTwo D := by
    intro g hg
    rcases strictShape strict g hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · rcases hop with h | h <;> simp [h, hlen]
    · simp [hop, hlen]

  have readOthers (gs : List Gate) (v : ℕ) (w : List Bool) (b c : Bool)
      (hh : v = w.length) (unused : ∀ g ∈ gs, v ∉ g.inputs) (i : ℕ) (hi : i ≠ v) :
      (gs.foldl step (w ++ [b])).getD i false = (gs.foldl step (w ++ [c])).getD i false := by
    apply noReadAgree gs v _ _ (by simp) unused _ i hi
    intro j hj
    by_cases hj' : j < w.length
    · simp only [List.getD_append _ _ _ _ hj']
    · have he : w.length + 1 ≤ j := by omega
      rw [List.getD_eq_default _ _ (by simpa using he), List.getD_eq_default _ _ (by simpa using he)]

  have unusedReplace (D : Circuit) (strict : Strict 11 D)
      (j : ℕ) (hj : j < D.size) (ho : 11 + j ≠ D.output)
      (unused : ∀ g ∈ D.gates, 11 + j ∉ g.inputs) :
      ∃ E : Circuit, FanInTwo E ∧ E.output = D.output ∧ E.size = D.size ∧
        notCount E = notCount D ∧ binaryCount E = binaryCount D ∧
        E.gates.countP (fun g => !g.inputs.isEmpty) < E.size ∧
        ∀ x : Fin 10 → Bool, E.eval (List.ofFn x ++ [x 0 || x 2]) =
          D.eval (List.ofFn x ++ [x 0 || x 2]) := by
    let g : Gate := D.gates[j]
    let pre := D.gates.take j
    let tail := D.gates.drop (j + 1)
    let E : Circuit := ⟨pre ++ ⟨g.op, []⟩ :: tail, D.output⟩
    have preLen : pre.length = j := List.length_take_of_le (by exact Nat.le_of_lt hj)
    have split : D.gates = pre ++ g :: tail := by
      simpa only [pre, tail, g, ← List.drop_eq_getElem_cons hj] using (List.take_append_drop j D.gates).symm
    have gatesEq : E.gates = pre ++ ⟨g.op, []⟩ :: tail := rfl
    have hn : notCount E = notCount D := by
      change (E.gates.filter isNot).length = (D.gates.filter isNot).length
      rw [gatesEq, split]
      have same : isNot (⟨g.op, []⟩ : Gate) = isNot g := rfl
      cases h : isNot g <;> simp [same, h]
    have hb : binaryCount E = binaryCount D := by
      unfold binaryCount
      rw [gatesEq, split]
      have same : isNot (⟨g.op, []⟩ : Gate) = isNot g := rfl
      cases h : isNot g <;> simp [same, h]
    have sizeEq : E.size = D.size := by
      unfold Circuit.size
      rw [gatesEq, split]
      simp
    refine ⟨E, ?_, rfl, sizeEq, hn, hb, ?_, ?_⟩
    · intro a ha
      rw [gatesEq] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact strictFan strict a (split ▸ List.mem_append_left _ ha)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨(strictFan strict g (split ▸ List.mem_append_right _ (List.mem_cons_self ..))).1, by simp⟩
        · exact strictFan strict a (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha))
    · unfold Circuit.size
      rw [gatesEq]
      simp only [List.countP_append, List.countP_cons, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.length_append, List.length_cons]
      have h₁ := List.countP_le_length (p := fun g : Gate => !g.inputs.isEmpty) (l := pre)
      have h₂ := List.countP_le_length (p := fun g : Gate => !g.inputs.isEmpty) (l := tail)
      omega
    · intro x
      let w := List.ofFn x ++ [x 0 || x 2]
      let v := pre.foldl step w
      have hv : 11 + j = v.length := by rw [show v.length = w.length + pre.length from wires_len pre w, preLen]; simp [w]
      change ((E.gates.foldl step w).getD D.output false) = (D.gates.foldl step w).getD D.output false
      rw [gatesEq, split, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
      exact readOthers tail (11+j) v _ _ hv
        (fun a ha => unused a (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha)))
        D.output ho.symm

  have candidateNormalize {E : Circuit} (fan : FanInTwo E)
      (out : E.output < 11 + E.size) (nots : notCount E ≤ 2)
      (bins : binaryCount E ≤ 17) (size : E.size ≤ 18)
      (eval : ∀ x : Fin 10 → Bool, E.eval (List.ofFn x ++ [x 0 || x 2]) = p10 x) :
      ∃ D : Circuit, Candidate D ∧ D.size ≤ E.gates.countP (fun g => !g.inputs.isEmpty) := by
    obtain ⟨D, strict, outLo, final, hn, hb, hsz, computes⟩ := normalize E fan out eval
    refine ⟨D, ⟨strict, outLo, final, hn.trans nots, hb.trans bins, ?_, computes⟩, hsz⟩
    exact hsz.trans (List.countP_le_length.trans size)

  have candidateLive {D : Circuit} (hD : Candidate D)
      (least : ∀ E : Circuit, Candidate E → D.size ≤ E.size) (j : ℕ) (hj : j < D.size)
      (ho : 11 + j ≠ D.output) : ∃ g ∈ D.gates, 11 + j ∈ g.inputs := by
    by_contra! unused
    obtain ⟨strict, _, fin, hn, hb, hsz, comp⟩ := hD
    obtain ⟨E, fan, outEq, sizeEq, notEq, binEq, empty, eval⟩ := unusedReplace D strict j hj ho unused
    obtain ⟨F, cand, shorter⟩ := candidateNormalize fan (by omega) (by omega) (by omega) (by omega)
      (fun x => (eval x).trans (comp x))
    have := least F cand
    omega

  let PinLE (a b : List Bool) : Prop :=
    a.length = b.length ∧ ∀ i : ℕ, a.getD i false ≤ b.getD i false

  have leOr (a a' b b' : Bool) :
      a ≤ a' → b ≤ b' → (a || b) ≤ (a' || b') := by decide +revert

  have leAnd (a a' b b' : Bool) :
      a ≤ a' → b ≤ b' → (a && b) ≤ (a' && b') := by decide +revert

  have neg_le_except (a b : Bool) : ¬((!a) ≤ (!b)) → a = false ∧ b = true := by decide +revert

  have gateMono (s : List ℕ) (a b : List Bool) (h : PinLE a b) :
      GateOp.and.eval (s.map fun i => a.getD i false) ≤ GateOp.and.eval (s.map fun i => b.getD i false) ∧
      GateOp.or.eval (s.map fun i => a.getD i false) ≤ GateOp.or.eval (s.map fun i => b.getD i false) := by
    induction s with
    | nil => exact ⟨le_rfl, le_rfl⟩
    | cons i s ih =>
      exact ⟨leAnd _ _ _ _ (h.2 i) ih.1, leOr _ _ _ _ (h.2 i) ih.2⟩

  have extendLE {a b : List Bool} (h : PinLE a b) {v w : Bool} (hw : v ≤ w) :
      PinLE (a ++ [v]) (b ++ [w]) := by
    refine ⟨by simp [h.1], ?_⟩
    intro i
    by_cases ith : i < a.length
    · rw [List.getD_append _ _ _ _ ith, List.getD_append _ _ _ _ (by rw [← h.1]; exact ith)]
      exact h.2 i
    · by_cases j : i = a.length
      · rw [j, getD_snoc_end, h.1, getD_snoc_end]
        exact hw
      · have eq := h.1
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have noNotsMono (gs : List Gate)
      (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      {a b : List Bool} (h : PinLE a b) : PinLE (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun v hv => mono v (List.mem_cons_of_mem _ hv))
      apply extendLE h
      rcases mono g (List.mem_cons_self ..) with hop | hop
      · rw [hop]
        exact (gateMono g.inputs a b h).1
      · rw [hop]
        exact (gateMono g.inputs a b h).2

  let pins (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]

  have pinsLen (x : Fin 10 → Bool) : (pins x).length = 11 := by simp [pins]

  have pinsMono {x y : Fin 10 → Bool} (h : x ≤ y) : PinLE (pins x) (pins y) := by
    apply extendLE _ (leOr _ _ _ _ (h 0) (h 2))
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < 10
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
      simpa only [List.getElem_ofFn] using h ⟨i, hi⟩
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  let negateGate (i : ℕ) : Gate := ⟨GateOp.not, [i]⟩

  have opNot (g : Gate) (h : g.op = GateOp.not) (len : g.inputs.length = 1) :
      ∃ i, g = negateGate i := by
    obtain ⟨op, args⟩ := g
    cases args with
    | nil => simp at len
    | cons i tail =>
      have : tail = [] := by simpa using len
      subst tail
      exact ⟨i, by simp [negateGate, show op = GateOp.not from h]⟩

  have opMono {D : Circuit} (strict : Strict 11 D) {gs : List Gate}
      (sub : ∀ g ∈ gs, g ∈ D.gates) (none : (gs.filter isNot).length = 0) :
      ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases strictShape strict g (sub g hg) with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · have H := List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, (isNot_eq g).mpr h⟩)
      omega

  have negWire (i : ℕ) (w : List Bool) :
      step w (negateGate i) = w ++ [!(w.getD i false)] := rfl

  have resultNeg (gs : List Gate) (i : ℕ) (x : Fin 10 → Bool) :
      (Circuit.mk (gs ++ [negateGate i]) (11 + gs.length)).eval (pins x) =
        !((gs.foldl step (pins x)).getD i false) := by
    change ((gs ++ [negateGate i]).foldl step (pins x)).getD (11 + gs.length) false = _
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, negWire,
      ← pinsLen x, ← wires_len, getD_snoc_end]

  have negateCompare (a b : Bool) : (!a) = false → (!b) = true → ¬a ≤ b := by
    decide +revert

  have candidateLastBinary {D : Circuit} (hD : Candidate D)
      (least : ∀ E : Circuit, Candidate E → D.size ≤ E.size) :
      (gateAt D (D.size - 1)).op ≠ GateOp.not := by
    obtain ⟨strict, outLo, final, nots, bins, size, computes⟩ := hD
    let j := D.size - 1
    have hj : j < D.gates.length := by change j < D.size; dsimp [j]; omega
    have hout : D.output = 11 + j := by dsimp [j]; omega
    have hs : j + 1 = D.gates.length := by change j + 1 = D.size; dsimp [j]; omega
    intro hlast
    have hgate : D.gates[j].op = GateOp.not := by
      change (D.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not at hlast
      rwa [List.getD_eq_getElem _ _ hj] at hlast
    have hshape := strictShape strict _ (List.getElem_mem hj)
    have hlen : D.gates[j].inputs.length = 1 := by
      rcases hshape with ⟨hop, _⟩ | ⟨_, len⟩
      · simp [hgate] at hop
      · exact len
    obtain ⟨last, hneg⟩ := opNot D.gates[j] hgate hlen
    let before := D.gates.take j
    have lenBefore : before.length = j := List.length_take_of_le hj.le
    have split : D.gates = before ++ [negateGate last] := by
      rw [← hneg]
      simpa only [before, hs, List.take_length] using
        (List.take_succ_eq_append_getElem hj)
    have computes' (x : Fin 10 → Bool) :
        (!((before.foldl step (pins x)).getD last false)) = p10 x := by
      rw [← resultNeg, lenBefore, ← hout]
      simpa only [pins, ← split] using computes x
    have collapse {x y : Fin 10 → Bool} (hx : p10 x = false) (hy : p10 y = true) :
        ¬PinLE (before.foldl step (pins x)) (before.foldl step (pins y)) := by
      intro h
      exact negateCompare _ _ ((computes' x).trans hx) ((computes' y).trans hy) (h.2 last)
    have sumNots : (before.filter isNot).length ≤ 1 := by
      change (D.gates.filter isNot).length ≤ 2 at nots
      simp only [split, List.filter_append, List.length_append, show isNot (negateGate last) = true from rfl,
        List.filter_cons, List.filter_nil, ↓reduceIte, List.length_singleton] at nots
      omega
    have root0 : p10 (fun _ => false) = false := rfl
    have root1 : p10 (fun _ => true) = true := rfl
    have beforeSub (g : Gate) (hg : g ∈ before) : g ∈ D.gates := by
      rw [split]
      exact List.mem_append_left _ hg
    by_cases has : ∃ g ∈ before, g.op = GateOp.not
    · obtain ⟨g, hg, hgn⟩ := has
      obtain ⟨_, hlen⟩ := (strictShape strict g (beforeSub g hg)).resolve_left (by simp [hgn])
      obtain ⟨src, rfl⟩ := opNot g hgn hlen
      obtain ⟨pre, mid, hbefore, _⟩ := List.eq_append_cons_of_mem hg
      have noMore : (pre.filter isNot).length = 0 ∧ (mid.filter isNot).length = 0 := by
        simp only [hbefore, List.filter_append, List.filter_cons, show isNot (negateGate src) = true from rfl,
          ↓reduceIte, List.length_append, List.length_cons] at sumNots
        omega
      have preSub (v : Gate) (hv : v ∈ pre) : v ∈ D.gates :=
        beforeSub _ (by rw [hbefore]; exact List.mem_append_left _ hv)
      have midSub (v : Gate) (hv : v ∈ mid) : v ∈ D.gates :=
        beforeSub _ (by rw [hbefore]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hv))
      let preValue (x : Fin 10 → Bool) := (pre.foldl step (pins x)).getD src false
      have pair {x y : Fin 10 → Bool} (hxy : x ≤ y) (hx : p10 x = false) (hy : p10 y = true) :
          preValue x = false ∧ preValue y = true := by
        apply neg_le_except
        intro h
        apply collapse hx hy
        simp only [hbefore, List.foldl_append, List.foldl_cons, negWire]
        exact noNotsMono mid (opMono strict midSub noMore.2)
          (extendLE (noNotsMono pre (opMono strict preSub noMore.1) (pinsMono hxy)) h)
      have preComputes (x : Fin 10 → Bool) : preValue x = p10 x := by
        cases h : p10 x
        · exact (pair (x := x) (y := fun _ => true) (fun _ => Bool.le_true _) h root1).1
        · exact (pair (x := fun _ => false) (y := x) (fun _ => Bool.false_le _) root0 h).2
      have hpre : pre.length < D.gates.length := by
        rw [split, hbefore]
        simp
      have srcBd : src < 11 + pre.length := by
        have full : D.gates = pre ++ negateGate src :: (mid ++ [negateGate last]) := by
          rw [split, hbefore, List.append_assoc, List.cons_append]
        have gEq : D.gates[pre.length] = negateGate src := by
          have H : D.gates[pre.length]? = some (negateGate src) := by
            rw [full, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
            rfl
          exact Option.some.inj ((List.getElem?_eq_getElem hpre).symm.trans H)
        have H := strict pre.length hpre
        rw [gEq] at H
        rcases H with ⟨hop, _⟩ | ⟨_, _, reads⟩
        · simp [negateGate] at hop
        · exact reads src (by simp [negateGate])
      let E : Circuit := ⟨pre, src⟩
      have efan : FanInTwo E := fun v hv => strictFan strict v (preSub v hv)
      have esize : E.size < D.size := hpre
      have enot : notCount E = 0 := noMore.1
      have ebins : binaryCount E ≤ binaryCount D := by
        unfold binaryCount
        change (pre.filter _).length ≤ _
        rw [split, hbefore, List.append_assoc, List.filter_append, List.length_append]
        omega
      obtain ⟨F, hF, hfsize⟩ := candidateNormalize efan srcBd (by omega) (ebins.trans bins)
        (by omega) preComputes
      have H := least F hF
      have bound := hfsize.trans (List.countP_le_length (l := E.gates))
      change F.size ≤ E.size at bound
      omega
    · have zero : (before.filter isNot).length = 0 := by
        apply List.length_eq_zero_iff.mpr
        apply List.filter_eq_nil_iff.mpr
        intro g hg
        cases ht : isNot g
        · simp
        · exact (has ⟨g, hg, (isNot_eq g).mp ht⟩).elim
      exact collapse (x := fun _ => false) (y := fun _ => true)
        root0 root1 (noNotsMono before (opMono strict beforeSub zero)
          (pinsMono (fun _ => Bool.false_le true)))

  intro C hFan _ hSize _ hOutHi hNotLo hNotHi
  by_contra! computes
  have hBins : binaryCount C ≤ 17 := by
    have h := filter_part C.gates
    change C.size = notCount C + binaryCount C at h
    omega
  obtain ⟨E, hE, _⟩ := candidateNormalize hFan hOutHi hNotHi hBins hSize computes
  classical
  have existsSize : ∃ s : ℕ, ∃ D, D.size = s ∧ Candidate D := ⟨E.size, E, rfl, hE⟩
  obtain ⟨D, minimalSize, hD⟩ := Nat.find_spec existsSize
  have least (F : Circuit) (hF : Candidate F) : D.size ≤ F.size := by
    rw [minimalSize]
    exact Nat.find_min' existsSize ⟨F, rfl, hF⟩
  have live := candidateLive hD least
  have terminal := candidateLastBinary hD least
  obtain ⟨hDStrict, _, hDOut, hDNot, hDNonNot, hDSize, hDEval⟩ := hD
  have hDShape := strictShape hDStrict
  have hDFan := strictFan hDStrict
  have hPartD : D.size = notCount D + binaryCount D := filter_part D.gates
  let baseSet : Fin 10 → List ℕ := fun v =>
    ([[2, 5], [6], [0, 7], [4], [3], [7], [1], [5], [3], [4]] : List (List ℕ)).getD v.val []
  let xv (v : Fin 10) : Fin 10 → Bool := fun u => (baseSet v).contains u.val
  let yv (v : Fin 10) : Fin 10 → Bool := fun u => (u == v) || (baseSet v).contains u.val
  have hWitDiff : ∀ v : Fin 10,
      (∀ u : Fin 10, u ≠ v → xv v u = yv v u) ∧
      (xv v 0 || xv v 2) = (yv v 0 || yv v 2) ∧
      p10 (xv v) ≠ p10 (yv v) := by decide
  have hReadPos : ∀ v : Fin 10, 1 ≤ D.gates.countP (fun g => g.inputs.contains v.val) := by
    intro v
    by_contra hzero
    have hc0 : D.gates.countP (fun g => g.inputs.contains v.val) = 0 := by omega
    have hno_v : ∀ g ∈ D.gates, v.val ∉ g.inputs := by
      intro g hg hmem
      have hc_pos : 0 < D.gates.countP (fun g' => g'.inputs.contains v.val) :=
        List.countP_pos_iff.mpr ⟨g, hg, List.contains_iff_mem.mpr hmem⟩
      omega
    obtain ⟨hag_u, hag_10, hne_p10⟩ := hWitDiff v
    let w1 := List.ofFn (xv v) ++ [xv v 0 || xv v 2]
    let w2 := List.ofFn (yv v) ++ [yv v 0 || yv v 2]
    have heq_out : D.eval w1 = D.eval w2 := by
      apply noReadAgree D.gates v.val w1 w2 (by simp [w1, w2]) hno_v
      · intro i hi
        by_cases hi10 : i < 10
        · rw [List.getD_append _ _ _ _ (by simp [hi10]),
            List.getD_append _ _ _ _ (by simp [hi10]),
            List.getD_eq_getElem _ _ (by simp [hi10]),
            List.getD_eq_getElem _ _ (by simp [hi10])]
          simp only [List.getElem_ofFn]
          exact hag_u ⟨i, hi10⟩ (fun he => hi (congrArg Fin.val he))
        · by_cases hieq10 : i = 10
          · subst hieq10
            simp [w1, w2, List.getD_eq_getElem?_getD, hag_10]
          · rw [List.getD_eq_default _ _ (by simp [w1]; omega),
              List.getD_eq_default _ _ (by simp [w2]; omega)]
      · have hv10 := v.isLt; omega
    exact hne_p10 ((hDEval (xv v)).symm.trans (heq_out.trans (hDEval (yv v))))
  let invTbl : List (List ℕ) :=
    [[9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
     [4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
     [0, 4, 9, 7, 5, 1, 3, 6, 2, 8],
     [1, 0, 4, 9, 6, 2, 5, 3, 7, 8],
     [4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
     [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
     [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let invAt (v u : ℕ) : ℕ := (invTbl.getD v []).getD u 9
  have hInvLt : ∀ (v u : Fin 10), u ≠ v → invAt v.val u.val < 9 := by decide
  have hInv02Ne : ∀ v : Fin 10, v.val ≠ 0 → v.val ≠ 2 → invAt v.val 0 ≠ invAt v.val 2 := by decide
  have hP9Bool : ∀ (v : Fin 10) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool),
      p10 (fun u : Fin 10 => if u = v then false else
        [b0, b1, b2, b3, b4, b5, b6, b7, b8].getD (invAt v.val u.val) false) =
      p9 (fun i : Fin 9 => [b0, b1, b2, b3, b4, b5, b6, b7, b8].getD i.val false) := by decide
  have hList9Get (y : Fin 9 → Bool) (i : Fin 9) :
      [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8].getD i.val false = y i := by
    rcases i with ⟨iv, hi⟩
    interval_cases iv <;> rfl
  let extY (v : Fin 10) (y : Fin 9 → Bool) : Fin 10 → Bool :=
    fun u => if h : u = v then false else y ⟨invAt v.val u.val, hInvLt v u h⟩
  have hExtP9 (v : Fin 10) (y : Fin 9 → Bool) : p10 (extY v y) = p9 y := by
    have hb := hP9Bool v (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    have hlhs : (fun u : Fin 10 => if u = v then false else
        [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8].getD (invAt v.val u.val) false) = extY v y := by
      funext u
      dsimp only [extY]
      by_cases huv : u = v
      · simp [huv]
      · simp only [huv, ↓reduceIte, ↓reduceDIte]
        exact hList9Get y ⟨invAt v.val u.val, hInvLt v u huv⟩
    have hrhs : (fun i : Fin 9 =>
        [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8].getD i.val false) = y := by
      funext i
      exact hList9Get y i
    rw [hlhs, hrhs] at hb
    exact hb
  have hP9Sing : ∀ u : Fin 9, p9 (fun i => decide (i = u)) = false := by decide
  have absurd_p9 (ngs : List Gate) (sym : Bool ⊕ ℕ)
      (hstr : ∀ j (hj : j < ngs.length), StrictGate (9 + j) ngs[j])
      (hbd : ∀ k, sym = Sum.inr k → k < 9 + ngs.length)
      (hnot : (ngs.filter isNot).length ≤ 2)
      (hsem : ∀ y : Fin 9 → Bool, evalSym sym (ngs.foldl step (List.ofFn y)) = p9 y) :
      16 ≤ ngs.length := by
    by_contra hle15
    have hlen15 : ngs.length ≤ 15 := by omega
    cases hsym : sym with
    | inl b =>
      have h1 := hsem (fun _ => false)
      have h2 := hsem (fun i => decide (i = 0 ∨ i = 1))
      rw [hsym] at h1 h2
      have hne : p9 (fun _ => false) ≠ p9 (fun i => decide (i = 0 ∨ i = 1)) := by decide
      exact hne (h1.symm.trans h2)
    | inr k =>
      have hk_hi : k < 9 + ngs.length := hbd k hsym
      by_cases hk_lo : k < 9
      · let u : Fin 9 := ⟨k, hk_lo⟩
        have hev := hsem (fun i => decide (i = u))
        rw [hsym, hP9Sing u] at hev
        simp only [evalSym, Sum.elim_inr] at hev
        rw [wires_getD_lt ngs _ k (by rw [List.length_ofFn]; exact hk_lo),
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk_lo)] at hev
        simp only [List.getElem_ofFn, decide_eq_false_iff_not] at hev
        exact hev rfl
      · obtain ⟨hCStr, hCSize, hCOut, hCNot, _, hCEval⟩ :=
          truncStrict 9 ngs k hstr (Nat.le_of_not_lt hk_lo) hk_hi
        set C : Circuit := ⟨ngs.take (k - 9 + 1), k⟩
        obtain ⟨y, hy⟩ := h_p9 C hCStr (hCSize.trans hlen15) hCOut (hCNot.trans hnot)
        apply hy
        rw [hCEval _ (by simp)]
        have hev := hsem y
        rw [hsym] at hev
        exact hev
  have hDel02 (v : Fin 10) (hv02 : v.val = 0 ∨ v.val = 2) :
      ((D.gates.countP fun g => g.inputs.contains v.val) + 16 ≤ D.size) ∧
      (D.size = 17 → ∀ j (hj : j < D.gates.length), v.val ∈ D.gates[j].inputs →
        D.gates[j].op = GateOp.or) := by
    let st0 : List (Bool ⊕ ℕ) :=
      ((List.finRange 10).map fun u => if u = v then Sum.inl false else Sum.inr (invAt v.val u.val)) ++
        [Sum.inr 0]
    have hst0_len : st0.length = 11 := by simp [st0]
    have hst0_bd : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < 9 + ([] : List Gate).length := by
      intro s hs k hk
      simp only [st0, List.mem_append, List.mem_map, List.mem_finRange, true_and,
        List.mem_singleton] at hs
      rcases hs with ⟨u, hs⟩ | hs
      · by_cases huv : u = v
        · simp [huv] at hs; rw [← hs] at hk; cases hk
        · simp [huv] at hs; rw [← hs] at hk; cases hk
          simpa using hInvLt v u huv
      · rw [hs] at hk; cases hk; omega
    have hst0_v : st0.getD v.val (Sum.inl false) = Sum.inl false := by
      rw [List.getD_append _ _ _ _ (by simp [v.isLt]),
        List.getD_eq_getElem _ _ (by simp [v.isLt])]
      simp
    obtain ⟨⟨stT, hst, hsl⟩, hstr_r, hbd_r, hn1_r, _, hsem_r⟩ :=
      elimRun_spec 9 D.gates hDFan st0 [] (fun _ hj => by simp at hj) hst0_bd
    have hdrop := elimRun_drop 9 D.gates hDShape st0 [] v.val false (by rw [hst0_len]; have := v.isLt; omega) hst0_v
    set res := D.gates.foldl (elimStep 9) (st0, [])
    have hres_len : res.1.length = 11 + D.size := by
      rw [hst, List.length_append, hst0_len, hsl]; rfl
    have restricted (y : Fin 9 → Bool) :
        evalSym (res.1.getD D.output (Sum.inl false)) (res.2.foldl step (List.ofFn y)) = p9 y := by
      rw [← hExtP9 v y, ← hDEval (extY v y)]
      let w0 := List.ofFn (extY v y) ++ [extY v y 0 || extY v y 2]
      refine hsem_r (List.ofFn y) w0 (by simp) (by simp [w0, hst0_len]) ?_ D.output (by omega)
      intro i hi
      rw [hst0_len] at hi
      by_cases hi10 : i < 10
      · let u : Fin 10 := ⟨i, hi10⟩
        have hst_i : st0.getD i (Sum.inl false) =
            (if u = v then Sum.inl false else Sum.inr (invAt v.val u.val)) := by
          rw [List.getD_append _ _ _ _ (by simp [hi10]),
            List.getD_eq_getElem _ _ (by simp [hi10])]
          simp [u]
        have hw0_i : w0.getD i false = extY v y u := by
          rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi10),
            List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi10)]
          simp only [List.getElem_ofFn]; rfl
        rw [hst_i, hw0_i]
        dsimp only [extY]
        by_cases huv : u = v
        · simp [huv, evalSym]
        · simp only [huv, ↓reduceIte, ↓reduceDIte, evalSym, Sum.elim_inr, List.foldl_nil]
          have hlt9 := hInvLt v u huv
          rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt9)]
          simp only [List.getElem_ofFn]
      · have hieq10 : i = 10 := by omega
        subst hieq10
        have hst_10 : st0.getD 10 (Sum.inl false) = Sum.inr 0 := by
          simp [st0, List.getD_eq_getElem?_getD]
        have hw0_10 : w0.getD 10 false = (extY v y 0 || extY v y 2) := by
          have hs := getD_snoc_end (List.ofFn (extY v y)) (extY v y 0 || extY v y 2) false
          rw [List.length_ofFn] at hs
          exact hs
        rw [hst_10, hw0_10]
        simp only [evalSym, Sum.elim_inr, List.foldl_nil]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega)]
        simp only [List.getElem_ofFn]
        rcases hv02 with hv0 | hv2
        · have hv_eq : v = 0 := Fin.ext hv0
          subst hv_eq
          have hne20 : (2 : Fin 10) ≠ 0 := by decide
          dsimp only [extY]
          simp only [↓reduceDIte, hne20, Bool.false_or]
          rfl
        · have hv_eq : v = 2 := Fin.ext hv2
          subst hv_eq
          have hne02 : (0 : Fin 10) ≠ 2 := by decide
          dsimp only [extY]
          simp only [↓reduceDIte, hne02, Bool.or_false]
          rfl
    have h16 : 16 ≤ res.2.length := by
      refine absurd_p9 res.2 (res.1.getD D.output (Sum.inl false)) hstr_r ?_ ?_ restricted
      · intro k hk
        have hmem : res.1.getD D.output (Sum.inl false) ∈ res.1 := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
        exact hbd_r _ hmem k hk
      · have h1 : (res.2.filter isNot).length ≤ notCount D := by change (res.2.filter isNot).length ≤ (D.gates.filter isNot).length; simpa using hn1_r
        omega
    constructor
    · change res.2.length + _ ≤ 0 + D.size at hdrop
      omega
    · intro sz j hj reads
      by_contra hor
      let g : Gate := D.gates[j]
      let before := D.gates.take j
      let after := D.gates.drop (j+1)
      have split : D.gates = before ++ g :: after := by
        simpa only [before, after, g, ← List.drop_eq_getElem_cons hj] using
          (List.take_append_drop j D.gates).symm
      obtain ⟨fixed, shrinks⟩ := compactDropAfter 9 before after g v.val st0 []
        (by rw [hst0_len]; have := v.isLt; omega) hst0_v reads
        (by
          rcases hDShape g (List.getElem_mem hj) with ⟨hop, hlen⟩ | hnot
          · exact Or.inl ⟨hop.resolve_right hor, hlen⟩
          · exact Or.inr hnot)
        (fun a ha => hDShape a (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha)))
      have pos : st0.length + before.length = 11 + j := by
        rw [hst0_len, List.length_take_of_le hj.le]
      rw [← split, pos] at fixed shrinks
      by_cases last : 11 + j = D.output
      · obtain ⟨b, hb⟩ := fixed
        change res.1.getD (11 + j) (Sum.inl false) = Sum.inl b at hb
        rw [last] at hb
        have a := restricted (fun _ => false)
        have c := restricted (fun _ => true)
        rw [hb] at a c
        have af : b = false := a
        have ct : b = true := c
        cases af.symm.trans ct
      · obtain ⟨r, hr, hread⟩ := live j hj last
        have hr' : r ∈ after := by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
          have early : 11 + j < 11 + i := by
            rcases hDStrict i hi with ⟨_, _, _, readBack⟩ | ⟨_, _, readBack⟩ <;> exact readBack _ hread
          have index : i - (j+1) < after.length := by simp [after]; omega
          have item := List.getElem_drop (xs := D.gates) (i := j+1) (j := i-(j+1)) (h := index)
          have eq : j+1+(i-(j+1)) = i := by omega
          exact List.mem_iff_getElem.mpr ⟨i-(j+1), index, by simpa only [eq] using item⟩
        have H := shrinks r hr' hread
        change res.2.length + 2 ≤ 0 + D.size at H
        omega
  have hDelAll (v : Fin 10) :
      (D.gates.countP fun g => g.inputs.contains v.val) + 15 ≤ D.size := by
    by_cases hv02 : v.val = 0 ∨ v.val = 2
    · have := (hDel02 v hv02).1; omega
    · push Not at hv02
      obtain ⟨hv0, hv2⟩ := hv02
      let i0 := invAt v.val 0
      let i2 := invAt v.val 2
      have hi0_lt : i0 < 9 := hInvLt v 0 (fun h => hv0 (congrArg Fin.val h.symm))
      have hi2_lt : i2 < 9 := hInvLt v 2 (fun h => hv2 (congrArg Fin.val h.symm))
      have hi02_ne : i0 ≠ i2 := hInv02Ne v hv0 hv2
      let ngs0 : List Gate := [⟨GateOp.or, [i0, i2]⟩]
      let st0 : List (Bool ⊕ ℕ) :=
        ((List.finRange 10).map fun u => if u = v then Sum.inl false else Sum.inr (invAt v.val u.val)) ++
          [Sum.inr 9]
      have hst0_len : st0.length = 11 := by simp [st0]
      have hstr0 : ∀ j (hj : j < ngs0.length), StrictGate (9 + j) ngs0[j] := by
        intro j hj
        simp only [ngs0, List.length_singleton] at hj
        have hjeq : j = 0 := by omega
        subst hjeq
        dsimp only [ngs0, List.getElem_cons_zero]
        refine Or.inl ⟨Or.inr rfl, rfl, by simp [hi02_ne], ?_⟩
        intro idx hidx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hidx
        rcases hidx with rfl | rfl <;> omega
      have hst0_bd : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < 9 + ngs0.length := by
        intro s hs k hk
        simp only [st0, List.mem_append, List.mem_map, List.mem_finRange, true_and,
          List.mem_singleton] at hs
        rcases hs with ⟨u, hs⟩ | hs
        · by_cases huv : u = v
          · simp [huv] at hs; rw [← hs] at hk; cases hk
          · simp [huv] at hs; rw [← hs] at hk; cases hk
            have := hInvLt v u huv; simp [ngs0]; omega
        · rw [hs] at hk; cases hk; simp [ngs0]
      have hst0_v : st0.getD v.val (Sum.inl false) = Sum.inl false := by
        rw [List.getD_append _ _ _ _ (by simp [v.isLt]),
          List.getD_eq_getElem _ _ (by simp [v.isLt])]
        simp
      obtain ⟨⟨stT, hst, hsl⟩, hstr_r, hbd_r, hn1_r, _, hsem_r⟩ :=
        elimRun_spec 9 D.gates hDFan st0 ngs0 hstr0 hst0_bd
      have hdrop := elimRun_drop 9 D.gates hDShape st0 ngs0 v.val false
        (by rw [hst0_len]; have := v.isLt; omega) hst0_v
      set res := D.gates.foldl (elimStep 9) (st0, ngs0)
      have hres_len : res.1.length = 11 + D.size := by
        rw [hst, List.length_append, hst0_len, hsl]; rfl
      have hngs0_not : (ngs0.filter isNot).length = 0 := rfl
      have h16 : 16 ≤ res.2.length := by
        refine absurd_p9 res.2 (res.1.getD D.output (Sum.inl false)) hstr_r ?_ ?_ ?_
        · intro k hk
          have hmem : res.1.getD D.output (Sum.inl false) ∈ res.1 := by
            rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
          exact hbd_r _ hmem k hk
        · rw [hngs0_not, zero_add] at hn1_r
          have h1 : (res.2.filter isNot).length ≤ notCount D := by change (res.2.filter isNot).length ≤ (D.gates.filter isNot).length; simpa using hn1_r
          omega
        · intro y
          rw [← hExtP9 v y, ← hDEval (extY v y)]
          let w0 := List.ofFn (extY v y) ++ [extY v y 0 || extY v y 2]
          refine hsem_r (List.ofFn y) w0 (by simp) (by simp [w0, hst0_len]) ?_ D.output (by omega)
          intro i hi
          rw [hst0_len] at hi
          by_cases hi10 : i < 10
          · let u : Fin 10 := ⟨i, hi10⟩
            have hst_i : st0.getD i (Sum.inl false) =
                (if u = v then Sum.inl false else Sum.inr (invAt v.val u.val)) := by
              rw [List.getD_append _ _ _ _ (by simp [hi10]),
                List.getD_eq_getElem _ _ (by simp [hi10])]
              simp [u]
            have hw0_i : w0.getD i false = extY v y u := by
              rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi10),
                List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi10)]
              simp only [List.getElem_ofFn]; rfl
            rw [hst_i, hw0_i]
            dsimp only [extY]
            by_cases huv : u = v
            · simp [huv, evalSym]
            · simp only [huv, ↓reduceIte, ↓reduceDIte, evalSym, Sum.elim_inr]
              have hlt9 := hInvLt v u huv
              rw [wires_getD_lt ngs0 _ _ (by rw [List.length_ofFn]; exact hlt9),
                List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt9)]
              simp only [List.getElem_ofFn]
          · have hieq10 : i = 10 := by omega
            subst hieq10
            have hst_10 : st0.getD 10 (Sum.inl false) = Sum.inr 9 := by
              simp [st0, List.getD_eq_getElem?_getD]
            have hw0_10 : w0.getD 10 false = (extY v y 0 || extY v y 2) := by
              have hs := getD_snoc_end (List.ofFn (extY v y)) (extY v y 0 || extY v y 2) false
              rw [List.length_ofFn] at hs
              exact hs
            rw [hst_10, hw0_10]
            simp only [evalSym, Sum.elim_inr, ngs0, List.foldl_cons, List.foldl_nil, step]
            have hs9 := getD_snoc_end (List.ofFn y)
              (GateOp.or.eval (List.map (fun idx => (List.ofFn y).getD idx false) [i0, i2])) false
            rw [List.length_ofFn] at hs9
            rw [hs9]
            simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq]
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi0_lt),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi2_lt)]
            simp only [List.getElem_ofFn]
            have hne0v : (0 : Fin 10) ≠ v := fun h => hv0 (congrArg Fin.val h).symm
            have hne2v : (2 : Fin 10) ≠ v := fun h => hv2 (congrArg Fin.val h).symm
            dsimp only [extY]
            simp only [hne0v, hne2v, ↓reduceDIte]
            rfl
      change res.2.length + _ ≤ 1 + D.size at hdrop
      omega
  have hr0_16 : (D.gates.countP fun g => g.inputs.contains 0) + 16 ≤ D.size := (hDel02 0 (Or.inl rfl)).1
  have hr2_16 : (D.gates.countP fun g => g.inputs.contains 2) + 16 ≤ D.size := (hDel02 2 (Or.inr rfl)).1
  have hr0_pos : 1 ≤ (D.gates.countP fun g => g.inputs.contains 0) := hReadPos 0
  have hr2_pos : 1 ≤ (D.gates.countP fun g => g.inputs.contains 2) := hReadPos 2
  have hDSize17 : 17 ≤ D.size := by omega
  have ends (sz : D.size = 17) (g : Gate) (hg : g ∈ D.gates)
      (r : 0 ∈ g.inputs ∨ 2 ∈ g.inputs) : g.op = GateOp.or := by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    rcases r with r | r
    · exact (hDel02 0 (Or.inl rfl)).2 sz j hj r
    · exact (hDel02 2 (Or.inr rfl)).2 sz j hj r
  by_cases hnot0 : notCount D = 0
  · have hDSizeEq : D.size = 17 := by omega
    have hDOutEq : D.output = 27 := by omega
    have hDMono : IsMonotoneCircuit D := by
      intro g hg
      rcases hDShape g hg with ⟨hop, _⟩ | ⟨hop, _⟩
      · exact hop
      · exfalso
        have hmem : g ∈ D.gates.filter isNot := List.mem_filter.mpr ⟨hg, (isNot_eq g).mpr hop⟩
        have hpos : 0 < notCount D := List.length_pos_of_mem hmem
        omega
    obtain ⟨x, hx⟩ := h_not0 D hDStrict hDMono hDSizeEq hDOutEq hnot0 live (ends hDSizeEq)
      (by omega) (by omega) (fun v => ⟨hReadPos v, by have := hDelAll v; omega⟩)
    exact hx (hDEval x)
  · by_cases hnot1 : notCount D = 1
    · obtain ⟨x, hx⟩ := h_not1 D hDStrict hDSize17 hDSize hDOut hnot1 live ends terminal
        hr0_16 hr2_16 (fun v => ⟨hReadPos v, hDelAll v⟩)
      exact hx (hDEval x)
    · have hnot2 : notCount D = 2 := by omega
      obtain ⟨x, hx⟩ := h_not2 D hDStrict hDSize17 hDSize hDOut hnot2 live ends terminal
        hr0_16 hr2_16 (fun v => ⟨hReadPos v, hDelAll v⟩)
      exact hx (hDEval x)
