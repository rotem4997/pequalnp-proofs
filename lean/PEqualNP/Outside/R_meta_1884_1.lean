import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1884_1
    (h_p10_18 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10
      (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (h_pv_15 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (h_only10 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      (∀ j : Fin D.gates.length,
        ((D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.head? ≠ some 0) ∧
        ((D.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 0 ∉ (D.gates.get j).inputs)) →
      ¬ ∃ j1 j2 : Fin D.gates.length, ∀ j : Fin D.gates.length,
        ((D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.head? = some 10 → j = j1 ∨ j = j2) ∧
        ((D.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 10 ∈ (D.gates.get j).inputs → j = j1 ∨ j = j2))
    (h_both010 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size = 18 →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      ¬ ∃ j0 j1 : Fin D.gates.length, j0 ≠ j1 ∧
        (D.gates.get j0).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 ∈ (D.gates.get j0).inputs ∧
        (D.gates.get j1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 10 ∈ (D.gates.get j1).inputs ∧
        ∀ p ∈ ([(0, j0), (10, j1)] : List (ℕ × Fin D.gates.length)), ∀ j : Fin D.gates.length,
          ((D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (D.gates.get j).inputs.head? = some p.1 → j = p.2) ∧
          ((D.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → p.1 ∈ (D.gates.get j).inputs → j = p.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  let p10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let pv : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_and (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
  have eval_not (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := rfl
  let active (g : PEqualNP.CircuitLowerBounds.Gate) : List ℕ :=
    PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
  have active_of_ne_not (g : PEqualNP.CircuitLowerBounds.Gate) (h : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) :
      active g = g.inputs := by
    cases hop : g.op with
    | and => dsimp only [active]; rw [hop]
    | or => dsimp only [active]; rw [hop]
    | not => exact False.elim (h hop)
    | mod _ => dsimp only [active]; rw [hop]
    | maj => dsimp only [active]; rw [hop]
  have active_of_not (g : PEqualNP.CircuitLowerBounds.Gate) (h : g.op = PEqualNP.CircuitLowerBounds.GateOp.not) :
      active g = g.inputs.take 1 := by
    dsimp only [active]; rw [h]
  let evalSym (s : Bool ⊕ ℕ) (w : List Bool) : Bool :=
    Sum.elim id (fun k => w.getD k false) s
  let elimNot (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ PEqualNP.CircuitLowerBounds.Gate :=
    List.casesOn vs (Sum.inl (Sum.inl true)) (fun v _ =>
      Sum.elim (fun b => Sum.inl (Sum.inl (!b))) (fun k => Sum.inr ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [k]⟩) v)
  let elimAnd (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ PEqualNP.CircuitLowerBounds.Gate :=
    List.casesOn vs (Sum.inl (Sum.inl true)) (fun v1 t1 =>
      List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
        List.casesOn t2
          (Sum.elim
            (fun b1 => Bool.casesOn b1 (Sum.inl (Sum.inl false)) (Sum.inl v2))
            (fun k1 => Sum.elim
              (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inl false)) (Sum.inl (Sum.inr k1)))
              (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [k1, k2]⟩)
              v2)
            v1)
          (fun _ _ => Sum.inl (Sum.inl false))))
  let elimOr (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ PEqualNP.CircuitLowerBounds.Gate :=
    List.casesOn vs (Sum.inl (Sum.inl false)) (fun v1 t1 =>
      List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
        List.casesOn t2
          (Sum.elim
            (fun b1 => Bool.casesOn b1 (Sum.inl v2) (Sum.inl (Sum.inl true)))
            (fun k1 => Sum.elim
              (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inr k1)) (Sum.inl (Sum.inl true)))
              (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [k1, k2]⟩)
              v2)
            v1)
          (fun _ _ => Sum.inl (Sum.inl false))))
  let elimGate (op : PEqualNP.CircuitLowerBounds.GateOp) (vs : List (Bool ⊕ ℕ)) :
      (Bool ⊕ ℕ) ⊕ PEqualNP.CircuitLowerBounds.Gate :=
    PEqualNP.CircuitLowerBounds.GateOp.casesOn op
      (elimAnd vs) (elimOr vs) (elimNot vs) (fun _ => Sum.inl (Sum.inl false)) (Sum.inl (Sum.inl false))
  let elimStep (n' : ℕ)
      (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool)
      (g : PEqualNP.CircuitLowerBounds.Gate) :
      List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate × List Bool :=
    let st := acc.1
    let ngs := acc.2.1
    let fl := acc.2.2
    let vs := g.inputs.map fun i => st.getD i (Sum.inl false)
    Sum.elim
      (fun sym => (st ++ [sym], ngs, fl ++ [true]))
      (fun ng => (st ++ [Sum.inr (n' + ngs.length)], ngs ++ [ng], fl ++ [false]))
      (elimGate g.op vs)
  have wires_start (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      rw [List.foldl_cons]
      obtain ⟨t, ht, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hlen]⟩
      rw [ht]; simp [step]
  have wires_len (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    obtain ⟨t, ht, hlen⟩ := wires_start gs w
    rw [ht, List.length_append, hlen]
  have wires_getD_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wires_start gs w
    rw [ht, List.getD_append _ _ _ _ hi]
  have getD_snoc_end {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    simp [List.getD_eq_getElem?_getD]
  have eval_active_congr (g : PEqualNP.CircuitLowerBounds.Gate)
      (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
      (w1 w2 : List Bool)
      (h : ∀ i ∈ active g, w1.getD i false = w2.getD i false) :
      g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h1 | h1 | h1
    · rw [h1]; congr 1; apply List.map_congr_left
      intro i hi; exact h i (by rw [active_of_ne_not g (by rw [h1]; intro h'; cases h')]; exact hi)
    · rw [h1]; congr 1; apply List.map_congr_left
      intro i hi; exact h i (by rw [active_of_ne_not g (by rw [h1]; intro h'; cases h')]; exact hi)
    · rw [h1]
      cases hin : g.inputs with
      | nil => rfl
      | cons a rest =>
        simp only [List.map_cons, eval_not, List.headD_cons]
        have ha : a ∈ active g := by rw [active_of_not g h1, hin]; simp
        rw [h a ha]
  have elimGate_ok (op : PEqualNP.CircuitLowerBounds.GateOp)
      (hop : op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
      (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (w : List Bool) :
      (∀ sym, elimGate op vs = Sum.inl sym →
        evalSym sym w = op.eval (vs.map fun s => evalSym s w) ∧
        (∀ k, sym = Sum.inr k → Sum.inr k ∈ vs)) ∧
      (∀ ng, elimGate op vs = Sum.inr ng →
        ng.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        ng.inputs.length ≤ 2 ∧
        ng.op.eval (ng.inputs.map fun i => w.getD i false) = op.eval (vs.map fun s => evalSym s w)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases vs with
      | nil =>
        exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          exact ⟨fun sym hs => by cases hs; exact ⟨by simp [eval_and], fun k hk => by subst hk; exact List.mem_singleton_self _⟩, fun ng hng => by cases hng⟩
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => simp at hlen
          | nil =>
            cases v1 with
            | inl b1 =>
              cases v2 with
              | inl b2 =>
                cases b1 <;> cases b2 <;>
                  exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
              | inr k2 =>
                cases b1 with
                | false =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_and], fun k hk => by cases hk; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩, fun ng hng => by cases hng⟩
            | inr k1 =>
              cases v2 with
              | inl b2 =>
                cases b2 with
                | false =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_and], fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_and], fun k hk => by cases hk; exact List.mem_cons_self ..⟩, fun ng hng => by cases hng⟩
              | inr k2 =>
                by_cases hk : k1 = k2
                · subst hk
                  refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimAnd, Sum.elim_inr, ↓reduceIte] at hs; cases hs
                    exact ⟨by simp [evalSym, eval_and], fun k hk' => by cases hk'; exact List.mem_cons_self ..⟩
                  · simp only [elimGate, elimAnd, Sum.elim_inr, ↓reduceIte] at hng; cases hng
                · refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimAnd, Sum.elim_inr, hk, ↓reduceIte] at hs; cases hs
                  · simp only [elimGate, elimAnd, Sum.elim_inr, hk, ↓reduceIte] at hng; cases hng
                    exact ⟨Set.mem_insert _ _, le_refl 2, by simp [evalSym, eval_and]⟩
    · cases vs with
      | nil =>
        exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          exact ⟨fun sym hs => by cases hs; exact ⟨by simp [eval_or], fun k hk => by subst hk; exact List.mem_singleton_self _⟩, fun ng hng => by cases hng⟩
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => simp at hlen
          | nil =>
            cases v1 with
            | inl b1 =>
              cases v2 with
              | inl b2 =>
                cases b1 <;> cases b2 <;>
                  exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
              | inr k2 =>
                cases b1 with
                | false =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_or], fun k hk => by cases hk; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩, fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
            | inr k1 =>
              cases v2 with
              | inl b2 =>
                cases b2 with
                | false =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_or], fun k hk => by cases hk; exact List.mem_cons_self ..⟩, fun ng hng => by cases hng⟩
                | true =>
                  exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_or], fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
              | inr k2 =>
                by_cases hk : k1 = k2
                · subst hk
                  refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimOr, Sum.elim_inr, ↓reduceIte] at hs; cases hs
                    exact ⟨by simp [evalSym, eval_or], fun k hk' => by cases hk'; exact List.mem_cons_self ..⟩
                  · simp only [elimGate, elimOr, Sum.elim_inr, ↓reduceIte] at hng; cases hng
                · refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                  · simp only [elimGate, elimOr, Sum.elim_inr, hk, ↓reduceIte] at hs; cases hs
                  · simp only [elimGate, elimOr, Sum.elim_inr, hk, ↓reduceIte] at hng; cases hng
                    exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), le_refl 2, by simp [evalSym, eval_or]⟩
    · cases vs with
      | nil =>
        exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
      | cons v1 t1 =>
        cases v1 with
        | inl b1 =>
          exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
        | inr k1 =>
          exact ⟨(fun sym hs => by cases hs), (fun ng hng => by cases hng; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), Nat.le_succ 1, rfl⟩)⟩
  have elimGate_of_const (op : PEqualNP.CircuitLowerBounds.GateOp)
      (hop : op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
      (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (c : Bool)
      (hnot_in : op = PEqualNP.CircuitLowerBounds.GateOp.not → vs.head? = some (Sum.inl c))
      (hbin_in : op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → Sum.inl c ∈ vs) :
      ∃ sym, elimGate op vs = Sum.inl sym ∧
        (op = PEqualNP.CircuitLowerBounds.GateOp.not → sym = Sum.inl (!c)) ∧
        (op = PEqualNP.CircuitLowerBounds.GateOp.and → c = false → sym = Sum.inl false) ∧
        (op = PEqualNP.CircuitLowerBounds.GateOp.or → c = true → sym = Sum.inl true) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hmem := hbin_in (by intro h; cases h)
      cases vs with
      | nil => cases hmem
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          simp only [List.mem_singleton] at hmem; subst hmem
          exact ⟨Sum.inl c, rfl, (fun h => by cases h), (fun _ hc => by subst hc; rfl), (fun h _ => by cases h)⟩
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => simp at hlen
          | nil =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl
            · cases v2 with
              | inl b2 => cases c <;> cases b2 <;> exact ⟨_, rfl, (fun h => by cases h), (fun _ hc => by cases hc <;> rfl), (fun h _ => by cases h)⟩
              | inr k2 => cases c <;> exact ⟨_, rfl, (fun h => by cases h), (fun _ hc => by cases hc <;> rfl), (fun h _ => by cases h)⟩
            · cases v1 with
              | inl b1 => cases c <;> cases b1 <;> exact ⟨_, rfl, (fun h => by cases h), (fun _ hc => by cases hc <;> rfl), (fun h _ => by cases h)⟩
              | inr k1 => cases c <;> exact ⟨_, rfl, (fun h => by cases h), (fun _ hc => by cases hc <;> rfl), (fun h _ => by cases h)⟩
    · have hmem := hbin_in (by intro h; cases h)
      cases vs with
      | nil => cases hmem
      | cons v1 t1 =>
        cases t1 with
        | nil =>
          simp only [List.mem_singleton] at hmem; subst hmem
          exact ⟨Sum.inl c, rfl, (fun h => by cases h), (fun h _ => by cases h), (fun _ hc => by subst hc; rfl)⟩
        | cons v2 t2 =>
          cases t2 with
          | cons _ _ => simp at hlen
          | nil =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl
            · cases v2 with
              | inl b2 => cases c <;> cases b2 <;> exact ⟨_, rfl, (fun h => by cases h), (fun h _ => by cases h), (fun _ hc => by cases hc <;> rfl)⟩
              | inr k2 => cases c <;> exact ⟨_, rfl, (fun h => by cases h), (fun h _ => by cases h), (fun _ hc => by cases hc <;> rfl)⟩
            · cases v1 with
              | inl b1 => cases c <;> cases b1 <;> exact ⟨_, rfl, (fun h => by cases h), (fun h _ => by cases h), (fun _ hc => by cases hc <;> rfl)⟩
              | inr k1 => cases c <;> exact ⟨_, rfl, (fun h => by cases h), (fun h _ => by cases h), (fun _ hc => by cases hc <;> rfl)⟩
    · have hhd := hnot_in rfl
      cases vs with
      | nil => cases hhd
      | cons v1 t1 =>
        simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd
        exact ⟨Sum.inl (!c), rfl, (fun _ => rfl), (fun h _ => by cases h), (fun h _ => by cases h)⟩
  have elimGate_two_const (op : PEqualNP.CircuitLowerBounds.GateOp)
      (hop : op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
      (c1 c2 : Bool) :
      ∃ c' : Bool, elimGate op [Sum.inl c1, Sum.inl c2] = Sum.inl (Sum.inl c') := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl <;> cases c1 <;> cases c2 <;> exact ⟨_, rfl⟩
  have elimRun_inv (n' : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (st0 : List (Bool ⊕ ℕ)) (ngs0 : List PEqualNP.CircuitLowerBounds.Gate) (fl0 : List Bool)
      (hfan0 : ∀ g ∈ ngs0, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (hbd0 : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n' + ngs0.length) :
      let res := gs.foldl (elimStep n') (st0, ngs0, fl0)
      (∃ stT ngsT flT, res.1 = st0 ++ stT ∧ res.2.1 = ngs0 ++ ngsT ∧ res.2.2 = fl0 ++ flT ∧
        stT.length = gs.length ∧ flT.length = gs.length) ∧
      res.2.1.length + res.2.2.count true = ngs0.length + fl0.count true + gs.length ∧
      (∀ g ∈ res.2.1, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ s ∈ res.1, ∀ k, s = Sum.inr k → k < n' + res.2.1.length) ∧
      (∀ (wIn w0 : List Bool), wIn.length = n' → w0.length = st0.length →
        (∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD i false) →
        ∀ i < res.1.length, evalSym (res.1.getD i (Sum.inl false)) (res.2.1.foldl step wIn) = (gs.foldl step w0).getD i false) := by
    induction gs generalizing st0 ngs0 fl0 with
    | nil =>
      refine ⟨⟨[], [], [], by simp, by simp, by simp, rfl, rfl⟩, by simp, hfan0, hbd0, ?_⟩
      intro wIn w0 _ _ hagree i hi
      exact hagree i hi
    | cons g gs ih =>
      have hg := hfan g (List.mem_cons_self ..)
      have hgs : ∀ a ∈ gs, a.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ a.inputs.length ≤ 2 :=
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
      cases heg : elimGate g.op vs with
      | inl sym =>
        have hstep : elimStep n' (st0, ngs0, fl0) g = (st0 ++ [sym], ngs0, fl0 ++ [true]) := by
          dsimp only [elimStep]
          change Sum.elim
            (fun s => (st0 ++ [s], ngs0, fl0 ++ [true]))
            (fun ng => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng], fl0 ++ [false]))
            (elimGate g.op vs) = _
          rw [heg]; rfl
        have hbd1 : ∀ s ∈ st0 ++ [sym], ∀ k, s = Sum.inr k → k < n' + ngs0.length := by
          intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h1
          · exact hbd0 s h1 k hk
          · simp only [List.mem_singleton] at h1; rw [h1] at hk
            have hmem := (elimGate_ok g.op hg.1 vs hvs_len []).1 sym heg |>.2 k hk
            exact hvs_bd (Sum.inr k) hmem k rfl
        have hrec := ih hgs (st0 ++ [sym]) ngs0 (fl0 ++ [true]) hfan0 hbd1
        rw [List.foldl_cons, hstep]
        obtain ⟨⟨stT, ngsT, flT, hst, hngs, hfl, hsl, hfl_len⟩, hcnt, hfan', hbd', hsem⟩ := hrec
        refine ⟨⟨sym :: stT, ngsT, true :: flT, ?_, hngs, ?_, by simp [hsl], by simp [hfl_len]⟩, ?_, hfan', hbd', ?_⟩
        · rw [hst]; simp
        · rw [hfl]; simp
        · simp only [List.count_append, List.count_cons, beq_self_eq_true, ↓reduceIte, List.count_nil,
            List.length_cons] at hcnt ⊢
          omega
        · intro wIn w0 hwIn hw0 hagree
          rw [List.foldl_cons]
          apply hsem wIn (step w0 g) hwIn (by simp [step, hw0])
          intro i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          by_cases hilt : i < st0.length
          · rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w0.length)]
            exact hagree i hilt
          · have hieq : i = st0.length := by omega
            subst hieq
            rw [getD_snoc_end]
            have hval := (elimGate_ok g.op hg.1 vs hvs_len (ngs0.foldl step wIn)).1 sym heg |>.1
            rw [hval]
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
        have hstep : elimStep n' (st0, ngs0, fl0) g =
            (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng], fl0 ++ [false]) := by
          dsimp only [elimStep]
          change Sum.elim
            (fun s => (st0 ++ [s], ngs0, fl0 ++ [true]))
            (fun ng' => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng'], fl0 ++ [false]))
            (elimGate g.op vs) = _
          rw [heg]; rfl
        have hng_ok := (elimGate_ok g.op hg.1 vs hvs_len []).2 ng heg
        have hfan1 : ∀ a ∈ ngs0 ++ [ng], a.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ a.inputs.length ≤ 2 := by
          intro a ha
          rcases List.mem_append.mp ha with h1 | h1
          · exact hfan0 a h1
          · simp only [List.mem_singleton] at h1; rw [h1]; exact ⟨hng_ok.1, hng_ok.2.1⟩
        have hbd1 : ∀ s ∈ st0 ++ [Sum.inr (n' + ngs0.length)], ∀ k, s = Sum.inr k → k < n' + (ngs0 ++ [ng]).length := by
          intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h1
          · have := hbd0 s h1 k hk; simp; omega
          · simp only [List.mem_singleton] at h1; rw [h1] at hk; cases hk; simp
        have hrec := ih hgs (st0 ++ [Sum.inr (n' + ngs0.length)]) (ngs0 ++ [ng]) (fl0 ++ [false]) hfan1 hbd1
        rw [List.foldl_cons, hstep]
        obtain ⟨⟨stT, ngsT, flT, hst, hngs, hfl, hsl, hfl_len⟩, hcnt, hfan', hbd', hsem⟩ := hrec
        refine ⟨⟨Sum.inr (n' + ngs0.length) :: stT, ng :: ngsT, false :: flT, ?_, ?_, ?_, by simp [hsl], by simp [hfl_len]⟩, ?_, hfan', hbd', ?_⟩
        · rw [hst]; simp
        · rw [hngs]; simp
        · rw [hfl]; simp
        · have hcf : [false].count true = 0 := rfl
          simp only [List.length_append, List.length_cons, List.length_nil, List.count_append, hcf] at hcnt ⊢
          omega
        · intro wIn w0 hwIn hw0 hagree
          rw [List.foldl_cons]
          apply hsem wIn (step w0 g) hwIn (by simp [step, hw0])
          intro i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          have hfold : (ngs0 ++ [ng]).foldl step wIn = step (ngs0.foldl step wIn) ng := by
            rw [List.foldl_append]; rfl
          rw [hfold]
          by_cases hilt : i < st0.length
          · rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w0.length)]
            have hprev := hagree i hilt
            have hmem : st0.getD i (Sum.inl false) ∈ st0 := by
              rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_mem hilt
            cases hs : st0.getD i (Sum.inl false) with
            | inl b => rw [hs] at hprev; exact hprev
            | inr k =>
              have hk : k < (ngs0.foldl step wIn).length := by
                rw [wires_len, hwIn]; exact hbd0 _ hmem k hs
              simp only [evalSym, Sum.elim_inr, step]
              rw [List.getD_append _ _ _ _ hk]
              rw [hs] at hprev; exact hprev
          · have hieq : i = st0.length := by omega
            subst hieq
            rw [getD_snoc_end]
            simp only [evalSym, Sum.elim_inr, step]
            have hlen_w : (ngs0.foldl step wIn).length = n' + ngs0.length := by
              rw [wires_len, hwIn]
            rw [← hlen_w, getD_snoc_end]
            have hval := (elimGate_ok g.op hg.1 vs hvs_len (ngs0.foldl step wIn)).2 ng heg |>.2.2
            rw [hval, ← hw0, getD_snoc_end]
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
  have elimRun_at_gate (n' : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (st0 : List (Bool ⊕ ℕ))
      (hbd0 : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n')
      (j : ℕ) (hj : j < gs.length) :
      let res := gs.foldl (elimStep n') (st0, [], [])
      let pre := (gs.take j).foldl (elimStep n') (st0, [], [])
      let vs := (gs[j]).inputs.map fun i => pre.1.getD i (Sum.inl false)
      pre.1.length = st0.length + j ∧
      (∀ i < st0.length + j, res.1.getD i (Sum.inl false) = pre.1.getD i (Sum.inl false)) ∧
      (∀ sym, elimGate (gs[j]).op vs = Sum.inl sym →
        res.1.getD (st0.length + j) (Sum.inl false) = sym ∧ res.2.2.getD j false = true) := by
    have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
      have h1 := (List.take_append_drop j gs).symm
      rw [List.drop_eq_getElem_cons hj] at h1; exact h1
    have hfan_take : ∀ g ∈ gs.take j, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan g (List.mem_of_mem_take hg)
    have hfan_drop : ∀ g ∈ gs.drop (j + 1), g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan g (List.mem_of_mem_drop hg)
    have hpre := elimRun_inv n' (gs.take j) hfan_take st0 [] [] (by simp) (by simpa using hbd0)
    obtain ⟨⟨stP, ngsP, flP, hstP, hngsP, hflP, hslP, hflP_len⟩, _, hfanP, hbdP, _⟩ := hpre
    have hlen_take : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hpre_st_len : ((gs.take j).foldl (elimStep n') (st0, [], [])).1.length = st0.length + j := by
      rw [hstP, List.length_append, hslP, hlen_take]
    have hpre_fl_len : ((gs.take j).foldl (elimStep n') (st0, [], [])).2.2.length = j := by
      rw [hflP, List.nil_append, hflP_len, hlen_take]
    have hres_eq : gs.foldl (elimStep n') (st0, [], []) =
        (gs.drop (j + 1)).foldl (elimStep n')
          (elimStep n' ((gs.take j).foldl (elimStep n') (st0, [], [])) gs[j]) := by
      have hf := congrArg (fun l => l.foldl (elimStep n') (st0, [], [])) hsplit
      rw [hf, List.foldl_append, List.foldl_cons]
    have hpost := elimRun_inv n' (gs[j] :: gs.drop (j + 1))
      (fun g hg => by
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact hfan _ (List.getElem_mem hj)
        · exact hfan_drop g hg')
      ((gs.take j).foldl (elimStep n') (st0, [], [])).1
      ((gs.take j).foldl (elimStep n') (st0, [], [])).2.1
      ((gs.take j).foldl (elimStep n') (st0, [], [])).2.2
      hfanP hbdP
    obtain ⟨⟨stT, _, _, hstT, _, _, _, _⟩, _, _, _, _⟩ := hpost
    have hres_eq2 : gs.foldl (elimStep n') (st0, [], []) =
        (gs[j] :: gs.drop (j + 1)).foldl (elimStep n') ((gs.take j).foldl (elimStep n') (st0, [], [])) := by
      have hf := congrArg (fun l => l.foldl (elimStep n') (st0, [], [])) hsplit
      rw [hf, List.foldl_append]
    refine ⟨hpre_st_len, ?_, ?_⟩
    · intro i hi
      rw [hres_eq2, hstT, List.getD_append _ _ _ _ (by omega)]
    · intro sym hsym
      set pre := (gs.take j).foldl (elimStep n') (st0, [], [])
      have hstep_j : elimStep n' pre gs[j] = (pre.1 ++ [sym], pre.2.1, pre.2.2 ++ [true]) := by
        dsimp only [elimStep]
        change Sum.elim
          (fun s => (pre.1 ++ [s], pre.2.1, pre.2.2 ++ [true]))
          (fun ng => (pre.1 ++ [Sum.inr (n' + pre.2.1.length)], pre.2.1 ++ [ng], pre.2.2 ++ [false]))
          (elimGate gs[j].op (gs[j].inputs.map fun i => pre.1.getD i (Sum.inl false))) = _
        rw [hsym]; rfl
      have hgj := hfan gs[j] (List.getElem_mem hj)
      have hvs_len : (gs[j].inputs.map fun i => pre.1.getD i (Sum.inl false)).length ≤ 2 := by simp [hgj.2]
      have hbd_next : ∀ s ∈ pre.1 ++ [sym], ∀ k, s = Sum.inr k → k < n' + pre.2.1.length := by
        intro s hs k hk
        rcases List.mem_append.mp hs with h1 | h1
        · exact hbdP s h1 k hk
        · simp only [List.mem_singleton] at h1; rw [h1] at hk
          have hmem := (elimGate_ok gs[j].op hgj.1 _ hvs_len []).1 sym hsym |>.2 k hk
          simp only [List.mem_map] at hmem
          obtain ⟨idx, _, hidx⟩ := hmem
          by_cases hlt : idx < pre.1.length
          · have hmem_pre : pre.1.getD idx (Sum.inl false) ∈ pre.1 := by
              rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
            exact hbdP _ hmem_pre k hidx
          · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)] at hidx; cases hidx
      have hdrop := elimRun_inv n' (gs.drop (j + 1)) hfan_drop (pre.1 ++ [sym]) pre.2.1 (pre.2.2 ++ [true]) hfanP hbd_next
      obtain ⟨⟨stD, _, flD, hstD, _, hflD, _, _⟩, _, _, _, _⟩ := hdrop
      rw [hres_eq, hstep_j]
      refine ⟨?_, ?_⟩
      · rw [hstD, List.getD_append _ _ _ _ (by simp; omega), ← hpre_st_len, getD_snoc_end]
      · rw [hflD, List.getD_append _ _ _ _ (by simp; omega), ← hpre_fl_len, getD_snoc_end]
  have count_ge_three (l : List Bool) (a b c : Fin l.length)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : l.getD a.val false = true) (hb : l.getD b.val false = true)
      (hc : l.getD c.val false = true) :
      3 ≤ l.count true := by
    let S : Finset (Fin l.length) := {a, b, c}
    have hcard : S.card = 3 := by simp [S, hab, hac, hbc]
    have hsub : S ⊆ Finset.univ.filter (fun i : Fin l.length => l.get i = true) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hget (k : Fin l.length) (hk : l.getD k.val false = true) : l.get k = true := by
        simpa [List.getD_eq_getElem _ _ k.isLt] using hk
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hget x ha
      · exact hget x hb
      · exact hget x hc
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    have hcnt : ∀ m : List Bool, (Finset.univ.filter (fun i : Fin m.length => m.get i = true)).card = m.count true := by
      intro m
      rw [Finset.card_filter]
      induction m with
      | nil => simp
      | cons x xs ih =>
        rw [List.count_cons]
        change (∑ i : Fin (xs.length + 1), if (x :: xs).get i = true then 1 else 0) = _
        rw [Fin.sum_univ_succ]
        have htail : (∑ i : Fin xs.length, if (x :: xs).get i.succ = true then 1 else 0) = xs.count true := ih
        rw [htail]
        cases x <;> simp [Nat.add_comm]
    have hcnt_l := hcnt l
    omega
  have count_ge_two (l : List Bool) (a b : Fin l.length)
      (hab : a ≠ b)
      (ha : l.getD a.val false = true) (hb : l.getD b.val false = true) :
      2 ≤ l.count true := by
    let S : Finset (Fin l.length) := {a, b}
    have hcard : S.card = 2 := by simp [S, hab]
    have hsub : S ⊆ Finset.univ.filter (fun i : Fin l.length => l.get i = true) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hget (k : Fin l.length) (hk : l.getD k.val false = true) : l.get k = true := by
        simpa [List.getD_eq_getElem _ _ k.isLt] using hk
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hget x ha
      · exact hget x hb
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    have hcnt : ∀ m : List Bool, (Finset.univ.filter (fun i : Fin m.length => m.get i = true)).card = m.count true := by
      intro m
      rw [Finset.card_filter]
      induction m with
      | nil => simp
      | cons x xs ih =>
        rw [List.count_cons]
        change (∑ i : Fin (xs.length + 1), if (x :: xs).get i = true then 1 else 0) = _
        rw [Fin.sum_univ_succ]
        have htail : (∑ i : Fin xs.length, if (x :: xs).get i.succ = true then 1 else 0) = xs.count true := ih
        rw [htail]
        cases x <;> simp [Nat.add_comm]
    have hcnt_l := hcnt l
    omega
  -- Main proof!
  intro x1 x2 x3 hfan1 hsize1
  refine Classical.byContradiction fun hno_wit => ?_
  push Not at hno_wit
  -- Helper: given a FanInTwo circuit C of size ≤ 18 and st0 of length 11 with values in Fin 10 / Bool matching P10, derive False via h_p10_18
  have absurd_p10_from (C : PEqualNP.CircuitLowerBounds.Circuit) (hfanC : PEqualNP.MetaComplexity.FanInTwo C)
      (hsizeC : C.size ≤ 18) (st0 : List (Bool ⊕ ℕ)) (hst0_len : st0.length = 11)
      (hst0_bd : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < 10)
      (hC_eq : ∀ x : Fin 10 → Bool,
        C.eval (st0.map fun s => evalSym s (List.ofFn x)) = p10 x) : False := by
    have hinv := elimRun_inv 10 C.gates hfanC st0 [] [] (by simp) (by simpa using hst0_bd)
    obtain ⟨⟨stT, _, _, hst, _, _, hsl, _⟩, hcnt, hfan_new, _, hsem⟩ := hinv
    set res := C.gates.foldl (elimStep 10) (st0, [], [])
    have hsem_x (x : Fin 10 → Bool) :
        evalSym (res.1.getD C.output (Sum.inl false)) (res.2.1.foldl step (List.ofFn x)) = p10 x := by
      rw [← hC_eq x]
      let w0 := st0.map fun s => evalSym s (List.ofFn x)
      have hw0_len : w0.length = st0.length := by simp [w0]
      have hagree0 : ∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (List.ofFn x) = w0.getD i false := by
        intro i hi
        rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega : i < w0.length)]
        simp [w0]
      by_cases hout : C.output < res.1.length
      · exact hsem (List.ofFn x) w0 (List.length_ofFn) hw0_len hagree0 C.output hout
      · have hlen_res : res.1.length = 11 + C.gates.length := by rw [hst, List.length_append, hst0_len, hsl]
        have hlen_w : (C.gates.foldl step w0).length = 11 + C.gates.length := by rw [wires_len, hw0_len, hst0_len]
        change evalSym (res.1.getD C.output (Sum.inl false)) _ = (C.gates.foldl step w0).getD C.output false
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hout),
          List.getD_eq_default _ _ (by omega : (C.gates.foldl step w0).length ≤ C.output)]
        rfl
    cases hout_sym : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      have h1 := hsem_x (fun _ => false)
      have h2 := hsem_x (fun _ => true)
      rw [hout_sym] at h1 h2
      have hne : p10 (fun _ => false) ≠ p10 (fun _ => true) := by decide
      exact hne (h1.symm.trans h2)
    | inr k =>
      apply h_p10_18
      refine ⟨⟨res.2.1, k⟩, hfan_new, ?_, fun x => ?_⟩
      · change res.2.1.length ≤ 18
        simp only [List.length_nil, List.count_nil, zero_add] at hcnt
        have hlen18 : C.gates.length ≤ 18 := hsizeC
        omega
      · have hx := hsem_x x
        rw [hout_sym] at hx
        exact hx
  -- Check the 4 cases of (x3 false, x3 true)!
  have hmap_x2 (x : Fin 10 → Bool) :
      ((List.finRange 10).map fun i => Sum.inr (x2 i).val).map (fun s => evalSym s (List.ofFn x)) = List.ofFn (x ∘ x2) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_finRange, evalSym, Sum.elim_inr, List.getElem_ofFn, Function.comp_apply]
    have hi10 : i < 10 := by simp at h1; exact h1
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (x2 ⟨i, hi10⟩).isLt), List.getElem_ofFn]
    rfl
  cases hx3f : x3 false with
  | false =>
    cases hx3t : x3 true with
    | false =>
      let st0 : List (Bool ⊕ ℕ) := ((List.finRange 10).map fun i => Sum.inr (x2 i).val) ++ [Sum.inl false]
      apply absurd_p10_from x1 hfan1 hsize1 st0 (by simp [st0])
      · intro s hs k hk
        simp only [st0, List.mem_append, List.mem_map, List.mem_singleton] at hs
        rcases hs with ⟨i, _, rfl⟩ | rfl
        · cases hk; exact (x2 i).isLt
        · cases hk
      · intro x
        have hx3_val : x3 (x 0) = false := by cases x 0 <;> assumption
        have hst : st0.map (fun s => evalSym s (List.ofFn x)) = List.ofFn (x ∘ x2) ++ [x3 (x 0)] := by
          simp only [st0, List.map_append, List.map_cons, List.map_nil, hmap_x2, hx3_val]; rfl
        rw [hst]; exact hno_wit x
    | true =>
      let st0 : List (Bool ⊕ ℕ) := ((List.finRange 10).map fun i => Sum.inr (x2 i).val) ++ [Sum.inr 0]
      apply absurd_p10_from x1 hfan1 hsize1 st0 (by simp [st0])
      · intro s hs k hk
        simp only [st0, List.mem_append, List.mem_map, List.mem_singleton] at hs
        rcases hs with ⟨i, _, rfl⟩ | rfl
        · cases hk; exact (x2 i).isLt
        · cases hk; omega
      · intro x
        have hx3_val : x3 (x 0) = x 0 := by cases x 0 <;> assumption
        have hget0 : (List.ofFn x).getD 0 false = x 0 := by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
        have hst : st0.map (fun s => evalSym s (List.ofFn x)) = List.ofFn (x ∘ x2) ++ [x3 (x 0)] := by
          simp only [st0, List.map_append, List.map_cons, List.map_nil, hmap_x2, evalSym, Sum.elim_inr, hget0, hx3_val]
        rw [hst]; exact hno_wit x
  | true =>
    cases hx3t : x3 true with
    | true =>
      let st0 : List (Bool ⊕ ℕ) := ((List.finRange 10).map fun i => Sum.inr (x2 i).val) ++ [Sum.inl true]
      apply absurd_p10_from x1 hfan1 hsize1 st0 (by simp [st0])
      · intro s hs k hk
        simp only [st0, List.mem_append, List.mem_map, List.mem_singleton] at hs
        rcases hs with ⟨i, _, rfl⟩ | rfl
        · cases hk; exact (x2 i).isLt
        · cases hk
      · intro x
        have hx3_val : x3 (x 0) = true := by cases x 0 <;> assumption
        have hst : st0.map (fun s => evalSym s (List.ofFn x)) = List.ofFn (x ∘ x2) ++ [x3 (x 0)] := by
          simp only [st0, List.map_append, List.map_cons, List.map_nil, hmap_x2, hx3_val]; rfl
        rw [hst]; exact hno_wit x
    | false =>
      -- Now x3 = Bool.not! First remap x1 to eliminate x2, obtaining a circuit D on List.ofFn x ++ [!x 0] of size ≤ 18.
      have hex_D : ∃ s : ℕ, s ≤ 18 ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = s ∧
          ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = p10 x := by
        let stR : List (Bool ⊕ ℕ) := ((List.finRange 10).map fun i => Sum.inr (x2 i).val) ++ [Sum.inr 10]
        have hstR_len : stR.length = 11 := by simp [stR]
        have hstR_bd : ∀ s ∈ stR, ∀ k, s = Sum.inr k → k < 11 := by
          intro s hs k hk
          simp only [stR, List.mem_append, List.mem_map, List.mem_singleton] at hs
          rcases hs with ⟨i, _, rfl⟩ | rfl
          · cases hk; have := (x2 i).isLt; omega
          · cases hk; omega
        have hinv := elimRun_inv 11 x1.gates hfan1 stR [] [] (by simp) (by simpa using hstR_bd)
        obtain ⟨⟨stT, _, _, hst, _, _, hsl, _⟩, hcnt, hfan_new, _, hsem⟩ := hinv
        set res := x1.gates.foldl (elimStep 11) (stR, [], [])
        have hsem_x (x : Fin 10 → Bool) :
            evalSym (res.1.getD x1.output (Sum.inl false)) (res.2.1.foldl step (List.ofFn x ++ [!x 0])) = p10 x := by
          have hx3_val : x3 (x 0) = !x 0 := by cases x 0 <;> assumption
          have h0 : x1.eval (List.ofFn (x ∘ x2) ++ [!x 0]) = p10 x := by
            have := hno_wit x; rw [hx3_val] at this; exact this
          rw [← h0]
          let w0 := List.ofFn (x ∘ x2) ++ [!x 0]
          have hw0_len : w0.length = stR.length := by simp [w0, hstR_len]
          have hagree0 : ∀ i < stR.length, evalSym (stR.getD i (Sum.inl false)) (List.ofFn x ++ [!x 0]) = w0.getD i false := by
            intro i hi
            by_cases hi10 : i < 10
            · have hst_i : stR.getD i (Sum.inl false) = Sum.inr (x2 ⟨i, hi10⟩).val := by
                rw [List.getD_append _ _ _ _ (by simp [hi10]),
                  List.getD_eq_getElem _ _ (by simp [hi10]), List.getElem_map, List.getElem_finRange]; rfl
              rw [hst_i]
              simp only [evalSym, Sum.elim_inr]
              rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact (x2 ⟨i, hi10⟩).isLt),
                List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (x2 ⟨i, hi10⟩).isLt),
                List.getElem_ofFn]
              rw [List.getD_append _ _ _ _ (by simp [hi10]),
                List.getD_eq_getElem _ _ (by simp [hi10]), List.getElem_ofFn]
              rfl
            · have hi_eq : i = 10 := by omega
              subst hi_eq
              have hst10 : stR.getD 10 (Sum.inl false) = Sum.inr 10 := by
                have hl10 : ((List.finRange 10).map fun i => (Sum.inr (x2 i).val : Bool ⊕ ℕ)).length = 10 := by simp
                dsimp only [stR]
                simpa only [hl10] using getD_snoc_end ((List.finRange 10).map fun i => (Sum.inr (x2 i).val : Bool ⊕ ℕ)) (Sum.inr 10) (Sum.inl false)
              rw [hst10]
              simp only [evalSym, Sum.elim_inr]
              have hA : (List.ofFn x ++ [!x 0]).getD 10 false = !x 0 := by
                simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn x) (!x 0) false
              have hB : w0.getD 10 false = !x 0 := by
                dsimp only [w0]
                simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn (x ∘ x2)) (!x 0) false
              rw [hA, hB]
          by_cases hout : x1.output < res.1.length
          · exact hsem (List.ofFn x ++ [!x 0]) w0 (by simp) hw0_len hagree0 x1.output hout
          · have hlen_res : res.1.length = 11 + x1.gates.length := by rw [hst, List.length_append, hstR_len, hsl]
            have hlen_w : (x1.gates.foldl step w0).length = 11 + x1.gates.length := by rw [wires_len, hw0_len, hstR_len]
            change evalSym (res.1.getD x1.output (Sum.inl false)) _ = (x1.gates.foldl step w0).getD x1.output false
            rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hout),
              List.getD_eq_default _ _ (by omega : (x1.gates.foldl step w0).length ≤ x1.output)]
            rfl
        cases hout_sym : res.1.getD x1.output (Sum.inl false) with
        | inl b =>
          have h1 := hsem_x (fun _ => false)
          have h2 := hsem_x (fun _ => true)
          rw [hout_sym] at h1 h2
          have hne : p10 (fun _ => false) ≠ p10 (fun _ => true) := by decide
          exact False.elim (hne (h1.symm.trans h2))
        | inr k =>
          refine ⟨res.2.1.length, ?_, ⟨res.2.1, k⟩, hfan_new, rfl, fun x => ?_⟩
          · simp only [List.length_nil, List.count_nil, zero_add] at hcnt
            have hlen18 : x1.gates.length ≤ 18 := hsize1
            omega
          · have hx := hsem_x x
            rw [hout_sym] at hx
            exact hx
      -- Pick a MINIMAL-size circuit D on List.ofFn x ++ [!x 0]!
      have hex_min : ∀ n : ℕ,
          (∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = n ∧
            ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = p10 x) →
          ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ n ∧
            (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = p10 x) ∧
            (∀ D' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D' → D'.size < D.size →
              (∀ x : Fin 10 → Bool, D'.eval (List.ofFn x ++ [!x 0]) = p10 x) → False) := by
        intro n
        induction n using Nat.strong_induction_on with
        | ind n ih =>
          intro hD
          obtain ⟨D0, hf0, hs0, he0⟩ := hD
          rcases Classical.em (∃ D' : PEqualNP.CircuitLowerBounds.Circuit,
              PEqualNP.MetaComplexity.FanInTwo D' ∧ D'.size < D0.size ∧
              ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x ++ [!x 0]) = p10 x) with ⟨D', hf', hs', he'⟩ | hmin
          · obtain ⟨Dm, hfm, hsm, hem, hminm⟩ := ih D'.size (by omega) ⟨D', hf', rfl, he'⟩
            exact ⟨Dm, hfm, by omega, hem, hminm⟩
          · exact ⟨D0, hf0, le_of_eq hs0, he0, fun D' hf' hs' he' => hmin ⟨D', hf', hs', he'⟩⟩
      obtain ⟨s0, hs0_le, hD0⟩ := hex_D
      obtain ⟨D, hfanD, hsizeD_le, hDeval, hD_min⟩ := hex_min s0 hD0
      let sMin := D.size
      have hsMin_le : sMin ≤ 18 := le_trans hsizeD_le hs0_le
      obtain ⟨gs, out⟩ := D
      have hlen_gs : gs.length = sMin := rfl
      have hfan_gs : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := hfanD
      have heval (x : Fin 10 → Bool) : (gs.foldl step (List.ofFn x ++ [!x 0])).getD out false = p10 x := hDeval x
      -- Helper: replacing gate r with a 0-input AND or OR gate preserving heval contradicts minimality!
      have no_const_mod (gs' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ) (hr : r < gs'.length)
          (hlen' : gs'.length = gs.length)
          (hfan' : ∀ g ∈ gs', g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
          (hgr_in : (gs'[r]).inputs = [])
          (heval' : ∀ x : Fin 10 → Bool, (gs'.foldl step (List.ofFn x ++ [!x 0])).getD out false = p10 x) :
          False := by
        let id11 : List (Bool ⊕ ℕ) := (List.finRange 11).map fun i => Sum.inr i.val
        have hid11_len : id11.length = 11 := by simp [id11]
        have hid11_bd : ∀ s ∈ id11, ∀ k, s = Sum.inr k → k < 11 := by
          intro s hs k hk
          simp only [id11, List.mem_map] at hs
          obtain ⟨i, _, rfl⟩ := hs; cases hk; exact i.isLt
        have hid11_getD (i : ℕ) (hi : i < 11) : id11.getD i (Sum.inl false) = Sum.inr i := by
          rw [List.getD_eq_getElem _ _ (by simp [id11]; omega)]; simp [id11]
        have hinv := elimRun_inv 11 gs' hfan' id11 [] [] (by simp) (by simpa using hid11_bd)
        obtain ⟨⟨stT, _, flT, hst, _, hfl, hsl, hfl_len⟩, hcnt, hfan_new, _, hsem⟩ := hinv
        set res := gs'.foldl (elimStep 11) (id11, [], [])
        have hat := elimRun_at_gate 11 gs' hfan' id11 hid11_bd r hr
        obtain ⟨_, _, hgate_r⟩ := hat
        have hfl_r : res.2.2.getD r false = true := by
          have hop := (hfan' gs'[r] (List.getElem_mem hr)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop | hop
          · exact (hgate_r (Sum.inl true) (by simp [hop, hgr_in, elimGate, elimAnd])).2
          · exact (hgate_r (Sum.inl false) (by simp [hop, hgr_in, elimGate, elimOr])).2
          · exact (hgate_r (Sum.inl true) (by simp [hop, hgr_in, elimGate, elimNot])).2
        have hfl_pos : 1 ≤ res.2.2.count true := by
          have hlen_fl : res.2.2.length = gs'.length := by rw [hfl, List.nil_append, hfl_len]
          have hmem : true ∈ res.2.2 := by
            have hr' : r < res.2.2.length := by omega
            rw [← hfl_r, List.getD_eq_getElem _ _ hr']; exact List.getElem_mem hr'
          exact List.count_pos_iff.mpr hmem
        have hnew_lt : res.2.1.length < gs.length := by
          simp only [List.length_nil, List.count_nil, zero_add] at hcnt; omega
        have hsem_x (x : Fin 10 → Bool) :
            evalSym (res.1.getD out (Sum.inl false)) (res.2.1.foldl step (List.ofFn x ++ [!x 0])) = p10 x := by
          rw [← heval' x]
          have hagree0 : ∀ i < id11.length, evalSym (id11.getD i (Sum.inl false)) (List.ofFn x ++ [!x 0]) = (List.ofFn x ++ [!x 0]).getD i false := by
            intro i hi; rw [hid11_len] at hi; rw [hid11_getD i hi]; rfl
          by_cases hout : out < res.1.length
          · exact hsem (List.ofFn x ++ [!x 0]) (List.ofFn x ++ [!x 0]) (by simp) (by simp [hid11_len]) hagree0 out hout
          · have hlen_res : res.1.length = 11 + gs'.length := by rw [hst, List.length_append, hid11_len, hsl]
            have hlen_w : (gs'.foldl step (List.ofFn x ++ [!x 0])).length = 11 + gs'.length := by rw [wires_len]; simp
            rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hout),
              List.getD_eq_default _ _ (by omega : (gs'.foldl step (List.ofFn x ++ [!x 0])).length ≤ out)]
            rfl
        cases hout_sym : res.1.getD out (Sum.inl false) with
        | inl b =>
          have h1 := hsem_x (fun _ => false)
          have h2 := hsem_x (fun _ => true)
          rw [hout_sym] at h1 h2
          have hne : p10 (fun _ => false) ≠ p10 (fun _ => true) := by decide
          exact hne (h1.symm.trans h2)
        | inr k =>
          apply hD_min ⟨res.2.1, k⟩ hfan_new hnew_lt
          intro x; have hx := hsem_x x; rw [hout_sym] at hx; exact hx
      -- Liveness: every gate r has out = 11 + r or a later active reader j > r!
      have gate_used (r : Fin gs.length) (hout_ne : out ≠ 11 + r.val) :
          ∃ j : Fin gs.length, r.val < j.val ∧ (11 + r.val) ∈ active (gs.get j) := by
        refine Classical.byContradiction fun hno => ?_
        push Not at hno
        let gs' := gs.set r.val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
        have hlen' : gs'.length = gs.length := by simp [gs']
        have hfan' : ∀ g ∈ gs', g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
          intro g hg
          rcases List.mem_iff_getElem.mp hg with ⟨i, hi, rfl⟩
          by_cases hir : i = r.val
          · subst hir; simp [gs']
          · simp only [gs', List.getElem_set_ne (Ne.symm hir)]
            exact hfan_gs _ (List.getElem_mem (by simp [gs'] at hi; exact hi))
        have heval' (x : Fin 10 → Bool) : (gs'.foldl step (List.ofFn x ++ [!x 0])).getD out false = p10 x := by
          rw [← heval x]
          have hagree_all (k : ℕ) (hk : k ≤ gs.length) :
              ∀ i, i ≠ 11 + r.val →
                ((gs'.take k).foldl step (List.ofFn x ++ [!x 0])).getD i false =
                ((gs.take k).foldl step (List.ofFn x ++ [!x 0])).getD i false := by
            induction k with
            | zero => intro i _; rfl
            | succ k ih =>
              have hklt : k < gs.length := Nat.lt_of_succ_le hk
              have hklt' : k < gs'.length := by omega
              rw [List.take_succ_eq_append_getElem hklt', List.take_succ_eq_append_getElem hklt,
                List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
                List.foldl_cons, List.foldl_nil]
              set w1 := (gs'.take k).foldl step (List.ofFn x ++ [!x 0])
              set w2 := (gs.take k).foldl step (List.ofFn x ++ [!x 0])
              have hlw1 : w1.length = 11 + k := by
                have hle' : k ≤ gs'.length := by omega
                simp [w1, wires_len, List.length_take_of_le hle']
              have hlw2 : w2.length = 11 + k := by
                simp [w2, wires_len, List.length_take_of_le (Nat.le_of_lt hklt)]
              intro i hine
              by_cases hilt : i < 11 + k
              · simp only [step]
                rw [List.getD_append _ _ _ _ (by omega : i < w1.length),
                  List.getD_append _ _ _ _ (by omega : i < w2.length)]
                exact ih (Nat.le_of_lt hklt) i hine
              · by_cases hieq : i = 11 + k
                · subst hieq
                  have hkne : k ≠ r.val := by omega
                  have hgeq : gs'[k] = gs[k] := by simp [gs', List.getElem_set_ne (Ne.symm hkne)]
                  have he1 : (step w1 gs'[k]).getD (11 + k) false =
                      gs'[k].op.eval (gs'[k].inputs.map fun idx => w1.getD idx false) := by
                    simp only [step]; rw [← hlw1, getD_snoc_end]
                  have he2 : (step w2 gs[k]).getD (11 + k) false =
                      gs[k].op.eval (gs[k].inputs.map fun idx => w2.getD idx false) := by
                    simp only [step]; rw [← hlw2, getD_snoc_end]
                  rw [he1, he2, hgeq]
                  apply eval_active_congr gs[k] (hfan_gs _ (List.getElem_mem hklt)).1
                  intro idx hidx
                  by_cases hkr : r.val < k
                  · have hidx_ne : idx ≠ 11 + r.val := by
                      intro heq; subst heq; exact hno ⟨k, hklt⟩ hkr (by simpa using hidx)
                    exact ih (Nat.le_of_lt hklt) idx hidx_ne
                  · by_cases hidx_lt : idx < 11 + k
                    · have hidx_ne : idx ≠ 11 + r.val := by omega
                      exact ih (Nat.le_of_lt hklt) idx hidx_ne
                    · rw [List.getD_eq_default _ _ (by omega : w1.length ≤ idx),
                        List.getD_eq_default _ _ (by omega : w2.length ≤ idx)]
                · rw [List.getD_eq_default _ _ (by simp [step, hlw1]; omega),
                    List.getD_eq_default _ _ (by simp [step, hlw2]; omega)]
          have hfull := hagree_all gs.length (le_refl _) out hout_ne
          rw [← List.take_length (l := gs'), hlen', hfull, List.take_length]
        exact no_const_mod gs' r.val (by omega) hlen' hfan' (by simp [gs']) heval'
      -- No gate j can actively read BOTH wire 0 and wire 10!
      have no_both010 (j : Fin gs.length)
          (h0 : 0 ∈ active (gs.get j)) (h10 : 10 ∈ active (gs.get j)) : False := by
        have hgj_fan := hfan_gs (gs.get j) (List.get_mem ..)
        have hnot_not : (gs.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
          intro hnot
          rw [active_of_not _ hnot] at h0 h10
          cases hin : (gs.get j).inputs with
          | nil => rw [hin] at h0; simp at h0
          | cons a rest =>
            rw [hin] at h0 h10
            simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at h0 h10
            omega
        rw [active_of_ne_not _ hnot_not] at h0 h10
        have hin_pair : (gs.get j).inputs = [0, 10] ∨ (gs.get j).inputs = [10, 0] := by
          cases hin : (gs.get j).inputs with
          | nil => rw [hin] at h0; cases h0
          | cons a rest =>
            cases rest with
            | nil =>
              rw [hin] at h0 h10; simp only [List.mem_singleton] at h0 h10; omega
            | cons b rest2 =>
              cases rest2 with
              | cons _ _ => have := hgj_fan.2; rw [hin] at this; simp at this
              | nil =>
                rw [hin] at h0 h10
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h10
                rcases h0 with rfl | rfl <;> rcases h10 with h10 | h10
                · omega
                · subst h10; exact Or.inl rfl
                · subst h10; exact Or.inr rfl
                · omega
        have hwire0 (x : Fin 10 → Bool) :
            ((gs.take j.val).foldl step (List.ofFn x ++ [!x 0])).getD 0 false = x 0 := by
          rw [wires_getD_lt _ _ 0 (by simp), List.getD_append _ _ _ _ (by simp),
            List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
        have hwire10 (x : Fin 10 → Bool) :
            ((gs.take j.val).foldl step (List.ofFn x ++ [!x 0])).getD 10 false = !x 0 := by
          rw [wires_getD_lt _ _ 10 (by simp)]
          simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn x) (!x 0) false
        have hconst_j : ∃ c_op : PEqualNP.CircuitLowerBounds.GateOp,
            c_op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
            ∀ x : Fin 10 → Bool,
              c_op.eval [] = gs[j.val].op.eval (gs[j.val].inputs.map fun i => ((gs.take j.val).foldl step (List.ofFn x ++ [!x 0])).getD i false) := by
          have hop := hgj_fan.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop | hop
          · refine ⟨PEqualNP.CircuitLowerBounds.GateOp.or, Or.inr rfl, fun x => ?_⟩
            change false = _
            change gs[j.val].op = PEqualNP.CircuitLowerBounds.GateOp.and at hop
            rcases hin_pair with hin | hin <;>
            · change gs[j.val].inputs = _ at hin
              rw [hop, hin]
              simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hwire0 x, hwire10 x]
              cases x 0 <;> rfl
          · refine ⟨PEqualNP.CircuitLowerBounds.GateOp.and, Or.inl rfl, fun x => ?_⟩
            change true = _
            change gs[j.val].op = PEqualNP.CircuitLowerBounds.GateOp.or at hop
            rcases hin_pair with hin | hin <;>
            · change gs[j.val].inputs = _ at hin
              rw [hop, hin]
              simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hwire0 x, hwire10 x]
              cases x 0 <;> rfl
          · exact False.elim (hnot_not hop)
        obtain ⟨c_op, hc_op, hc_eq⟩ := hconst_j
        let gs' := gs.set j.val ⟨c_op, []⟩
        have hlen' : gs'.length = gs.length := by simp [gs']
        have hfan' : ∀ g ∈ gs', g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
          intro g hg
          rcases List.mem_iff_getElem.mp hg with ⟨i, hi, rfl⟩
          by_cases hij : i = j.val
          · subst hij
            simp only [gs', List.getElem_set_self, List.length_nil, Nat.zero_le, and_true]
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc_op ⊢
            rcases hc_op with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · simp only [gs', List.getElem_set_ne (Ne.symm hij)]
            exact hfan_gs _ (List.getElem_mem (by simp [gs'] at hi; exact hi))
        have heval' (x : Fin 10 → Bool) : (gs'.foldl step (List.ofFn x ++ [!x 0])).getD out false = p10 x := by
          rw [← heval x]
          have hall (k : ℕ) (hk : k ≤ gs.length) :
              (gs'.take k).foldl step (List.ofFn x ++ [!x 0]) = (gs.take k).foldl step (List.ofFn x ++ [!x 0]) := by
            induction k with
            | zero => rfl
            | succ k ih =>
              have hklt : k < gs.length := Nat.lt_of_succ_le hk
              have hklt' : k < gs'.length := by omega
              rw [List.take_succ_eq_append_getElem hklt', List.take_succ_eq_append_getElem hklt,
                List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
                List.foldl_cons, List.foldl_nil, ih (Nat.le_of_lt hklt)]
              by_cases hkj : k = j.val
              · have hset_self : gs'[k] = ⟨c_op, []⟩ := by simp [gs', hkj]
                rw [hset_self]
                simp only [step, List.map_nil]
                congr 1; congr 1
                have hce_m : ∀ (m : ℕ) (hm : m < gs.length), m = j.val →
                    c_op.eval [] = gs[m].op.eval (gs[m].inputs.map fun i => ((gs.take m).foldl step (List.ofFn x ++ [!x 0])).getD i false) := by
                  intro m hm hmj; subst hmj; exact hc_eq x
                exact hce_m k hklt hkj
              · simp [gs', List.getElem_set_ne (Ne.symm hkj)]
          have hfull := hall gs.length (le_refl _)
          rw [← List.take_length (l := gs'), hlen', hfull, List.take_length]
        exact no_const_mod gs' j.val (by omega) hlen' hfan' (by simp [gs']) heval'
      -- Now run elimRun 9 on D with init0 (setting x 0 := false, !x 0 := true, rest → P-v)!
      let init0 : List (Bool ⊕ ℕ) :=
        [Sum.inl false, Sum.inr 4, Sum.inr 0, Sum.inr 1, Sum.inr 6, Sum.inr 7,
         Sum.inr 3, Sum.inr 5, Sum.inr 2, Sum.inr 8, Sum.inl true]
      have hinit0_len : init0.length = 11 := rfl
      have hinit0_bd : ∀ s ∈ init0, ∀ k, s = Sum.inr k → k < 9 := by
        intro s hs k hk
        simp only [init0, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk <;> omega
      have hinit0_f (y : Fin 9 → Bool) :
          p10 (fun i : Fin 10 => evalSym (init0.getD i.val (Sum.inl false)) (List.ofFn y)) = pv y := by
        have key : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
            (false && a4 || a4 && a0 || a0 && a1 || a1 && a6 || a6 && false ||
             false && a7 || a4 && a3 || a0 && a5 || a1 && a2 || a6 && a8 ||
             a7 && a5 || a5 && a8 || a8 && a3 || a3 && a2 || a2 && a7) =
            ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
             (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) ||
             (a6 && a8) || (a8 && a5)) := by decide
        have hget (k : ℕ) (hk : k < 9) : (List.ofFn y).getD k false = y ⟨k, hk⟩ := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]
        dsimp only [p10, pv, init0, evalSym]
        change (false && (List.ofFn y).getD 4 false || (List.ofFn y).getD 4 false && (List.ofFn y).getD 0 false ||
            (List.ofFn y).getD 0 false && (List.ofFn y).getD 1 false || (List.ofFn y).getD 1 false && (List.ofFn y).getD 6 false ||
            (List.ofFn y).getD 6 false && false || false && (List.ofFn y).getD 7 false ||
            (List.ofFn y).getD 4 false && (List.ofFn y).getD 3 false || (List.ofFn y).getD 0 false && (List.ofFn y).getD 5 false ||
            (List.ofFn y).getD 1 false && (List.ofFn y).getD 2 false || (List.ofFn y).getD 6 false && (List.ofFn y).getD 8 false ||
            (List.ofFn y).getD 7 false && (List.ofFn y).getD 5 false || (List.ofFn y).getD 5 false && (List.ofFn y).getD 8 false ||
            (List.ofFn y).getD 8 false && (List.ofFn y).getD 3 false || (List.ofFn y).getD 3 false && (List.ofFn y).getD 2 false ||
            (List.ofFn y).getD 2 false && (List.ofFn y).getD 7 false) = _
        rw [hget 0 (by decide), hget 1 (by decide), hget 2 (by decide), hget 3 (by decide),
          hget 4 (by decide), hget 5 (by decide), hget 6 (by decide), hget 7 (by decide), hget 8 (by decide)]
        exact key (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
      have hinv0 := elimRun_inv 9 gs hfan_gs init0 [] [] (by simp) (by simpa using hinit0_bd)
      obtain ⟨⟨stT0, _, flT0, hst0, _, hfl0, hsl0, hfl0_len⟩, hcnt0, hfan0_new, _, hsem0⟩ := hinv0
      set res0 := gs.foldl (elimStep 9) (init0, [], [])
      have hfl0_length : res0.2.2.length = gs.length := by rw [hfl0, List.nil_append, hfl0_len]
      have hres0_sem (y : Fin 9 → Bool) :
          evalSym (res0.1.getD out (Sum.inl false)) (res0.2.1.foldl step (List.ofFn y)) = pv y := by
        let x : Fin 10 → Bool := fun i => evalSym (init0.getD i.val (Sum.inl false)) (List.ofFn y)
        have hx0_false : x 0 = false := rfl
        have hx_eval : (gs.foldl step (List.ofFn x ++ [!x 0])).getD out false = pv y := by
          rw [heval x]; exact hinit0_f y
        rw [← hx_eval]
        have hagree0 : ∀ i < init0.length,
            evalSym (init0.getD i (Sum.inl false)) (List.ofFn y) = (List.ofFn x ++ [!x 0]).getD i false := by
          intro i hi
          by_cases hi10 : i < 10
          · have hlenx : (List.ofFn x).length = 10 := List.length_ofFn
            rw [List.getD_append _ _ _ _ (by omega : i < (List.ofFn x).length),
              List.getD_eq_getElem _ _ (by omega : i < (List.ofFn x).length), List.getElem_ofFn]
          · have hi_eq : i = 10 := by omega
            subst hi_eq
            have hA : (List.ofFn x ++ [!x 0]).getD 10 false = !x 0 := by
              simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn x) (!x 0) false
            rw [hA, hx0_false]; rfl
        by_cases hout : out < res0.1.length
        · exact hsem0 (List.ofFn y) (List.ofFn x ++ [!x 0]) (List.length_ofFn) (by simp [hinit0_len]) hagree0 out hout
        · have hlen_res : res0.1.length = 11 + gs.length := by rw [hst0, List.length_append, hinit0_len, hsl0]
          have hlen_w : (gs.foldl step (List.ofFn x ++ [!x 0])).length = 11 + gs.length := by rw [wires_len]; simp
          rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hout),
            List.getD_eq_default _ _ (by omega : (gs.foldl step (List.ofFn x ++ [!x 0])).length ≤ out)]
          rfl
      have hout0_not_const (b : Bool) : res0.1.getD out (Sum.inl false) ≠ Sum.inl b := by
        intro heq
        have h1 := hres0_sem (fun _ => false)
        have h2 := hres0_sem (fun _ => true)
        rw [heq] at h1 h2
        have hne : pv (fun _ => false) ≠ pv (fun _ => true) := by decide
        exact hne (h1.symm.trans h2)
      have hnew0_ge16 : 16 ≤ res0.2.1.length := by
        refine Classical.byContradiction fun hlt => ?_
        cases hout_sym : res0.1.getD out (Sum.inl false) with
        | inl b => exact hout0_not_const b hout_sym
        | inr k =>
          apply h_pv_15
          refine ⟨⟨res0.2.1, k⟩, hfan0_new, by change res0.2.1.length ≤ 15; omega, fun y => ?_⟩
          have hy := hres0_sem y; rw [hout_sym] at hy; exact hy
      have hcnt0_le2 : res0.2.2.count true ≤ 2 := by
        simp only [List.length_nil, List.count_nil, zero_add] at hcnt0
        omega
      -- Helper: if w < 11 + j, w ∈ active (gs[j]), and res0.1[w] = inl c, then gate j is eliminated!
      have elim_of_const_in (j : Fin gs.length) (w : ℕ) (c : Bool) (hw : w < 11 + j.val)
          (hact : w ∈ active (gs.get j)) (hc : res0.1.getD w (Sum.inl false) = Sum.inl c) :
          res0.2.2.getD j.val false = true ∧
          ((gs.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → res0.1.getD (11 + j.val) (Sum.inl false) = Sum.inl (!c)) ∧
          ((gs.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and → c = false → res0.1.getD (11 + j.val) (Sum.inl false) = Sum.inl false) ∧
          ((gs.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or → c = true → res0.1.getD (11 + j.val) (Sum.inl false) = Sum.inl true) := by
        have hat := elimRun_at_gate 9 gs hfan_gs init0 hinit0_bd j.val j.isLt
        obtain ⟨_, hpre_eq, hgate_j⟩ := hat
        have hpre_w : ((gs.take j.val).foldl (elimStep 9) (init0, [], [])).1.getD w (Sum.inl false) = Sum.inl c := by
          rw [← hpre_eq w (by omega), hc]
        have hgj_fan := hfan_gs gs[j.val] (List.getElem_mem j.isLt)
        change w ∈ active gs[j.val] at hact
        let vs := gs[j.val].inputs.map fun i => ((gs.take j.val).foldl (elimStep 9) (init0, [], [])).1.getD i (Sum.inl false)
        have hvs_len : vs.length ≤ 2 := by simp [vs, hgj_fan.2]
        have hnot_in : gs[j.val].op = PEqualNP.CircuitLowerBounds.GateOp.not → vs.head? = some (Sum.inl c) := by
          intro hnot
          rw [active_of_not _ hnot] at hact
          cases hin : gs[j.val].inputs with
          | nil => rw [hin] at hact; simp at hact
          | cons a rest =>
            rw [hin] at hact
            simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hact
            subst hact
            simp only [vs, hin, List.map_cons, List.head?_cons, hpre_w]
        have hbin_in : gs[j.val].op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → Sum.inl c ∈ vs := by
          intro hne
          have hw_in : w ∈ gs[j.val].inputs := by rwa [active_of_ne_not _ hne] at hact
          exact List.mem_map.mpr ⟨w, hw_in, hpre_w⟩
        obtain ⟨sym, hsym, hsym_not, hsym_and, hsym_or⟩ := elimGate_of_const gs[j.val].op hgj_fan.1 vs hvs_len c hnot_in hbin_in
        have hres := hgate_j sym hsym
        refine ⟨hres.2, fun hnot => ?_, fun hand hcf => ?_, fun hor hct => ?_⟩
        · have heq := hsym_not hnot; simpa [hinit0_len, heq] using hres.1
        · have heq := hsym_and hand hcf; simpa [hinit0_len, heq] using hres.1
        · have heq := hsym_or hor hct; simpa [hinit0_len, heq] using hres.1
      have const_of_two_const (j : Fin gs.length) (w1 w2 : ℕ) (c1 c2 : Bool)
          (hne12 : w1 ≠ w2) (hw1 : w1 < 11 + j.val) (hw2 : w2 < 11 + j.val)
          (ha1 : w1 ∈ active (gs.get j)) (ha2 : w2 ∈ active (gs.get j))
          (hc1 : res0.1.getD w1 (Sum.inl false) = Sum.inl c1)
          (hc2 : res0.1.getD w2 (Sum.inl false) = Sum.inl c2) :
          ∃ c' : Bool, res0.1.getD (11 + j.val) (Sum.inl false) = Sum.inl c' := by
        have hat := elimRun_at_gate 9 gs hfan_gs init0 hinit0_bd j.val j.isLt
        obtain ⟨_, hpre_eq, hgate_j⟩ := hat
        have hp1 : ((gs.take j.val).foldl (elimStep 9) (init0, [], [])).1.getD w1 (Sum.inl false) = Sum.inl c1 := by
          rw [← hpre_eq w1 (by omega), hc1]
        have hp2 : ((gs.take j.val).foldl (elimStep 9) (init0, [], [])).1.getD w2 (Sum.inl false) = Sum.inl c2 := by
          rw [← hpre_eq w2 (by omega), hc2]
        have hgj_fan := hfan_gs gs[j.val] (List.getElem_mem j.isLt)
        change w1 ∈ active gs[j.val] at ha1
        change w2 ∈ active gs[j.val] at ha2
        have hnot_not : gs[j.val].op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
          intro hnot
          rw [active_of_not _ hnot] at ha1 ha2
          cases hin : gs[j.val].inputs with
          | nil => rw [hin] at ha1; simp at ha1
          | cons a rest =>
            rw [hin] at ha1 ha2
            simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at ha1 ha2
            exact hne12 (ha1.trans ha2.symm)
        have h1 : w1 ∈ gs[j.val].inputs := by rwa [active_of_ne_not _ hnot_not] at ha1
        have h2 : w2 ∈ gs[j.val].inputs := by rwa [active_of_ne_not _ hnot_not] at ha2
        cases hin : gs[j.val].inputs with
        | nil => rw [hin] at h1; cases h1
        | cons a rest =>
          cases rest with
          | nil =>
            rw [hin] at h1 h2; simp only [List.mem_singleton] at h1 h2
            exact False.elim (hne12 (h1.trans h2.symm))
          | cons b rest2 =>
            cases rest2 with
            | cons _ _ => have := hgj_fan.2; rw [hin] at this; simp at this
            | nil =>
              rw [hin] at h1 h2; simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
              rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
              · exact False.elim (hne12 h2.symm)
              · subst h2
                obtain ⟨c', hc'⟩ := elimGate_two_const gs[j.val].op hgj_fan.1 c1 c2
                refine ⟨c', ?_⟩
                have hres := hgate_j (Sum.inl c') (by rw [hin, List.map_cons, List.map_cons, List.map_nil, hp1, hp2]; exact hc')
                simpa [hinit0_len] using hres.1
              · subst h2
                obtain ⟨c', hc'⟩ := elimGate_two_const gs[j.val].op hgj_fan.1 c2 c1
                refine ⟨c', ?_⟩
                have hres := hgate_j (Sum.inl c') (by rw [hin, List.map_cons, List.map_cons, List.map_nil, hp1, hp2]; exact hc')
                simpa [hinit0_len] using hres.1
              · exact False.elim (hne12 h2.symm)
      have hres0_0 : res0.1.getD 0 (Sum.inl false) = Sum.inl false := by
        rw [hst0, List.getD_append _ _ _ _ (by omega)]; rfl
      have hres0_10 : res0.1.getD 10 (Sum.inl false) = Sum.inl true := by
        rw [hst0, List.getD_append _ _ _ _ (by omega)]; rfl
      have hD_size_le18 : PEqualNP.CircuitLowerBounds.Circuit.size ⟨gs, out⟩ ≤ 18 := by
        change gs.length ≤ 18; omega
      -- Split on whether any gate of D actively reads wire 0!
      rcases Classical.em (∃ j0 : Fin gs.length, 0 ∈ active (gs.get j0)) with ⟨j0, hj0_reads⟩ | hex0
      · -- Check whether any gate of D actively reads wire 10!
        rcases Classical.em (∃ j10 : Fin gs.length, 10 ∈ active (gs.get j10)) with ⟨j10, hj10_reads⟩ | hex10
        · have hj0_ne_j10 : j0 ≠ j10 := by
            intro heq; subst heq; exact no_both010 j0 hj0_reads hj10_reads
          have hj0_elim := elim_of_const_in j0 0 false (by omega) hj0_reads hres0_0
          have hj10_elim := elim_of_const_in j10 10 true (by omega) hj10_reads hres0_10
          have hfl_j0 : res0.2.2.getD j0.val false = true := hj0_elim.1
          have hfl_j10 : res0.2.2.getD j10.val false = true := hj10_elim.1
          have hcnt_ge2 : 2 ≤ res0.2.2.count true := by
            let fa : Fin res0.2.2.length := ⟨j0.val, by omega⟩
            let fb : Fin res0.2.2.length := ⟨j10.val, by omega⟩
            exact count_ge_two res0.2.2 fa fb
              (fun h => hj0_ne_j10 (Fin.ext (show j0.val = j10.val from congrArg (fun x : Fin res0.2.2.length => x.val) h)))
              hfl_j0 hfl_j10
          have hgs_eq18 : gs.length = 18 := by
            simp only [List.length_nil, List.count_nil, zero_add] at hcnt0; omega
          have only_two (k : Fin gs.length) (hk : res0.2.2.getD k.val false = true) :
              k = j0 ∨ k = j10 := by
            refine Classical.byContradiction fun hnot => ?_
            push Not at hnot
            obtain ⟨hk0, hk10⟩ := hnot
            let fa : Fin res0.2.2.length := ⟨j0.val, by omega⟩
            let fb : Fin res0.2.2.length := ⟨j10.val, by omega⟩
            let fc : Fin res0.2.2.length := ⟨k.val, by omega⟩
            have h3 := count_ge_three res0.2.2 fa fb fc
              (fun h => hj0_ne_j10 (Fin.ext (show j0.val = j10.val from congrArg (fun x : Fin res0.2.2.length => x.val) h)))
              (fun h => hk0 (Fin.ext (show k.val = j0.val from (congrArg (fun x : Fin res0.2.2.length => x.val) h).symm)))
              (fun h => hk10 (Fin.ext (show k.val = j10.val from (congrArg (fun x : Fin res0.2.2.length => x.val) h).symm)))
              hfl_j0 hfl_j10 hk
            omega
          -- Neither j0 nor j10 can output a constant under init0!
          have no_const_out (r : Fin gs.length) (hr : r = j0 ∨ r = j10) (c : Bool)
              (hc : res0.1.getD (11 + r.val) (Sum.inl false) = Sum.inl c) : False := by
            have hout_ne_r : out ≠ 11 + r.val := by
              intro heq; subst heq; exact hout0_not_const c hc
            obtain ⟨r', hr'gt, hr'reads⟩ := gate_used r hout_ne_r
            have hr'_elim := (elim_of_const_in r' (11 + r.val) c (by omega) hr'reads hc).1
            have hr'_ne_r : r' ≠ r := fun h => Nat.ne_of_gt hr'gt (congrArg Fin.val h)
            rcases only_two r' hr'_elim with h1 | h2
            · subst r'
              have hreq : r = j10 := by rcases hr with h | h; exact False.elim (hr'_ne_r h.symm); exact h
              subst r
              obtain ⟨c', hc'⟩ := const_of_two_const j0 (11 + j10.val) 0 c false
                (by omega) (by omega) (by omega) hr'reads hj0_reads hc hres0_0
              have hout_ne_j0 : out ≠ 11 + j0.val := by
                intro heq; subst heq; exact hout0_not_const c' hc'
              obtain ⟨r'', hr''gt, hr''reads⟩ := gate_used j0 hout_ne_j0
              have hr''_elim := (elim_of_const_in r'' (11 + j0.val) c' (by omega) hr''reads hc').1
              rcases only_two r'' hr''_elim with h1'' | h2''
              · exact Nat.ne_of_gt hr''gt (congrArg Fin.val h1'')
              · exact Nat.ne_of_gt (Nat.lt_trans hr'gt hr''gt) (congrArg Fin.val h2'')
            · subst r'
              have hreq : r = j0 := by rcases hr with h | h; exact h; exact False.elim (hr'_ne_r h.symm)
              subst r
              obtain ⟨c', hc'⟩ := const_of_two_const j10 (11 + j0.val) 10 c true
                (by omega) (by omega) (by omega) hr'reads hj10_reads hc hres0_10
              have hout_ne_j10 : out ≠ 11 + j10.val := by
                intro heq; subst heq; exact hout0_not_const c' hc'
              obtain ⟨r'', hr''gt, hr''reads⟩ := gate_used j10 hout_ne_j10
              have hr''_elim := (elim_of_const_in r'' (11 + j10.val) c' (by omega) hr''reads hc').1
              rcases only_two r'' hr''_elim with h1'' | h2''
              · exact Nat.ne_of_gt (Nat.lt_trans hr'gt hr''gt) (congrArg Fin.val h1'')
              · exact Nat.ne_of_gt hr''gt (congrArg Fin.val h2'')
          have hj0_or : (gs.get j0).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
            have hop := (hfan_gs (gs.get j0) (List.get_mem ..)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop | hop
            · exact False.elim (no_const_out j0 (Or.inl rfl) false (hj0_elim.2.2.1 hop rfl))
            · exact hop
            · exact False.elim (no_const_out j0 (Or.inl rfl) (!false) (hj0_elim.2.1 hop))
          have hj10_and : (gs.get j10).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
            have hop := (hfan_gs (gs.get j10) (List.get_mem ..)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop | hop
            · exact hop
            · exact False.elim (no_const_out j10 (Or.inr rfl) true (hj10_elim.2.2.2 hop rfl))
            · exact False.elim (no_const_out j10 (Or.inr rfl) (!true) (hj10_elim.2.1 hop))
          have hj0_in0 : 0 ∈ (gs.get j0).inputs := by
            rwa [active_of_ne_not _ (by rw [hj0_or]; intro h; cases h)] at hj0_reads
          have hj10_in10 : 10 ∈ (gs.get j10).inputs := by
            rwa [active_of_ne_not _ (by rw [hj10_and]; intro h; cases h)] at hj10_reads
          have huniq0 (j : Fin gs.length) (hj : 0 ∈ active (gs.get j)) : j = j0 := by
            have hel := (elim_of_const_in j 0 false (by omega) hj hres0_0).1
            rcases only_two j hel with h | h
            · exact h
            · subst j; exact False.elim (no_both010 j10 hj hj10_reads)
          have huniq10 (j : Fin gs.length) (hj : 10 ∈ active (gs.get j)) : j = j10 := by
            have hel := (elim_of_const_in j 10 true (by omega) hj hres0_10).1
            rcases only_two j hel with h | h
            · subst j; exact False.elim (no_both010 j0 hj0_reads hj)
            · exact h
          exact h_both010 ⟨gs, out⟩ hfanD hgs_eq18 hDeval
            ⟨j0, j10, hj0_ne_j10, hj0_or, hj0_in0, hj10_and, hj10_in10, fun p hp j => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl
              · refine ⟨fun hnot h0 => ?_, fun hne h0 => ?_⟩
                · apply huniq0 j
                  cases hin : (gs.get j).inputs with
                  | nil => rw [hin] at h0; cases h0
                  | cons a rest =>
                    rw [hin] at h0; simp only [List.head?_cons, Option.some.injEq] at h0
                    subst h0; rw [active_of_not _ hnot, hin]; simp
                · apply huniq0 j; rw [active_of_ne_not _ hne]; exact h0
              · refine ⟨fun hnot h10 => ?_, fun hne h10 => ?_⟩
                · apply huniq10 j
                  cases hin : (gs.get j).inputs with
                  | nil => rw [hin] at h10; cases h10
                  | cons a rest =>
                    rw [hin] at h10; simp only [List.head?_cons, Option.some.injEq] at h10
                    subst h10; rw [active_of_not _ hnot, hin]; simp
                · apply huniq10 j; rw [active_of_ne_not _ hne]; exact h10⟩
        · -- No gate of D reads wire 10! So D ignores wire 10 -> gives 18-gate circuit for p10!
          push Not at hex10
          have hout_ne10 : out ≠ 10 := by
            intro heq; subst heq
            have h1 := heval (fun _ => false)
            rw [wires_getD_lt _ _ 10 (by simp)] at h1
            have hA : (List.ofFn (fun _ : Fin 10 => false) ++ [!false]).getD 10 false = !false := by
              simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn (fun _ : Fin 10 => false)) (!false) false
            rw [hA] at h1
            revert h1; decide
          let st0 : List (Bool ⊕ ℕ) := ((List.finRange 10).map fun i => Sum.inr i.val) ++ [Sum.inl false]
          apply absurd_p10_from ⟨gs, out⟩ hfanD hD_size_le18 st0 (by simp [st0])
          · intro s hs k hk
            simp only [st0, List.mem_append, List.mem_map, List.mem_singleton] at hs
            rcases hs with ⟨i, _, rfl⟩ | rfl
            · cases hk; exact i.isLt
            · cases hk
          · intro x
            rw [← heval x]
            have hst_eq : st0.map (fun s => evalSym s (List.ofFn x)) = List.ofFn x ++ [false] := by
              apply List.ext_getElem (by simp [st0])
              intro i h1 h2
              simp only [st0, List.getElem_map]
              by_cases hi10 : i < 10
              · simp only [List.getElem_append_left (by simp [hi10] : i < ((List.finRange 10).map fun i => Sum.inr i.val).length),
                  List.getElem_map, List.getElem_finRange, evalSym, Sum.elim_inr,
                  List.getElem_append_left (by simp [hi10] : i < (List.ofFn x).length), List.getElem_ofFn]
                rw [List.getD_eq_getElem _ _ (by simp [hi10]), List.getElem_ofFn]; rfl
              · have hi_eq : i = 10 := by simp [st0] at h1; omega
                subst hi_eq
                simp [List.getElem_append_right, evalSym]
            change (gs.foldl step (st0.map fun s => evalSym s (List.ofFn x))).getD out false = _
            rw [hst_eq]
            have hagree_all (k : ℕ) (hk : k ≤ gs.length) :
                ∀ i, i ≠ 10 →
                  ((gs.take k).foldl step (List.ofFn x ++ [false])).getD i false =
                  ((gs.take k).foldl step (List.ofFn x ++ [!x 0])).getD i false := by
              induction k with
              | zero =>
                intro i hine
                simp only [List.take_zero, List.foldl_nil]
                by_cases hi10 : i < 10
                · rw [List.getD_append _ _ _ _ (by simp [hi10]), List.getD_append _ _ _ _ (by simp [hi10])]
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
              | succ k ih =>
                have hklt : k < gs.length := Nat.lt_of_succ_le hk
                rw [List.take_succ_eq_append_getElem hklt, List.foldl_append, List.foldl_append,
                  List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
                set w1 := (gs.take k).foldl step (List.ofFn x ++ [false])
                set w2 := (gs.take k).foldl step (List.ofFn x ++ [!x 0])
                have hlw1 : w1.length = 11 + k := by simp [w1, wires_len, List.length_take_of_le (Nat.le_of_lt hklt)]
                have hlw2 : w2.length = 11 + k := by simp [w2, wires_len, List.length_take_of_le (Nat.le_of_lt hklt)]
                intro i hine
                by_cases hilt : i < 11 + k
                · simp only [step]
                  rw [List.getD_append _ _ _ _ (by omega : i < w1.length),
                    List.getD_append _ _ _ _ (by omega : i < w2.length)]
                  exact ih (Nat.le_of_lt hklt) i hine
                · by_cases hieq : i = 11 + k
                  · subst hieq
                    have he1 : (step w1 gs[k]).getD (11 + k) false =
                        gs[k].op.eval (gs[k].inputs.map fun idx => w1.getD idx false) := by
                      simp only [step]; rw [← hlw1, getD_snoc_end]
                    have he2 : (step w2 gs[k]).getD (11 + k) false =
                        gs[k].op.eval (gs[k].inputs.map fun idx => w2.getD idx false) := by
                      simp only [step]; rw [← hlw2, getD_snoc_end]
                    rw [he1, he2]
                    apply eval_active_congr gs[k] (hfan_gs _ (List.getElem_mem hklt)).1
                    intro idx hidx
                    have hne10 : idx ≠ 10 := by
                      intro heq; subst heq; exact hex10 ⟨k, hklt⟩ (by simpa using hidx)
                    exact ih (Nat.le_of_lt hklt) idx hne10
                  · rw [List.getD_eq_default _ _ (by simp [step, hlw1]; omega),
                      List.getD_eq_default _ _ (by simp [step, hlw2]; omega)]
            have hfull := hagree_all gs.length (le_refl _) out hout_ne10
            simpa [List.take_length] using hfull
      · -- Case A: NO gate of D actively reads wire 0!
        push Not at hex0
        have hno0_form : ∀ j : Fin gs.length,
            ((gs.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gs.get j).inputs.head? ≠ some 0) ∧
            ((gs.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 0 ∉ (gs.get j).inputs) := by
          intro j
          refine ⟨fun hnot h0 => ?_, fun hne h0 => ?_⟩
          · apply hex0 j
            cases hin : (gs.get j).inputs with
            | nil => rw [hin] at h0; cases h0
            | cons a rest =>
              rw [hin] at h0; simp only [List.head?_cons, Option.some.injEq] at h0
              subst h0; rw [active_of_not _ hnot, hin]; simp
          · apply hex0 j; rw [active_of_ne_not _ hne]; exact h0
        -- Prove wire 10 has at least 1 reader (otherwise D ignores both 0 and 10 -> independent of x 0!)
        have hex10 : ∃ j1 : Fin gs.length, 10 ∈ active (gs.get j1) := by
          refine Classical.byContradiction fun hno10 => ?_
          push Not at hno10
          have hout_ne0 : out ≠ 0 := by
            intro heq; subst heq
            have h1 := heval (fun i => decide (i.val = 1 ∨ i.val = 2))
            rw [wires_getD_lt _ _ 0 (by simp), List.getD_append _ _ _ _ (by simp),
              List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at h1
            revert h1; decide
          have hout_ne10 : out ≠ 10 := by
            intro heq; subst heq
            have h1 := heval (fun _ => false)
            rw [wires_getD_lt _ _ 10 (by simp)] at h1
            have hA : (List.ofFn (fun _ : Fin 10 => false) ++ [!false]).getD 10 false = !false := by
              simpa only [List.length_ofFn] using getD_snoc_end (List.ofFn (fun _ : Fin 10 => false)) (!false) false
            rw [hA] at h1
            revert h1; decide
          let xA : Fin 10 → Bool := fun i => decide (i.val = 1)
          let xB : Fin 10 → Bool := fun i => decide (i.val = 0 ∨ i.val = 1)
          have hagree (k : ℕ) (hk : k ≤ gs.length) :
              ∀ i, i ≠ 0 → i ≠ 10 →
                ((gs.take k).foldl step (List.ofFn xA ++ [!xA 0])).getD i false =
                ((gs.take k).foldl step (List.ofFn xB ++ [!xB 0])).getD i false := by
            induction k with
            | zero =>
              intro i hne0 hne10
              simp only [List.take_zero, List.foldl_nil]
              by_cases hi10 : i < 10
              · rw [List.getD_append _ _ _ _ (by simp [hi10]), List.getD_append _ _ _ _ (by simp [hi10]),
                  List.getD_eq_getElem _ _ (by simp [hi10]), List.getD_eq_getElem _ _ (by simp [hi10]),
                  List.getElem_ofFn, List.getElem_ofFn]
                simp [xA, xB, hne0]
              · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
            | succ k ih =>
              have hklt : k < gs.length := Nat.lt_of_succ_le hk
              rw [List.take_succ_eq_append_getElem hklt, List.foldl_append, List.foldl_append,
                List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
              set wA := (gs.take k).foldl step (List.ofFn xA ++ [!xA 0])
              set wB := (gs.take k).foldl step (List.ofFn xB ++ [!xB 0])
              have hlwA : wA.length = 11 + k := by simp [wA, wires_len, List.length_take_of_le (Nat.le_of_lt hklt)]
              have hlwB : wB.length = 11 + k := by simp [wB, wires_len, List.length_take_of_le (Nat.le_of_lt hklt)]
              intro i hne0 hne10
              by_cases hilt : i < 11 + k
              · simp only [step]
                rw [List.getD_append _ _ _ _ (by omega : i < wA.length),
                  List.getD_append _ _ _ _ (by omega : i < wB.length)]
                exact ih (Nat.le_of_lt hklt) i hne0 hne10
              · by_cases hieq : i = 11 + k
                · subst hieq
                  have heA : (step wA gs[k]).getD (11 + k) false =
                      gs[k].op.eval (gs[k].inputs.map fun idx => wA.getD idx false) := by
                    simp only [step]; rw [← hlwA, getD_snoc_end]
                  have heB : (step wB gs[k]).getD (11 + k) false =
                      gs[k].op.eval (gs[k].inputs.map fun idx => wB.getD idx false) := by
                    simp only [step]; rw [← hlwB, getD_snoc_end]
                  rw [heA, heB]
                  apply eval_active_congr gs[k] (hfan_gs _ (List.getElem_mem hklt)).1
                  intro idx hidx
                  have hne0' : idx ≠ 0 := by intro h; subst h; exact hex0 ⟨k, hklt⟩ (by simpa using hidx)
                  have hne10' : idx ≠ 10 := by intro h; subst h; exact hno10 ⟨k, hklt⟩ (by simpa using hidx)
                  exact ih (Nat.le_of_lt hklt) idx hne0' hne10'
                · rw [List.getD_eq_default _ _ (by simp [step, hlwA]; omega),
                    List.getD_eq_default _ _ (by simp [step, hlwB]; omega)]
          have hfull := hagree gs.length (le_refl _) out hout_ne0 hout_ne10
          simp only [List.take_length] at hfull
          rw [heval xA, heval xB] at hfull
          revert hfull; decide
        obtain ⟨j1, hj1_reads⟩ := hex10
        have hfl_j1 : res0.2.2.getD j1.val false = true :=
          (elim_of_const_in j1 10 true (by omega) hj1_reads hres0_10).1
        -- Either j1 is the only reader of 10, or there is a second reader j2 ≠ j1 (and no third)!
        have hex_pair : ∃ j2 : Fin gs.length, ∀ j : Fin gs.length, 10 ∈ active (gs.get j) → j = j1 ∨ j = j2 := by
          rcases Classical.em (∃ j2 : Fin gs.length, j2 ≠ j1 ∧ 10 ∈ active (gs.get j2)) with ⟨j2, hj2_ne, hj2_reads⟩ | hex2
          · have hfl_j2 : res0.2.2.getD j2.val false = true :=
              (elim_of_const_in j2 10 true (by omega) hj2_reads hres0_10).1
            refine ⟨j2, fun j hj => ?_⟩
            refine Classical.byContradiction fun hnot => ?_
            push Not at hnot
            obtain ⟨hj_ne1, hj_ne2⟩ := hnot
            have hfl_j : res0.2.2.getD j.val false = true :=
              (elim_of_const_in j 10 true (by omega) hj hres0_10).1
            let fa : Fin res0.2.2.length := ⟨j1.val, by omega⟩
            let fb : Fin res0.2.2.length := ⟨j2.val, by omega⟩
            let fc : Fin res0.2.2.length := ⟨j.val, by omega⟩
            have h3 := count_ge_three res0.2.2 fa fb fc
              (fun h => hj2_ne (Fin.ext (show j2.val = j1.val from (congrArg (fun x : Fin res0.2.2.length => x.val) h).symm)))
              (fun h => hj_ne1 (Fin.ext (show j.val = j1.val from (congrArg (fun x : Fin res0.2.2.length => x.val) h).symm)))
              (fun h => hj_ne2 (Fin.ext (show j.val = j2.val from (congrArg (fun x : Fin res0.2.2.length => x.val) h).symm)))
              hfl_j1 hfl_j2 hfl_j
            omega
          · push Not at hex2
            refine ⟨j1, fun j hj => Or.inl ?_⟩
            refine Classical.byContradiction fun hne => hex2 j hne hj
        obtain ⟨j2, hj12⟩ := hex_pair
        exact h_only10 ⟨gs, out⟩ hfanD hD_size_le18 hDeval hno0_form
          ⟨j1, j2, fun j => ⟨fun hnot h10 => by
              apply hj12 j
              cases hin : (gs.get j).inputs with
              | nil => rw [hin] at h10; cases h10
              | cons a rest =>
                rw [hin] at h10; simp only [List.head?_cons, Option.some.injEq] at h10
                subst h10; rw [active_of_not _ hnot, hin]; simp,
            fun hne h10 => by
              apply hj12 j; rw [active_of_ne_not _ hne]; exact h10⟩⟩
