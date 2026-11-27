import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4075_473
    (binary : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun 10 C = (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) → 15 ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (_ : ℕ) => Bool.true) Bool.true g.op) C.gates)
    (few : ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (_ : ℕ) => Bool.false) Bool.false g.op) x2.gates ≤ 4 →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  classical
  intro adjacent D u v fan small f w ha hb cover
  let neg : Gate → Bool := fun g => GateOp.rec false false true (fun _ => false) false g.op
  let pos : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  by_cases hn : D.gates.countP neg ≤ 4
  · exact few adjacent D u v fan small hn ha hb cover
  · by_contra noBad
    let first : Gate := ⟨.and,[0,if adjacent then 1 else 2]⟩
    let last : Gate := ⟨.and,[u,v]⟩
    let C : Circuit := ⟨first :: (D.gates ++ [last]),11+D.gates.length⟩
    let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    let seed (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && (if adjacent then x 1 else x 2)]
    have seedStep (x : Fin 10 → Bool) : step (List.ofFn x) first = seed x := by
      cases adjacent with
      | false =>
        change List.ofFn x ++ [x 0 && (x 2 && true)] = List.ofFn x ++ [x 0 && x 2]
        rw [Bool.and_true]
      | true =>
        change List.ofFn x ++ [x 0 && (x 1 && true)] = List.ofFn x ++ [x 0 && x 1]
        rw [Bool.and_true]
    have runLen (gs : List Gate) (ws : List Bool) :
        (gs.foldl step ws).length = ws.length + gs.length := by
      induction gs generalizing ws with
      | nil => simp
      | cons g gs ih =>
        change (gs.foldl step (step ws g)).length = ws.length + (gs.length+1)
        rw [ih]
        simp only [step,List.length_append,List.length_singleton]
        omega
    have evaluates (x : Fin 10 → Bool) : C.eval (List.ofFn x) = (w x u && w x v) := by
      change (((first :: (D.gates ++ [last])).foldl step (List.ofFn x)).getD (11+D.gates.length) false) = _
      simp only [List.foldl_cons,List.foldl_append,List.foldl_nil]
      rw [seedStep]
      have hl : (D.gates.foldl step (seed x)).length = 11+D.gates.length := by
        rw [runLen]
        simp [seed]
      change (D.gates.foldl step (seed x) ++
        [GateOp.and.eval ([u,v].map fun i => (D.gates.foldl step (seed x)).getD i false)]).getD
          (11+D.gates.length) false = _
      rw [← hl]
      simp only [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero]
      change ((D.gates.foldl step (seed x)).getD u false &&
        ((D.gates.foldl step (seed x)).getD v false && true)) = (w x u && w x v)
      rw [Bool.and_true]
      rfl
    have fanC : FanInTwo C := by
      intro g hg
      change g ∈ first :: (D.gates ++ [last]) at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [first]
      rcases List.mem_append.mp hg with hg | hg
      · exact fan _ hg
      · have : g = last := by simpa using hg
        subst g
        simp [last]
    have computes : circuitFun 10 C = f := by
      funext x
      change C.eval (List.ofFn x) = f x
      rw [evaluates]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true]
      constructor
      · rintro ⟨hu,hv⟩
        by_contra hf
        have asFalse : ∀ b : Bool, b ≠ true → b = false := by decide
        have hf' : f x = false := asFalse _ hf
        exact noBad ⟨x,hf',hu,hv⟩
      · exact cover x
    have lower := binary C fanC computes
    have total (gs : List Gate) : gs.countP pos + gs.countP neg = gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        dsimp only [pos,neg] at ih
        cases hop : g.op <;> simp [pos,neg,List.countP_cons,hop] <;> omega
    have countC : C.gates.countP pos = D.gates.countP pos + 2 := by
      simp [C,first,last,List.countP_cons,List.countP_append,pos,Nat.add_comm] <;> omega
    change 15 ≤ C.gates.countP pos at lower
    rw [countC] at lower
    have ht := total D.gates
    change D.gates.length ≤ 17 at small
    omega
