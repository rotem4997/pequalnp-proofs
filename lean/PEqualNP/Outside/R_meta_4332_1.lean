import Mathlib
import PEqualNP.Defs

-- Size cut for L-meta-4332. On the inputs with x_9 false the edge function of the Petersen graph
-- is the edge function of the graph without vertex 9. From a circuit of the statement with at most
-- 12 gates, a first gate OR of nothing (the constant false, wire 9) and, for the negated case, a
-- final NOT give a circuit on the nine inputs with at most 14 gates for that function, which the
-- checked bound of L-meta-2012 excludes. What is left is the case of 13 gates and more.
theorem PEqualNP.Outside.R_meta_4332_1
    (hcore : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) → (13 : ℕ) ≤ x2.size →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8)
    (hsmall : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) (14 : ℕ)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8 := by
  dsimp only at hcore ⊢
  intro x2 x3 x4 hf hs
  by_cases h : 13 ≤ x2.size
  · exact hcore x2 x3 x4 hf hs h
  · by_contra hc
    push Not at hc
    apply hsmall
    -- the inputs of the nine-input circuit, extended by x_9 = false
    have hz : ∀ y : Fin 9 → Bool,
        List.ofFn (fun i : Fin 10 => if hi : i.val < 9 then y ⟨i.val, hi⟩ else false) = List.ofFn y ++ [false] := by
      intro y
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]
    have hval : ∀ y : Fin 9 → Bool,
        (if x4 = true then !(x2.wires (List.ofFn y ++ [false])).getD x3 false
          else (x2.wires (List.ofFn y ++ [false])).getD x3 false) = (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ))) := by
      intro y
      have h1 := hc (fun i : Fin 10 => if hi : i.val < 9 then y ⟨i.val, hi⟩ else false) (by simp)
      rw [hz y] at h1
      rw [h1]
      have hy : y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8] := by
        funext i
        fin_cases i <;> rfl
      rw [hy]
      generalize y 0 = b0
      generalize y 1 = b1
      generalize y 2 = b2
      generalize y 3 = b3
      generalize y 4 = b4
      generalize y 5 = b5
      generalize y 6 = b6
      generalize y 7 = b7
      generalize y 8 = b8
      revert b0 b1 b2 b3 b4 b5 b6 b7 b8
      decide
    by_cases hx : x4 = true
    · refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: (x2.gates ++
          [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [x3]⟩]), 10 + x2.gates.length⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨by simp, by simp⟩
        · rcases List.mem_append.mp hg with hg | hg
          · exact hf g hg
          · simp only [List.mem_singleton] at hg
            subst hg
            exact ⟨by simp, by simp⟩
      · show (x2.gates ++ [({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x3] } : PEqualNP.CircuitLowerBounds.Gate)]).length + 1 ≤ 14
        have h' : ¬ 13 ≤ x2.gates.length := h
        rw [List.length_append, List.length_singleton]
        omega
      · intro y
        show _ = (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)))
        rw [← hval y, if_pos hx]
        have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool),
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).length =
              l.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro l; simp
          | cons g gs ih =>
            intro l
            rw [List.foldl_cons, ih]
            simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
            omega
        have hW : (x2.wires (List.ofFn y ++ [false])).length = 10 + x2.gates.length := by
          have := hlen x2.gates (List.ofFn y ++ [false])
          simp only [List.length_append, List.length_ofFn, List.length_singleton] at this
          exact this
        have key : PEqualNP.CircuitLowerBounds.Circuit.eval
            ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: (x2.gates ++
              [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [x3]⟩]), 10 + x2.gates.length⟩ (List.ofFn y) =
            ((x2.wires (List.ofFn y ++ [false])) ++
              [PEqualNP.CircuitLowerBounds.GateOp.not.eval
                ([x3].map fun i => (x2.wires (List.ofFn y ++ [false])).getD i false)]).getD
              (10 + x2.gates.length) false := by
          show (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
              (List.ofFn y ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval []])
              (x2.gates ++ [({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x3] } : PEqualNP.CircuitLowerBounds.Gate)])).getD (10 + x2.gates.length) false = _
          rw [List.foldl_append]
          rfl
        rw [key, List.getD_append_right _ _ _ _ (by omega), hW, Nat.sub_self]
        rfl
    · refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: x2.gates, x3⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨by simp, by simp⟩
        · exact hf g hg
      · show x2.gates.length + 1 ≤ 14
        have h' : ¬ 13 ≤ x2.gates.length := h
        omega
      · intro y
        show _ = (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (0 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)))
        rw [← hval y, if_neg hx]
        rfl
