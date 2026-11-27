import Mathlib
import PEqualNP.Defs

-- Gate elimination for the Petersen edge function after a free first gate x0 AND x1 or x0 OR x1.
-- The free gate is prepended as a real gate, giving a circuit of at most 19 gates on ten inputs.
-- hElim: fixing input v to false removes every gate that reads v (the checked L_meta_5148).
-- hSmall: the function with one vertex fixed to false has no circuit with at most 15 gates
--   (the checked L_meta_5150).
-- An input read by four or more gates therefore leaves at most 15 gates for that function.
-- hRest: the step for circuits in which every input is read by at most three gates
--   (the free first gate counted as a reader of x0 and x1).
theorem PEqualNP.Outside.R_meta_4936_509
    (hElim : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (S : Finset ℕ),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ j ∈ S, ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? = some (v : ℕ))) →
      (∃ c : Bool, ∀ x : Fin n → Bool, x v = false → C.eval (List.ofFn x) = c) ∨
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size + S.card ≤ C.size ∧
        ∀ x : Fin n → Bool, x v = false → C'.eval (List.ofFn x) = C.eval (List.ofFn x))
    (hSmall : ∀ (v : Fin 10) (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
      PEqualNP.MetaComplexity.FanInTwo C → C.size + (if b = true then 1 else 0) ≤ 15 →
      ∃ x : Fin 10 → Bool, x v = false ∧
        (if b = true then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hRest : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → (∀ (v : Fin 10) (S : Finset ℕ), (∀ j ∈ S, ∃ g : PEqualNP.CircuitLowerBounds.Gate, (({ op := if x2 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] } : PEqualNP.CircuitLowerBounds.Gate) :: x1.gates)[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? = some (v : ℕ))) → S.card ≤ 3) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  intro C b hfan hsize hout hwires
  let pre : PEqualNP.CircuitLowerBounds.Gate :=
    { op := if b = true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or,
      inputs := [0, 1] }
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre :: C.gates, C.output⟩
  have hD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · refine ⟨?_, by simp [pre]⟩
      cases b <;> simp [pre]
    · exact hfan g hg
  have hDsize : D.size ≤ 19 := by
    have h18 : C.gates.length ≤ 18 := hsize
    show (pre :: C.gates).length ≤ 19
    simp only [List.length_cons]
    omega
  have hDeval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) =
      C.eval (List.ofFn x ++ [if b = true then x 0 && x 1 else x 0 || x 1]) := by
    intro x
    have h0 : (List.ofFn x).getD 0 false = x 0 := by simp
    have h1 : (List.ofFn x).getD 1 false = x 1 := by simp
    have hpre : pre.op.eval (pre.inputs.map fun i => (List.ofFn x).getD i false) =
        (if b = true then x 0 && x 1 else x 0 || x 1) := by
      cases b
      · show PEqualNP.CircuitLowerBounds.GateOp.or.eval
            [(List.ofFn x).getD 0 false, (List.ofFn x).getD 1 false] = (x 0 || x 1)
        rw [h0, h1]
        cases x 0 <;> cases x 1 <;> rfl
      · show PEqualNP.CircuitLowerBounds.GateOp.and.eval
            [(List.ofFn x).getD 0 false, (List.ofFn x).getD 1 false] = (x 0 && x 1)
        rw [h0, h1]
        cases x 0 <;> cases x 1 <;> rfl
    show (D.gates.foldl _ (List.ofFn x)).getD D.output false =
      (C.gates.foldl _ (List.ofFn x ++ [if b = true then x 0 && x 1 else x 0 || x 1])).getD C.output false
    show ((pre :: C.gates).foldl _ (List.ofFn x)).getD C.output false = _
    rw [List.foldl_cons, hpre]
  have key : ∀ v : Fin 10, (fun x : Fin 10 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) (fun i => decide (i ≠ v)) = true := by
    decide
  by_cases hbig : ∃ (v : Fin 10) (S : Finset ℕ),
      (∀ j ∈ S, ∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[j]? = some g ∧ (v : ℕ) ∈ g.inputs ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? = some (v : ℕ))) ∧
      3 < S.card
  · obtain ⟨v, S, hS, hcard⟩ := hbig
    rcases hElim 10 D v S hD hS with ⟨c, hc⟩ | ⟨D', hD', hsz, hagree⟩
    · cases c
      · refine ⟨fun i => decide (i ≠ v), ?_⟩
        rw [← hDeval, hc _ (by simp)]
        have := key v
        simp only at this ⊢
        rw [this]
        decide
      · refine ⟨fun _ => false, ?_⟩
        rw [← hDeval, hc _ rfl]
        decide
    · have hsz' : D'.size + (if false = true then 1 else 0) ≤ 15 := by
        simp only [Bool.false_eq_true, ite_false]
        omega
      obtain ⟨x, hxv, hne⟩ := hSmall v D' false hD' hsz'
      refine ⟨x, ?_⟩
      rw [← hDeval x, ← hagree x hxv]
      simpa using hne
  · apply hRest C b hfan hsize hout hwires
    intro v S hS
    by_contra hlt
    exact hbig ⟨v, S, hS, by omega⟩
