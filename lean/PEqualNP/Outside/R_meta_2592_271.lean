import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2592_271
    (binaryFloor :
      let f := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x) →
        15 + notCount C ≤ C.size)
    (fewNot :
      let f := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → C.size ≤ 19 → 1 ≤ notCount C → notCount C ≤ 4 →
        ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C fan size hasNot correct
  have minSize := binaryFloor C fan correct
  obtain ⟨g,mem,op⟩ := hasNot
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have survives : g ∈ C.gates.filter (fun h : Gate => decide (h.op = GateOp.not)) :=
    List.mem_filter.mpr ⟨mem,decide_eq_true op⟩
  have pos : 1 ≤ notCount C := by
    by_contra! h
    have zero : notCount C = 0 := by omega
    have empty := List.length_eq_zero_iff.mp zero
    rw [empty] at survives
    cases survives
  exact fewNot C fan size pos (by omega) correct
