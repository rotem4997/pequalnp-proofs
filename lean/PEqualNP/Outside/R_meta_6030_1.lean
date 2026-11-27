import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6030_1 :
  (
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (w : Fin 10 → Fin 10),
    PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 17 →
    ∃ x : Fin 10 → Bool,
      c.eval (List.ofFn (x ∘ w) ++ [x 0 && x 2, true])
        ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] :
              List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  ) →
  (
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (w : Fin 10 → Fin 10),
    PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 17 → ∀ i : Fin 11,
    ∃ x : Fin 10 → Bool,
      let inputs := List.ofFn (x ∘ w) ++ [x 0 && x 2]
      c.eval (inputs ++ [!(inputs.getD i false)])
        ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] :
              List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  ) →
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6) := by
  intro constCase inputCase c w fan small h
  obtain ⟨g, gs, hg, hop⟩ := h
  let tail : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, c.output⟩
  have tailFan : PEqualNP.MetaComplexity.FanInTwo tail := by
    intro k hk
    apply fan k
    rw [hg]
    exact List.mem_cons_of_mem g hk
  have tailSmall : tail.size ≤ 17 := by
    change c.gates.length ≤ 18 at small
    rw [hg, List.length_cons] at small
    change gs.length ≤ 17
    omega
  have splitEval (xs : List Bool) :
      c.eval xs = tail.eval (xs ++ [!((g.inputs.map fun i => xs.getD i false).headD false)]) := by
    delta PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [hg, List.foldl_cons, hop] <;> rfl
  cases hreads : g.inputs with
  | nil =>
    obtain ⟨x, hx⟩ := constCase tail w tailFan tailSmall
    refine ⟨x, ?_⟩
    simpa [splitEval, hreads, List.any_cons, Bool.or_assoc, List.append_assoc] using hx
  | cons i is =>
    by_cases hi : i < 11
    · obtain ⟨x, hx⟩ := inputCase tail w tailFan tailSmall ⟨i, hi⟩
      refine ⟨x, ?_⟩
      simpa [splitEval, hreads, List.any_cons, Bool.or_assoc] using hx
    · obtain ⟨x, hx⟩ := constCase tail w tailFan tailSmall
      refine ⟨x, ?_⟩
      have hdefault :
          (List.ofFn (x ∘ w) ++ [x 0 && x 2]).getD i false = false := by
        apply List.getD_eq_default
        simpa using Nat.le_of_not_gt hi
      rw [splitEval, hreads]
      simp only [List.map_cons, List.headD_cons, hdefault]
      simpa [List.any_cons, Bool.or_assoc, List.append_assoc] using hx
