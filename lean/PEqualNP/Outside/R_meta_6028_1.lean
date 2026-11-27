import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6028_1 :
  (
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (w : Fin 10 → Fin 10),
    PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 17 →
    ∃ x : Fin 10 → Bool,
      c.eval (List.ofFn (x ∘ w) ++ [x 0 && x 2, false])
        ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] :
              List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  ) →
  (
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (w : Fin 10 → Fin 10),
    PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 17 → ∀ i : Fin 11,
    ∃ x : Fin 10 → Bool,
      let inputs := List.ofFn (x ∘ w) ++ [x 0 && x 2]
      c.eval (inputs ++ [inputs.getD i false])
        ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] :
              List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  ) →
  (
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (w : Fin 10 → Fin 10),
    PEqualNP.MetaComplexity.FanInTwo c → c.size ≤ 17 → ∀ i j : Fin 11,
    ∃ x : Fin 10 → Bool,
      let inputs := List.ofFn (x ∘ w) ++ [x 0 && x 2]
      c.eval (inputs ++ [inputs.getD i false || inputs.getD j false])
        ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] :
              List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  ) →
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6) := by
  intro zeroCase oneCase twoCase c w fan small h
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
  have hglen : g.inputs.length ≤ 2 := (fan g (hg ▸ List.mem_cons_self)).2
  have splitEval (xs : List Bool) :
      c.eval xs = tail.eval (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) := by
    delta PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [hg, List.foldl_cons, hop] <;> rfl
  have orEval : ∀ l : List Bool,
      PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id :=
    fun l => rfl
  have target_eq : ∀ y : Fin 10 → Bool,
      (y (0 : Fin 10) && y (1 : Fin 10) || y (1 : Fin 10) && y (2 : Fin 10) ||
        y (2 : Fin 10) && y (3 : Fin 10) || y (3 : Fin 10) && y (4 : Fin 10) ||
        y (4 : Fin 10) && y (0 : Fin 10) || y (0 : Fin 10) && y (5 : Fin 10) ||
        y (1 : Fin 10) && y (6 : Fin 10) || y (2 : Fin 10) && y (7 : Fin 10) ||
        y (3 : Fin 10) && y (8 : Fin 10) || y (4 : Fin 10) && y (9 : Fin 10) ||
        y (5 : Fin 10) && y (7 : Fin 10) || y (7 : Fin 10) && y (9 : Fin 10) ||
        y (9 : Fin 10) && y (6 : Fin 10) || y (6 : Fin 10) && y (8 : Fin 10) ||
        y (8 : Fin 10) && y (5 : Fin 10)) =
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] :
            List (Fin 10 × Fin 10)).any (fun e => y e.1 && y e.2) := by
    intro y
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    ac_rfl
  rcases hreads : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · -- g.inputs = []
    obtain ⟨x, hx⟩ := zeroCase tail w tailFan tailSmall
    refine ⟨x, ?_⟩
    simp only [splitEval, hreads, hop, orEval, id_eq, List.map_nil, List.any_nil, List.append_assoc]
    rw [target_eq]
    exact hx
  · -- g.inputs = [i]
    by_cases hi : i < 11
    · obtain ⟨x, hx⟩ := oneCase tail w tailFan tailSmall ⟨i, hi⟩
      refine ⟨x, ?_⟩
      simp only [splitEval, hreads, hop, orEval, id_eq, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, List.append_assoc]
      rw [target_eq]
      exact hx
    · obtain ⟨x, hx⟩ := zeroCase tail w tailFan tailSmall
      refine ⟨x, ?_⟩
      have hdefault : (List.ofFn (x ∘ w) ++ [x 0 && x 2]).getD i false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
      simp only [splitEval, hreads, hop, orEval, id_eq, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, List.append_assoc, hdefault]
      rw [target_eq]
      exact hx
  · -- g.inputs = [i, j]
    by_cases hi : i < 11 <;> by_cases hj : j < 11
    · obtain ⟨x, hx⟩ := twoCase tail w tailFan tailSmall ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨x, ?_⟩
      simp only [splitEval, hreads, hop, orEval, id_eq, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, List.append_assoc]
      rw [target_eq]
      exact hx
    · obtain ⟨x, hx⟩ := oneCase tail w tailFan tailSmall ⟨i, hi⟩
      refine ⟨x, ?_⟩
      have hdefault : (List.ofFn (x ∘ w) ++ [x 0 && x 2]).getD j false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)
      simp only [splitEval, hreads, hop, orEval, id_eq, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, List.append_assoc, hdefault]
      rw [target_eq]
      exact hx
    · obtain ⟨x, hx⟩ := oneCase tail w tailFan tailSmall ⟨j, hj⟩
      refine ⟨x, ?_⟩
      have hdefault : (List.ofFn (x ∘ w) ++ [x 0 && x 2]).getD i false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
      simp only [splitEval, hreads, hop, orEval, id_eq, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, Bool.false_or, List.append_assoc, hdefault]
      rw [target_eq]
      exact hx
    · obtain ⟨x, hx⟩ := zeroCase tail w tailFan tailSmall
      refine ⟨x, ?_⟩
      have hdefaulti : (List.ofFn (x ∘ w) ++ [x 0 && x 2]).getD i false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
      have hdefaultj : (List.ofFn (x ∘ w) ++ [x 0 && x 2]).getD j false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)
      simp only [splitEval, hreads, hop, orEval, id_eq, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, List.append_assoc, hdefaulti, hdefaultj]
      rw [target_eq]
      exact hx
  · -- g.inputs has at least 3 entries, contradicting FanInTwo
    exfalso
    rw [hreads] at hglen
    simp only [List.length_cons] at hglen
    omega
