import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2541_73
    (normal : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool)
        (f : (Fin 9 → Bool) → Bool),
      PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 14 →
      (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
      (∀ x : Fin 9 → Bool,
        PEqualNP.MetaComplexity.circuitFun 9 C (fun i => if i = 0 then b != x 0 else x i) = f x) →
      (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size ≤ 14 ∧
        ∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 D x = f x) ∨
      (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (j w : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size ≤ 14 ∧
        (D.gates.filter (fun g => g.inputs.contains 0)).length = 1 ∧
        j < D.gates.length ∧
        0 < w ∧ w < 9 + j ∧
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [0, w] ∧
        ∀ x : Fin 9 → Bool,
          PEqualNP.MetaComplexity.circuitFun 9 D (fun i => if i = 0 then !x 0 else x i) = f x))
    (unnegated : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 14 →
      ∃ x : Fin 9 → Bool,
        PEqualNP.MetaComplexity.circuitFun 9 D x ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
           x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (binReader : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j w : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 14 →
      (D.gates.filter (fun g => g.inputs.contains 0)).length = 1 →
      j < D.gates.length →
      0 < w → w < 9 + j →
      ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs = [0, w] →
      ∃ x : Fin 9 → Bool,
        PEqualNP.MetaComplexity.circuitFun 9 D (fun i => if i = 0 then !x 0 else x i) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
           x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then x2 != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C b hFan hSize hFlt
  by_contra hAll
  have hEq : ∀ x : Fin 9 → Bool,
      PEqualNP.MetaComplexity.circuitFun 9 C (fun i => if i = 0 then b != x 0 else x i) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
         x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hNe
    exact hAll ⟨x, hNe⟩
  rcases normal C b _ hFan hSize hFlt hEq with ⟨D, hDFan, hDSize, hDEq⟩ |
      ⟨D, j, w, hDFan, hDSize, hDFlt, hj, hw0, hwlt, hOp, hIn, hDEq⟩
  · obtain ⟨x, hx⟩ := unnegated D hDFan hDSize
    exact hx (hDEq x)
  · obtain ⟨x, hx⟩ := binReader D j w hDFan hDSize hDFlt hj hw0 hwlt hOp hIn
    exact hx (hDEq x)
