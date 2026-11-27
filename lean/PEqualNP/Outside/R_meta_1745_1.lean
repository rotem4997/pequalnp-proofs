import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1745_1 :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = 3) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → 7 ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo x5 →
      PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
      (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →
      (∀ x14 ∉ x3,
        have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then 1 else 2) x16.inputs).contains ↑x14) x5.gates;
        x16.length ≤ 3 ∧ (x16.length = 3 → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∃ v ∉ x3, (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length ≤ 1) →
      ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + 4 ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = 3) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → 7 ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo x5 →
      PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
      (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →
      (∀ x14 ∉ x3,
        have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then 1 else 2) x16.inputs).contains ↑x14) x5.gates;
        2 ≤ x16.length ∧ x16.length ≤ 3 ∧ (x16.length = 3 → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∃ v ∉ x3, (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length = 2) →
      ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + 4 ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = 3) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → 7 ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo x5 →
      PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
      (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →
      (∀ x14 ∉ x3,
        have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then 1 else 2) x16.inputs).contains ↑x14) x5.gates;
        x16.length = 3 ∧ ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + 4 ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  intro h1 h2 h3 x1 x2 x3 x4 x5 hDeg hGirth hDisj hEdge hF hFan hFun hMin hRead
  rcases Classical.em (∃ v ∉ x3, (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length ≤ 1) with hLe1 | hNotLe1
  · exact h1 x1 x2 x3 x4 x5 hDeg hGirth hDisj hEdge hF hFan hFun hMin hRead hLe1
  · have hGe2 : ∀ v ∉ x3, 2 ≤ (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length := by
      intro v hv
      rcases Nat.lt_or_ge 1 (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length with hGt | hLe
      · exact hGt
      · exact False.elim (hNotLe1 ⟨v, hv, hLe⟩)
    rcases Classical.em (∃ v ∉ x3, (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length = 2) with hEq2 | hNotEq2
    · exact h2 x1 x2 x3 x4 x5 hDeg hGirth hDisj hEdge hF hFan hFun hMin
        (fun v hv => ⟨hGe2 v hv, (hRead v hv).1, (hRead v hv).2⟩) hEq2
    · refine h3 x1 x2 x3 x4 x5 hDeg hGirth hDisj hEdge hF hFan hFun hMin ?_
      intro v hv
      have h3v : (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs).contains ↑v) x5.gates).length = 3 := by
        rcases Nat.eq_or_lt_of_le (hRead v hv).1 with hEq | hLt
        · exact hEq
        · exact False.elim (hNotEq2 ⟨v, hv, Nat.le_antisymm (Nat.le_of_lt_succ hLt) (hGe2 v hv)⟩)
      exact ⟨h3v, (hRead v hv).2 h3v⟩
