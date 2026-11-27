import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5018_75 (localCase :
    ∀ (n : Nat) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n),
    v ∉ A → 1 < (G.neighborSet v).ncard →
    (∀ i j, G.Adj i j → i ∉ A) →
    (∀ i (c : G.Walk i i), c.IsCycle → 7 ≤ c.length) →
    (∀ x, f x = true ↔ (∃ i ∈ A, x i = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
    (C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length = 1 →
    ∀ g ∈ C.gates, ∀ y : Fin n, y ≠ v → (g.inputs = [v.val,y.val] ∨ g.inputs = [y.val,v.val]) →
      g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → y ∈ A)) (residual :
  ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) → (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) → (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) → PEqualNP.MetaComplexity.FanInTwo x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 → (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) → (∃ x16 ∉ x4, (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x16) x6.gates).length = (1 : ℕ) ∧ ∀ g ∈ x6.gates, ∀ y : Fin x1, y ≠ x16 → (g.inputs = [x16.val,y.val] ∨ g.inputs = [y.val,x16.val]) → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → y ∈ x4)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ)) :
  ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) → (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) → (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) → PEqualNP.MetaComplexity.FanInTwo x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 → (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) → (∃ x16 ∉ x4, (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x16) x6.gates).length = (1 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  intro n k G A f C deg girth isolated edge cover spec fan comp least one
  apply residual n k G A f C deg girth isolated edge cover spec fan comp least
  obtain ⟨v,hv,count⟩ := one
  exact ⟨v,hv,count,localCase n G A f C v hv (by rw [deg v hv]; decide) isolated girth spec fan comp count⟩
