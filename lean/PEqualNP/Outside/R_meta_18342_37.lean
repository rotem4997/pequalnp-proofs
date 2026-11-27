import PEqualNP.Defs

-- A case split on the output wire of the circuit. Either the output is one of the 10 input
-- wires (the circuit returns one input bit), or it is a later wire, produced by a gate or
-- past the end of the circuit. Each case is the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_18342_37
    (outIn : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (10 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (10 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (10 : ℕ) (x6 % (10 : ℕ))))
    (outGate : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (10 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (10 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (10 : ℕ) (x6 % (10 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (10 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (10 : ℕ) (x6 % (10 : ℕ))) := by
  intro x1
  rcases Nat.lt_or_ge x1.output (10 : ℕ) with h | h
  · exact outIn x1 h
  · exact outGate x1 h
