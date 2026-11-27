import PEqualNP.MetaComplexity.Helpers.OneNotPiece

theorem PEqualNP.MetaComplexity.L675 : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ), (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → (((ins).map (fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false)).headD false) = true → (((ins).map (fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩ (List.ofFn y)).getD i false)).headD false) = true :=
  PEqualNP.MetaComplexity.OneNot.on1_piece_h
