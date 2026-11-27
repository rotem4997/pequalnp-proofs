import PEqualNP.MetaComplexity.Helpers.OneNotPiece

theorem PEqualNP.MetaComplexity.L677 : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ) (o : ℕ) (x : Fin n → Bool), (((ins).map (fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false)).headD false) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } : PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) :=
  PEqualNP.MetaComplexity.OneNot.on1_piece_d
