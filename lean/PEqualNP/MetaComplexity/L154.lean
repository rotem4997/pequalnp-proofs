import PEqualNP.MetaComplexity.Helpers.EdgeUpperMono

/-- If a graph on `n` vertices has an edge and `T` is a vertex cover of it, the function that is
true when some edge has both endpoints true has a fan-in-two circuit with no NOT gate and at
most (edges) + `|T|` - 1 gates. -/
theorem PEqualNP.MetaComplexity.L154 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ D.size + 1 ≤ G.edgeFinset.card + T.card :=
  PEqualNP.MetaComplexity.Helpers.EdgeUpperMono.edge_upper_mono
