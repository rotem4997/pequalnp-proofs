import PEqualNP.MetaComplexity.Helpers.EdgeUpper

/-- If a graph on `n` vertices has an edge and `T` is a vertex cover of it, the function that is
true when some edge has both endpoints true has a circuit with (edges) + `|T|` - 1 gates. -/
theorem PEqualNP.MetaComplexity.L105 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) :=
  PEqualNP.MetaComplexity.Helpers.EdgeUpper.edge_upper
