import PEqualNP.MetaComplexity.Helpers.LocFinal

/-- Let `G` be a graph in which every cycle has length at least 9 and any two distinct vertices
of degree at least 3 are joined only by walks of length at least 7. Every circuit of AND and OR
gates of fan-in at most two, with no NOT gate, computing "both ends of some edge are true" has
at least `|E| + |T| - 1` gates for some vertex cover `T` of `G`. -/
theorem PEqualNP.MetaComplexity.L115 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) → (∀ (u v : Fin n), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v, 7 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ G.edgeFinset.card + T.card ≤ D.size + 1 :=
  PEqualNP.MetaComplexity.Loc.Final.row
