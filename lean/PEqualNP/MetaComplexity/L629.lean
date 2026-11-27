import PEqualNP.MetaComplexity.Helpers.LineDegTest

/-- The test lemma for line-degree: an AND/OR circuit of line-degree at most `D`, for a graph whose
edges join a marked and an unmarked input, true on every edge and false on every input made of at
most `D` lines and all points adjacent to none of them, computes the edge function. -/
theorem PEqualNP.MetaComplexity.L629 : ∀ (n D : ℕ) (marked : Finset ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin n, G.Adj i j → (i.val ∈ marked ↔ j.val ∉ marked)) → PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C D → (∀ i j : Fin n, G.Adj i j → C.eval (List.ofFn fun k => decide (k = i ∨ k = j)) = true) → (∀ S : Finset (Fin n), (∀ j ∈ S, j.val ∈ marked) → S.card ≤ D → C.eval (List.ofFn fun k => decide (k ∈ S ∨ (k.val ∉ marked ∧ ∀ j ∈ S, ¬ G.Adj k j))) = false) → ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true :=
  PEqualNP.MetaComplexity.LineDegTest.main
