import PEqualNP.MetaComplexity.Helpers.LowMergeMain

/-- The low-merge inequality: in a circuit of AND and OR gates of fan-in at most two computing
the edge function of a bipartite incidence (points first, then lines), at every line `w` the
number of low merges at `w` is at least the number of points of `w` minus one. -/
theorem PEqualNP.MetaComplexity.L663 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) → ∀ w : Fin L, (Finset.univ.filter (fun p : Fin P => inc p w = true)).card ≤ ((Finset.range (P + L + C.gates.length)).filter (fun g => PEqualNP.LowMerge.IsLowMerge P L inc C g w)).card + 1 :=
  fun P L inc C hC hfan hcomp w =>
    PEqualNP.MetaComplexity.LowMergeProof.main' P L inc C hC hfan hcomp w
