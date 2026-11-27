import PEqualNP.MetaComplexity.Helpers.ExactCycle4

/-- The edge function of the 4-cycle on four inputs has a fan-in two circuit with `s` gates
exactly when `3 ≤ s`: its circuit size is `3`. -/
theorem PEqualNP.MetaComplexity.L112 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)) s ↔ 3 ≤ s :=
  PEqualNP.MetaComplexity.Helpers.ExactCycle4.size_iff
