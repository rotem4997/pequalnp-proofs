import PEqualNP.MetaComplexity.Helpers.ExactMaj3

/-- Majority of three inputs has a circuit of AND, OR and NOT gates of fan-in two with `s`
gates exactly when `4 ≤ s`. -/
theorem PEqualNP.MetaComplexity.L100 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) s ↔ 4 ≤ s :=
  PEqualNP.MetaComplexity.Helpers.ExactMaj3.maj3_size
