import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.MetaComplexity.L012

/-- The OR of `n` inputs has a minimal circuit, of `n - 1` gates. -/
theorem PEqualNP.MetaComplexity.L098 : ∀ n : ℕ, ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ C.size = n - 1 ∧ PEqualNP.MetaComplexity.circuitFun n C = fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true) := by
  intro n
  obtain ⟨C, hF, hs, hf⟩ := (PEqualNP.MetaComplexity.L012 n (n - 1)).2 (by omega)
  have hfun : PEqualNP.MetaComplexity.circuitFun n C =
      fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true) := funext hf
  have lo : n ≤ C.size + 1 := (PEqualNP.MetaComplexity.L012 n C.size).1 ⟨C, hF, le_rfl, hf⟩
  refine ⟨C, ⟨hF, fun D hD hD' => ?_⟩, by omega, hfun⟩
  rw [hfun] at hD'
  have := (PEqualNP.MetaComplexity.L012 n D.size).1 ⟨D, hD, le_rfl, fun x => congrFun hD' x⟩
  omega
