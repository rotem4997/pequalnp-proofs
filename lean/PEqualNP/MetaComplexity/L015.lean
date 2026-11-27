import PEqualNP.MetaComplexity.Helpers.HittingSet

/-- A function that is false on the all-false input and true on the indicator of every set of
the family `F` has a fan-in two circuit with `s` gates exactly when `F` has a hitting set of
size at most `s + 1`. -/
theorem PEqualNP.MetaComplexity.L015 : ∀ (n : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ), (∃ f : (Fin n → Bool) → Bool, f (fun _ : Fin n => false) = false ∧ (∀ S ∈ F, f (fun i : Fin n => decide (i ∈ S)) = true) ∧ PEqualNP.MetaComplexity.HasCircuitSize n f s) ↔ (∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ s + 1) :=
  PEqualNP.MetaComplexity.Helpers.hitting_iff
