import PEqualNP.MetaComplexity.Helpers.LocalPrivate2

/-- Private witnesses for 1-local reductions whose format may vary with the input. -/
theorem PEqualNP.MetaComplexity.L046 : ∀ (n : ℕ) (w : (Fin n → Bool) → List Bool) (s n' : (Fin n → Bool) → ℕ) (T : (Fin n → Bool) → List (Option Bool)), PEqualNP.MetaComplexity.QueryLocal n 1 w → (∀ x : Fin n → Bool, w x = List.replicate (s x) true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n' x) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → ∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 → ∃ f : (Fin (n' x) → Bool) → Bool, PEqualNP.MetaComplexity.Consistent (n' x) (T x) f ∧ PEqualNP.MetaComplexity.HasCircuitSize (n' x) f (s x) ∧ ∀ y : Fin n → Bool, s y = s x → n' y = n' x → PEqualNP.MetaComplexity.Consistent (n' x) (T y) f → y = x :=
  PEqualNP.MetaComplexity.Helpers.LocalPrivate2.private_var
