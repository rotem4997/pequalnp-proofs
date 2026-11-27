import PEqualNP.MetaComplexity.Helpers.LocalPrivate2

/-- The locality 2 form of the private witness lemma is false. -/
theorem PEqualNP.MetaComplexity.L045 : ¬ ∀ (n n' s : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), PEqualNP.MetaComplexity.QueryLocal n 2 w → (∀ x : Fin n → Bool, w x = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n') → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → ∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 → ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' (T x) f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s ∧ ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.Consistent n' (T y) f → y = x :=
  PEqualNP.MetaComplexity.Helpers.LocalPrivate2.not_private_two
