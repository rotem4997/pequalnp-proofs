import PEqualNP.MetaComplexity.Helpers.LocalPrivate2

/-- The explicit count behind private witnesses. -/
theorem PEqualNP.MetaComplexity.L044 : ∀ (n n' s : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), 0 < n → PEqualNP.MetaComplexity.QueryLocal n 1 w → (∀ x : Fin n → Bool, w x = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n') → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 2 ^ (n - 1) ≤ (s + 1) * ((3 * ((n' + s + 2) * (n' + s + 2))) ^ s * (n' + s + 1)) :=
  PEqualNP.MetaComplexity.Helpers.LocalPrivate2.count_explicit
