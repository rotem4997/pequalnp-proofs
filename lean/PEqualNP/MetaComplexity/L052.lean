import PEqualNP.MetaComplexity.Helpers.LocalHard

/-- A local reduction of parity outputs a table of large partial circuit size at every even input. -/
theorem PEqualNP.MetaComplexity.L052 : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ z : Fin n → Bool, (Finset.univ.filter fun i : Fin n => z i = true).card % 2 = 0 → ∀ (n' s : ℕ) (T : List (Option Bool)), w z = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (¬ ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) ∧ (n - 3 * q) / (4 * q) < (2 * s + 3) * (Nat.log 2 M + 3) + Nat.log 2 q :=
  PEqualNP.MetaComplexity.Helpers.LocalHard.size_bound_even
