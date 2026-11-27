import PEqualNP.MetaComplexity.Helpers.LocalFinite

/-- The finite form of the local reduction chain. A `q`-local map that reduces parity on `n`
bits to partial MCSP, with outputs of length at most `M`, and whose table on the all-false
input has a consistent circuit with at most `B` gates, exists only when `2 ^ ((n - 3 q) / (4 q))`
is at most `8 q B` times a bound on the number of circuits with fewer than `B` gates on `log M`
inputs. -/
theorem PEqualNP.MetaComplexity.L032 : ∀ (n q M B : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → (∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f B) → 2 * q * (Nat.log 2 M + 2) < n → 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * (B * (B * ((3 * ((Nat.log 2 M + B + 1) * (Nat.log 2 M + B + 1))) ^ (B - 1) * (Nat.log 2 M + B)))) :=
  PEqualNP.MetaComplexity.Helpers.LocalFinite.finite
