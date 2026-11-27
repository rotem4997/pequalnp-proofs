import PEqualNP.MetaComplexity.Helpers.TotalLocal

/-- The core of the local obstruction for total MCSP, from any well-formed image of the
all-false input: the analogue of `L-meta-036` for total tables. -/
theorem PEqualNP.MetaComplexity.L040 : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.MCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List Bool), w (fun _ : Fin n => false) = List.replicate s true ++ false :: T → T.length = 2 ^ n' → (¬ PEqualNP.MetaComplexity.HasCircuitSize n' (PEqualNP.MetaComplexity.tableFun n' T) s) ∧ 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))) ^ s * (Nat.log 2 M + s + 1)))) :=
  PEqualNP.MetaComplexity.Helpers.TotalLocal.core
