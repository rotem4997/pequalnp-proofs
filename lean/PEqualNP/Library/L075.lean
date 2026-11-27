import PEqualNP.Library.L074

/-- The same proposition as L-lib-074 (seat-barrier-1), recorded twice. -/
theorem PEqualNP.Library.L075 : (∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3)) → ((∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ PEqualNP.Library.P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ 2 ^ (n / k) → |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) - (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) → ¬ ∃ Q : Language Bool, PEqualNP.MetaComplexity.Large Q ∧ Q ∈ PEqualNP.Library.P ∧ ∀ k : ℕ, PEqualNP.MetaComplexity.UsefulAgainst Q (fun n : ℕ => n ^ k + k)) :=
  PEqualNP.Library.L074
