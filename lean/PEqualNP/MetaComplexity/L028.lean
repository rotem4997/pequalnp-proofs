import PEqualNP.MetaComplexity.Helpers.Coding

/-- Parity on `m ≥ 1` bits is not a union of fewer than `2 ^ (m / (2 k)) / (4 k)` sets each of
whose non-members is excluded by a subcube fixing at most `k` coordinates (an OR of CNFs of
width `k`). -/
theorem PEqualNP.MetaComplexity.L028 : ∀ (m k N : ℕ) (E : Fin N → Finset (Fin m → Bool)), 0 < k → 0 < m → (∀ (a : Fin N) (x : Fin m → Bool), x ∉ E a → ∃ V : Finset (Fin m), V.card ≤ k ∧ ∀ y : Fin m → Bool, (∀ i ∈ V, y i = x i) → y ∉ E a) → (∀ x : Fin m → Bool, (∃ a : Fin N, x ∈ E a) ↔ (Finset.univ.filter fun i : Fin m => x i = true).card % 2 = 1) → 2 ^ m ≤ N * (4 * k * 2 ^ (m - m / (2 * k))) :=
  PEqualNP.MetaComplexity.Helpers.Coding.parity_cover
