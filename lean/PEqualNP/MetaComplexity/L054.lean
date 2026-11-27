import PEqualNP.MetaComplexity.Helpers.ExpReduce

/-- The exponential-size reduction from hitting set to partial MCSP, with the table explicit. -/
theorem PEqualNP.MetaComplexity.L054 : ∀ (n : ℕ) (F : Finset (Finset (Fin n))) (k : ℕ), (if ∅ ∈ F ∨ (k = 0 ∧ F ≠ ∅) then false :: PEqualNP.MetaComplexity.encodePartial (some true :: List.replicate (2 ^ n - 1) none) else List.replicate (k - 1) true ++ false :: PEqualNP.MetaComplexity.encodePartial ((List.range (2 ^ n)).map fun j : ℕ => if j = 0 then some false else if (Finset.univ.filter fun i : Fin n => Nat.testBit j (i : ℕ) = true) ∈ F then some true else none)) ∈ PEqualNP.MetaComplexity.PartialMCSP ↔ ∃ H : Finset (Fin n), (∀ S ∈ F, (H ∩ S).Nonempty) ∧ H.card ≤ k :=
  PEqualNP.MetaComplexity.Helpers.ExpReduce.S1_total
