import PEqualNP.Defs

/-- The zero completion: if the function that is `true` exactly on the entries of the partial
table `T` defined as `true` has a circuit of size `s`, then `T` with bound `s` is a member of
partial MCSP. -/
theorem PEqualNP.MetaComplexity.L017 : ∀ (n s : ℕ) (T : List (Option Bool)), T.length = 2 ^ n →
    PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x : Fin n → Bool =>
        decide (T.getD (PEqualNP.MetaComplexity.tableIndex x) none = some true)) s →
    (List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T)
      ∈ PEqualNP.MetaComplexity.PartialMCSP := by
  intro n s T hlen h
  refine ⟨n, s, T, rfl, hlen, _, ?_, h⟩
  intro x b hb
  show decide (T.getD (PEqualNP.MetaComplexity.tableIndex x) none = some true) = b
  rw [hb]
  cases b <;> simp
