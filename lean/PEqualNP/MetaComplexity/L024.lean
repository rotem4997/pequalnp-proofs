import PEqualNP.MetaComplexity.Helpers.ZeroCompletion

/-- If a language with circuits of polynomial size `p` decides, on inputs `i ++ c` with `i` of
length `n`, whether the partial table `T` reads `some true` at the position coded by `i`, then
the completion of `T` by `false` has a circuit of size at most `p (n + |c|) + 1`. -/
theorem PEqualNP.MetaComplexity.L024 : ∀ (B : Language Bool) (p : Polynomial ℕ) (n : ℕ) (T : List (Option Bool)) (c : List Bool), B ∈ PEqualNP.CircuitLowerBounds.SIZE (fun m : ℕ => p.eval m) → (∀ i : List Bool, i.length = n → (i ++ c ∈ B ↔ T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i) none = some true)) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (T.getD (PEqualNP.MetaComplexity.tableIndex x) none = some true)) (p.eval (n + c.length) + 1) :=
  fun B p n T c hB hT => PEqualNP.MetaComplexity.Helpers.zero_completion B p n T c hB hT
