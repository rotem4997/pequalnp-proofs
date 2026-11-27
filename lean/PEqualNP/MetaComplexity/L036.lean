import PEqualNP.MetaComplexity.Helpers.LocalCoreWf

/-- The core of the local reduction chain, from any well-formed image. A `q`-local map with
`3 q < n` that reduces parity on `n` bits to partial MCSP, with outputs of length at most `M`:
whenever the image of the all-false input is an instance with size bound `s`, that instance is
not a member, and `2 ^ ((n - 3 q) / (4 q))` is at most `8 q (s + 1)` times a bound on the number
of circuits with `s` gates on `log M` inputs. -/
theorem PEqualNP.MetaComplexity.L036 : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (¬ ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) ∧ 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))) ^ s * (Nat.log 2 M + s + 1)))) :=
  PEqualNP.MetaComplexity.Helpers.LocalCoreWf.core_wf
