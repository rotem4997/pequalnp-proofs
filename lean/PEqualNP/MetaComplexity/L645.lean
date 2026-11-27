import PEqualNP.MetaComplexity.Helpers.HonestFactor

/-- Honest factor: if a point-only monotone function AND a list of monotone functions is true only
at inputs where an incident point and line are both on, and is true at the input with exactly point
`p` and line `w` on, then the list is nonempty and some member is false at `p` alone and true at `p`
plus a line `u` only when `I p u`. -/
theorem PEqualNP.MetaComplexity.L645 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (Λ : (Fin (N + N) → Bool) → Bool) (r : List ((Fin (N + N) → Bool) → Bool)) (p w : Fin N), Monotone Λ → (∀ z z' : Fin (N + N) → Bool, (∀ i : Fin N, z (Fin.castAdd N i) = z' (Fin.castAdd N i)) → Λ z = Λ z') → (∀ f ∈ r, Monotone f) → (∀ z : Fin (N + N) → Bool, (Λ z && r.all (fun f => f z)) = true → ∃ a b : Fin N, I a b ∧ z (Fin.castAdd N a) = true ∧ z (Fin.natAdd N b) = true) → (Λ (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)) && r.all (fun f => f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)))) = true → r ≠ [] ∧ ∃ f ∈ r, f (fun k => decide (k = Fin.castAdd N p)) = false ∧ ∀ u : Fin N, f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N u)) = true → I p u :=
  PEqualNP.MetaComplexity.HonestFactor.main
