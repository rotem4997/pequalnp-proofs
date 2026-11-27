import PEqualNP.MetaComplexity.Helpers.CoverCircB2

/-- With all owners and listed wires among the inputs, the root cover circuit is true exactly when some owner is true together with one of the inputs on its list. -/
theorem PEqualNP.MetaComplexity.L398 : ∀ (n : ℕ) (own : List (ℕ × List ℕ)), (∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) → ∀ x : Fin n → Bool, ((PEqualNP.MetaComplexity.coverCircuitB n own).eval (List.ofFn x) = true ↔ ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧ ∃ w ∈ p.2, (List.ofFn x).getD w false = true) :=
  fun n own h x => PEqualNP.MetaComplexity.Helpers.CoverCircB.circuit_fun n own h x
