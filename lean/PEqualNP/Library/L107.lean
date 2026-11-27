import PEqualNP.Library.L105
import PEqualNP.Library.L106

/-- Cutting planes refutations of bit pigeonhole are superpolynomial in lines (Beame and
Whitmeyer, ICALP 2025, Theorem 1.5): the triangle dag bound L-lib-105 through the simulation
L-lib-106. -/
theorem PEqualNP.Library.L107 : ∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.Search.CPLine (Fin (2 ^ l + 1) × Fin l)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → p.eval (2 ^ l) < π.length := by
  intro p
  obtain ⟨l, hl⟩ := PEqualNP.Library.L105 p
  refine ⟨l, fun π hπ => ?_⟩
  obtain ⟨ρ, hρ, hlen⟩ := PEqualNP.Library.L106 _ (fun v : Fin (2 ^ l + 1) × Fin l => decide (2 * v.2.val < l)) _ π hπ
  exact lt_of_lt_of_le (hl ρ hρ) hlen
