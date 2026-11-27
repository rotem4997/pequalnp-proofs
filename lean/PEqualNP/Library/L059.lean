import PEqualNP.Defs
import PEqualNP.Library.Helpers.BGSDiagonal

/-- Baker-Gill-Solovay, combinatorial form: if the oracle polynomial-time languages are covered
by deciders that each depend on the oracle through polynomially many strings, then some oracle
`B` puts the length test of `B` outside `P^B`. -/
theorem PEqualNP.Library.L059 : (∃ (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ), (∀ (A L : Language Bool), L ∈ PEqualNP.Library.OracleP A → ∃ i : ℕ, g i A = L) ∧ ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool), Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') → (x ∈ g i A ↔ x ∈ g i A')) → ∃ B : Language Bool, ({x : List Bool | ∃ w ∈ B, w.length = x.length} : Language Bool) ∉ PEqualNP.Library.OracleP B := by
  rintro ⟨g, q, hcov, hloc⟩
  obtain ⟨B, hB⟩ := PEqualNP.Library.Helpers.BGS.diagonal g q hloc
  refine ⟨B, fun hmem => ?_⟩
  obtain ⟨i, hi⟩ := hcov B _ hmem
  exact hB i hi
