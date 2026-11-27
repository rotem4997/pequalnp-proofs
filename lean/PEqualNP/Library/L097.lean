import PEqualNP.Library.Universal.Projection

/-- Projection: bounded existential quantification over a polynomial-time map into an NP language stays in NP. -/
theorem PEqualNP.Library.L097 : ∀ (E : Language Bool) (π : List Bool × List Bool → List Bool) (p : Polynomial ℕ), E ∈ PEqualNP.Library.NP → PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair (fun x : List Bool => x) π → ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ π (x, c) ∈ E} : Language Bool) ∈ PEqualNP.Library.NP :=
  fun E π p hE hπ => PEqualNP.Library.Universal.projection_np E π p hE hπ
