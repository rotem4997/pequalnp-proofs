import PEqualNP.Library.Universal.Hierarchy

/-- Time hierarchy for P: for every `k` some language in P is not decided in `n ^ k + k` steps. -/
theorem PEqualNP.Library.L011 : ∀ k : ℕ, ∃ L ∈ PEqualNP.Library.P, L ∉ PEqualNP.Library.DTIME (fun n : ℕ => n ^ k + k) :=
  PEqualNP.Library.Universal.hierarchy
