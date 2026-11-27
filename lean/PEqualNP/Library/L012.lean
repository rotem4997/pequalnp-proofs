import PEqualNP.Library.Universal.ExpHierarchy

/-- Some language decidable in exponential time `2 ^ (n ^ k) + k` is not in P. -/
theorem PEqualNP.Library.L012 : ∃ L : Language Bool, (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧ L ∉ PEqualNP.Library.P :=
  PEqualNP.Library.Universal.expHierarchy
