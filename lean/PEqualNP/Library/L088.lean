import PEqualNP.Library.Universal.GenHierarchy

/-- Time hierarchy for time-constructible bounds: a fixed polynomial gap `k` separates `DTIME`. -/
theorem PEqualNP.Library.L088 : ∃ k : ℕ, ∀ t : ℕ → ℕ, (∀ n : ℕ, n ≤ t n) → (∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => List.replicate (t x.length) true) (fun n : ℕ => c * t n + c)) → ∃ L : Language Bool, (∃ c : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => c * t n ^ k + c)) ∧ L ∉ PEqualNP.Library.DTIME t :=
  PEqualNP.Library.Universal.genHierarchy
