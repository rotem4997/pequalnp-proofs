import PEqualNP.Library.Helpers.ExpClockK0

/-- L-lib-082 is false at k = 0: the bound is then the constant 3c, but a machine must erase its
input, so its running time grows at least linearly in the input length. -/
theorem PEqualNP.Library.L082Refutation : ¬ (∀ k : ℕ, ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true) (fun n : ℕ => c * 2 ^ (n ^ k) + c)) :=
  PEqualNP.Library.Helpers.L082_statement_false
