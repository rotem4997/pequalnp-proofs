import PEqualNP.Library.Universal.Padding

/-- Upward padding: an exponential-time language, padded in front, is in P. -/
theorem PEqualNP.Library.L092 : ∀ (L : Language Bool) (k : ℕ), L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k) → ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈ PEqualNP.Library.P :=
  fun L k h => PEqualNP.Library.Universal.padding_in_P L k h
