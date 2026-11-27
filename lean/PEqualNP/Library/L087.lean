import PEqualNP.Library.Helpers.RRFanInTwo
import PEqualNP.Library.Helpers.RRSeeded

/-- Razborov-Rudich with fan-in-two distinguishers, from the circuit simulation (corrects the
vacuous L-lib-074). -/
theorem PEqualNP.Library.L087 : (∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3)) → (∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ PEqualNP.Library.P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 2 ^ (n / k) → |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) - (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) → ¬ ∃ Q : Language Bool, PEqualNP.MetaComplexity.Large Q ∧ Q ∈ PEqualNP.Library.P ∧ ∀ k : ℕ, PEqualNP.MetaComplexity.UsefulAgainst Q (fun n : ℕ => n ^ k + k) :=
  fun h => PEqualNP.Library.Helpers.RRFanInTwo.linkC2
    (PEqualNP.Library.Helpers.RRFanInTwo.linkA2 h) (PEqualNP.Library.Helpers.RRSeeded.linkB h)
