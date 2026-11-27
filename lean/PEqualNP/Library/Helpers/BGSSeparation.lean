import PEqualNP.Library.L059
import PEqualNP.Library.L060

/-!
# The Baker-Gill-Solovay separation, assembled

Helper module for `L-lib-062` (proofs only). From the enumeration statement of `L-lib-058`,
the diagonal `L-lib-059` gives an oracle `B` whose length test is outside `P^B`, and `L-lib-060`
puts that test inside `NP^B`.
-/

namespace PEqualNP.Library.Helpers.BGS

theorem separation_of_enum
    (h : ∃ (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ),
      (∀ (A L : Language Bool), L ∈ PEqualNP.Library.OracleP A → ∃ i : ℕ, g i A = L) ∧
      ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool),
        Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') →
          (x ∈ g i A ↔ x ∈ g i A')) :
    ∃ B : Language Bool, PEqualNP.Library.OracleP B ≠ PEqualNP.Library.OracleNP B := by
  obtain ⟨B, hB⟩ := PEqualNP.Library.L059 h
  exact ⟨B, fun heq => hB (heq ▸ PEqualNP.Library.L060 B)⟩

end PEqualNP.Library.Helpers.BGS
