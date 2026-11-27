import PEqualNP.Library.L002
import PEqualNP.Library.L004

/-- P is contained in EXP. -/
theorem PEqualNP.Library.L049 : PEqualNP.Library.P ⊆ PEqualNP.Library.EXP := by
  intro L hL
  obtain ⟨k, hk⟩ := (PEqualNP.Library.L004 L).mp hL
  exact ⟨k, PEqualNP.Library.L002 _ _
    (fun n => Nat.add_le_add_right Nat.lt_two_pow_self.le k) hk⟩
