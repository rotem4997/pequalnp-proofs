import PEqualNP.Library.L002
import PEqualNP.Library.L004

/-- P is inside EXP: a language in P is decided within `n ^ k + k` steps, which is at most
`2 ^ (n ^ k) + k`. -/
theorem PEqualNP.Library.L044 : PEqualNP.Library.P ⊆ PEqualNP.Library.EXP := by
  intro L hL
  obtain ⟨k, hk⟩ := (PEqualNP.Library.L004 L).mp hL
  refine ⟨k, PEqualNP.Library.L002 _ _ (fun n => ?_) hk⟩
  exact Nat.add_le_add_right (Nat.lt_two_pow_self).le k
