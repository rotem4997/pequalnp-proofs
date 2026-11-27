import PEqualNP.MetaComplexity.Helpers.Natural

/-- If MCSP is in P then for every `k` there is a property of truth tables that is decided in
polynomial time, large, and useful against circuits of size `n ^ k` (Razborov and Rudich 1997;
Kabanets and Cai 2000): the tables whose function has no circuit of size `(n + 1) ^ k`, padded
with every short table. -/
theorem PEqualNP.MetaComplexity.L008 : PEqualNP.MetaComplexity.MCSP ∈ PEqualNP.Library.P → ∀ k : ℕ, ∃ Q : Language Bool, Q ∈ PEqualNP.Library.P ∧ PEqualNP.MetaComplexity.Large Q ∧ PEqualNP.MetaComplexity.UsefulAgainst Q (fun n : ℕ => n ^ k) :=
  PEqualNP.MetaComplexity.Helpers.Natural.natural_of_mcsp
