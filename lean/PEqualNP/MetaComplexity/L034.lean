import PEqualNP.MetaComplexity.Helpers.NaturalAll

/-- If MCSP is in P then a single property of truth tables is large, decided in polynomial
time, and useful against circuits of every polynomial size (Razborov and Rudich 1997; Kabanets
and Cai 2000): the tables whose function has no circuit of size `2 ^ (n / 2)`, padded with
every short table. The uniform form of `L-meta-008`. -/
theorem PEqualNP.MetaComplexity.L034 : PEqualNP.MetaComplexity.MCSP ∈ PEqualNP.Library.P → ∃ Q : Language Bool, PEqualNP.MetaComplexity.Large Q ∧ Q ∈ PEqualNP.Library.P ∧ ∀ k : ℕ, PEqualNP.MetaComplexity.UsefulAgainst Q (fun n : ℕ => n ^ k + k) :=
  PEqualNP.MetaComplexity.Helpers.NaturalAll.natural_all_of_mcsp
