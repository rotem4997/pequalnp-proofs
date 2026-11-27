import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17142

theorem sing (p l : Fin 13) : (p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9) ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by
  revert p l
  decide

theorem miss (Q : Finset (Fin 13)) (l : Fin 13) :
    l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q ↔
      ∀ q ∈ Q, ¬(q - l = 0 ∨ q - l = 1 ∨ q - l = 3 ∨ q - l = 9) := by
  simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.disjoint_left]
  constructor
  · intro h q hq hc
    exact h ((sing q l).1 hc) hq
  · intro h q hq hqQ
    exact h q hqQ ((sing q l).2 hq)

end PEqualNP.Outside.L_meta_17142

theorem PEqualNP.Outside.L_meta_17142 :
    ∀ (x1 : Finset (Fin (13 : ℕ))) (x2 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1 ↔ ∀ x3 ∈ x1, ¬(x3 - x2 = (0 : Fin (13 : ℕ)) ∨ x3 - x2 = (1 : Fin (13 : ℕ)) ∨ x3 - x2 = (3 : Fin (13 : ℕ)) ∨ x3 - x2 = (9 : Fin (13 : ℕ))) := by
  exact PEqualNP.Outside.L_meta_17142.miss
