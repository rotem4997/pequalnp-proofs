import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7121

open PEqualNP.CircuitLowerBounds

def circ : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩], 8⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  simp

theorem computes : ∀ x : Fin 8 → Bool, circ.eval (List.ofFn x) = (x 0 || x 3) := by
  decide +kernel

end PEqualNP.Outside.L_meta_7121

theorem PEqualNP.Outside.L_meta_7121 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (1 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))) :=
  ⟨PEqualNP.Outside.L_meta_7121.circ, PEqualNP.Outside.L_meta_7121.mono, by decide,
    PEqualNP.Outside.L_meta_7121.computes⟩
