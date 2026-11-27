import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10402_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Append a true input to the five bits. Exactly two are true precisely when
-- the middle pair of the resulting six bits differs. The comparator order follows
-- Bert Dobbelaere, List of median selection networks, six-input ten-comparator network.
def witness : Circuit := ⟨[
  ⟨.and, [3, 4]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.and, [0, 6]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.and, [1, 5]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.and, [2, 10]⟩,
  ⟨.or, [2, 10]⟩,
  ⟨.or, [12, 11]⟩,
  ⟨.and, [8, 13]⟩,
  ⟨.or, [14, 15]⟩,
  ⟨.and, [14, 15]⟩,
  ⟨.not, [17]⟩,
  ⟨.and, [16, 18]⟩], 19⟩

theorem fanIn : FanInTwo witness := by
  intro g hg
  simp [witness] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem correct : ∀ x : Fin 5 → Bool, witness.eval (List.ofFn x) = decide (((List.ofFn x).count true) = 2) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10402_aux

theorem PEqualNP.Outside.L_meta_10402 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (((List.ofFn x).count true) = 2)) 16 := by
  exact ⟨PEqualNP.Outside.L_meta_10402_aux.witness, PEqualNP.Outside.L_meta_10402_aux.fanIn, by decide, PEqualNP.Outside.L_meta_10402_aux.correct⟩
