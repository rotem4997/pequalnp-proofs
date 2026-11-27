import PEqualNP.Defs

-- An explicit circuit of fan-in two (9 AND/OR gates, 1 NOT gate(s)) found by a SAT search for exact
-- synthesis. Gate kinds by cases (the pattern of the merged L_meta_10258), the size
-- and the 25 promise inputs by `decide`.

namespace PEqualNP.Outside.L_meta_19505_aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 to 4 are the left vertices, 5 to 9 the right ones; gate `j` writes wire `10 + j`. -/
def C : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [10, 16]⟩, ⟨.not, [17]⟩, ⟨.and, [15, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_19505_aux

theorem PEqualNP.Outside.L_meta_19505 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7882302 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19505_aux.C, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19505_aux.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
