import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19442_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [5, 1]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [10, 11]⟩, ⟨.not, [15]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [12, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19442_aux

theorem PEqualNP.Outside.L_meta_19442 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594810 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19442_aux.circuit, PEqualNP.Outside.L_meta_19442_aux.fan, by decide, by decide +kernel⟩
