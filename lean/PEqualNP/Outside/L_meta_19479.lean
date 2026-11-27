import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19479_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [10, 9]⟩, ⟨.not, [11]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [15, 0]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19479_aux

theorem PEqualNP.Outside.L_meta_19479 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237110 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19479_aux.circuit, PEqualNP.Outside.L_meta_19479_aux.fan, by decide, by decide +kernel⟩
