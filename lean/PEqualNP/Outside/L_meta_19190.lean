import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19190_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 1]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [11, 14]⟩], 15⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19190_aux

theorem PEqualNP.Outside.L_meta_19190 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13806 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19190_aux.circuit, PEqualNP.Outside.L_meta_19190_aux.fan, by decide, by decide +kernel⟩
