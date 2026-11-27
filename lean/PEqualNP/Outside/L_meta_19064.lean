import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19064

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19064

theorem PEqualNP.Outside.L_meta_19064 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5754 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19064.circuit, PEqualNP.Outside.L_meta_19064.fan, by decide, by decide +kernel⟩
