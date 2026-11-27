import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19491_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 6]⟩, ⟨.not, [10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 1]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.not, [18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19491_aux

theorem PEqualNP.Outside.L_meta_19491 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7570521 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19491_aux.circuit, PEqualNP.Outside.L_meta_19491_aux.fan, by decide, by decide +kernel⟩
