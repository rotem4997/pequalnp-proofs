import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19436_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 6]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [15, 6]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19436_aux

theorem PEqualNP.Outside.L_meta_19436 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3312573 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19436_aux.circuit, PEqualNP.Outside.L_meta_19436_aux.fan, by decide, by decide +kernel⟩
