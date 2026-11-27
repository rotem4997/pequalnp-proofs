import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19502_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [10, 14]⟩, ⟨.and, [11, 15]⟩, ⟨.not, [16]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [12, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19502_aux

theorem PEqualNP.Outside.L_meta_19502 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7641305 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19502_aux.circuit, PEqualNP.Outside.L_meta_19502_aux.fan, by decide, by decide +kernel⟩
