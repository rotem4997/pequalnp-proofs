import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19489_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 9]⟩, ⟨.and, [10, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [15, 6]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19489_aux

theorem PEqualNP.Outside.L_meta_19489 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3573853 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19489_aux.circuit, PEqualNP.Outside.L_meta_19489_aux.fan, by decide, by decide +kernel⟩
