import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19446_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 8]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [15, 16]⟩, ⟨.not, [17]⟩, ⟨.and, [14, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19446_aux

theorem PEqualNP.Outside.L_meta_19446 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (8130428 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19446_aux.circuit, PEqualNP.Outside.L_meta_19446_aux.fan, by decide, by decide +kernel⟩
