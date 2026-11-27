import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19435_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [2, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.not, [17]⟩, ⟨.and, [14, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19435_aux

theorem PEqualNP.Outside.L_meta_19435 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3269438 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19435_aux.circuit, PEqualNP.Outside.L_meta_19435_aux.fan, by decide, by decide +kernel⟩
