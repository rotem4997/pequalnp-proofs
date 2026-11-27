import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19445_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [14, 15]⟩, ⟨.not, [16]⟩, ⟨.and, [13, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19445_aux

theorem PEqualNP.Outside.L_meta_19445 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (8128318 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19445_aux.circuit, PEqualNP.Outside.L_meta_19445_aux.fan, by decide, by decide +kernel⟩
