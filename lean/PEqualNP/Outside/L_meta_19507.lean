import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19507_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.and, [0, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [16, 1]⟩, ⟨.or, [15, 17]⟩, ⟨.not, [18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19507_aux

theorem PEqualNP.Outside.L_meta_19507 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16221393 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19507_aux.circuit, PEqualNP.Outside.L_meta_19507_aux.fan, by decide, by decide +kernel⟩
