import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19476_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [2, 15]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.not, [18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19476_aux

theorem PEqualNP.Outside.L_meta_19476 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16221750 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19476_aux.circuit, PEqualNP.Outside.L_meta_19476_aux.fan, by decide, by decide +kernel⟩
