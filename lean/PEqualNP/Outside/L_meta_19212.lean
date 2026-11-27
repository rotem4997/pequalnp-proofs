import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19212

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩], 13⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 6 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19212

theorem PEqualNP.Outside.L_meta_19212 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19212.wit, PEqualNP.Outside.L_meta_19212.wit_fan, PEqualNP.Outside.L_meta_19212.wit_size,
    PEqualNP.Outside.L_meta_19212.wit_rep⟩
