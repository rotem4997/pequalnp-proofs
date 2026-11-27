import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19300.Work

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Op := Nat × Nat × Nat

def gate (o : Op) : Gate :=
  if o.1 = 0 then ⟨.and, [o.2.1, o.2.2]⟩
  else if o.1 = 1 then ⟨.or, [o.2.1, o.2.2]⟩
  else ⟨.not, [o.2.1]⟩

def operations : List Op := [(1, 1, 2), (2, 10, 10), (2, 0, 0), (1, 5, 6), (1, 7, 8), (0, 12, 13), (0, 11, 14), (0, 10, 9), (1, 15, 16), (1, 18, 17)]

def C : Circuit := ⟨operations.map gate, 19⟩

theorem fanIn : FanInTwo C := by
  intro g hg
  change g ∈ operations.map gate at hg
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp hg
  by_cases h : o.1 = 0
  · simp [gate, h]
  · by_cases j : o.1 = 1 <;> simp [gate, h, j]

end PEqualNP.Outside.L_meta_19300.Work

open PEqualNP.Outside.L_meta_19300.Work in
theorem PEqualNP.Outside.L_meta_19300 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16240236 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨C, fanIn, by decide, ?_⟩
  unfold PEqualNP.Represents.Represents
  decide +kernel
