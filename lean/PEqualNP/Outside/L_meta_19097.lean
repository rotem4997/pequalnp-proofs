import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19097 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1983 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.and, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
