import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_9286 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (40574043531 : ℕ).testBit (6 * u.val + v.val)) 19 := by
  let C : Circuit := ⟨[⟨.or, [5, 9]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [15, 12]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [19, 1]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [19, 6]⟩, ⟨.or, [20, 10]⟩, ⟨.and, [26, 24]⟩, ⟨.or, [27, 18]⟩, ⟨.and, [22, 23]⟩, ⟨.or, [28, 29]⟩], 30⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
