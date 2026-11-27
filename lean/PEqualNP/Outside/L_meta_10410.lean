import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10410

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each pair contributes one bit for being nonempty and one for being full.
-- Three true inputs give three nonempty pairs, or two nonempty pairs with one full pair.
def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
   ⟨.and, [0, 1]⟩,
   ⟨.or, [2, 3]⟩,
   ⟨.and, [2, 3]⟩,
   ⟨.or, [4, 5]⟩,
   ⟨.and, [4, 5]⟩,
   ⟨.and, [6, 8]⟩,
   ⟨.or, [6, 8]⟩,
   ⟨.and, [13, 10]⟩,
   ⟨.or, [14, 12]⟩,
   ⟨.and, [12, 10]⟩,
   ⟨.and, [7, 9]⟩,
   ⟨.or, [7, 9]⟩,
   ⟨.and, [18, 11]⟩,
   ⟨.or, [19, 17]⟩,
   ⟨.or, [18, 11]⟩,
   ⟨.or, [16, 21]⟩,
   ⟨.and, [15, 22]⟩,
   ⟨.and, [16, 21]⟩,
   ⟨.or, [20, 24]⟩,
   ⟨.not, [25]⟩,
   ⟨.and, [23, 26]⟩], 27⟩

end PEqualNP.Outside.L_meta_10410

theorem PEqualNP.Outside.L_meta_10410 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide (((List.ofFn x).count true) = 3)) 22 := by
  refine ⟨PEqualNP.Outside.L_meta_10410.circuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_10410.circuit,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · decide
  · decide +kernel
