import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_9103 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (51811205313 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : Circuit := ⟨[⟨.or, [1, 8]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [3, 6]⟩,
    ⟨.and, [14, 15]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [12, 17]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [19, 10]⟩,
    ⟨.and, [5, 11]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [22, 23]⟩], 24⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
