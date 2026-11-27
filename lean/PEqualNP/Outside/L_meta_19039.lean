import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19039

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.not, [7]⟩,
    ⟨.and, [1, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩,
    ⟨.or, [9, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_19039

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19039 :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧
      Represents (fun u v : Fin 4 => (4732 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19039.witness,
    by simp [FanInTwo, PEqualNP.Outside.L_meta_19039.witness],
    by decide +kernel, by decide +kernel⟩
