import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19443

private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 3]⟩,
      ⟨.or, [7, 6]⟩,
      ⟨.or, [4, 2]⟩,
      ⟨.or, [4, 9]⟩,
      ⟨.and, [13, 10]⟩,
      ⟨.or, [11, 14]⟩,
      ⟨.and, [12, 15]⟩,
      ⟨.or, [12, 15]⟩,
      ⟨.not, [17]⟩,
      ⟨.or, [16, 18]⟩], 19⟩

private theorem fan : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19443

open PEqualNP.Outside.L_meta_19443 in
theorem PEqualNP.Outside.L_meta_19443 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7641913 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨witness, fan, by decide +kernel, by decide +kernel⟩

