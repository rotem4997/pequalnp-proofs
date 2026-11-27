import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19420

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.not, [4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [0, 12]⟩, ⟨.not, [14]⟩, ⟨.not, [15]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, witness_ok⟩


end PEqualNP.Outside.L_meta_19420

theorem PEqualNP.Outside.L_meta_19420 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19420.solve
