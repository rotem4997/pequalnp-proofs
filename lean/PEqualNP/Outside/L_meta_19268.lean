import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19268

open PEqualNP.CircuitLowerBounds

def A : Fin 4 → Fin 4 → Bool :=
  fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [
        { op := GateOp.not, inputs := [4] },
        { op := GateOp.or, inputs := [0, 4] },
        { op := GateOp.or, inputs := [1, 8] },
        { op := GateOp.and, inputs := [9, 10] }
      ],
    output := 11 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19268

theorem PEqualNP.Outside.L_meta_19268 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19268.upperC, PEqualNP.Outside.L_meta_19268.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_19268.upper_rep⟩
