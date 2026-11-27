import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19192

open PEqualNP.CircuitLowerBounds

def A : Fin 4 → Fin 4 → Bool :=
  fun u v : Fin 4 => (990 : ℕ).testBit (4 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [
        { op := GateOp.or, inputs := [1, 4] },
        { op := GateOp.or, inputs := [0, 5] },
        { op := GateOp.or, inputs := [8, 9] },
        { op := GateOp.and, inputs := [8, 9] },
        { op := GateOp.or, inputs := [3, 11] },
        { op := GateOp.not, inputs := [12] },
        { op := GateOp.and, inputs := [10, 13] }
      ],
    output := 14 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19192

theorem PEqualNP.Outside.L_meta_19192 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (990 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19192.upperC, PEqualNP.Outside.L_meta_19192.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_19192.upper_rep⟩
