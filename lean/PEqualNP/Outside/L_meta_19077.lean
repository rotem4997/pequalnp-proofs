import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19077

open PEqualNP.CircuitLowerBounds

def A : Fin 4 → Fin 4 → Bool :=
  fun u v : Fin 4 => (4813 : ℕ).testBit (4 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [2, 4] },
        { op := GateOp.or, inputs := [3, 5] },
        { op := GateOp.or, inputs := [0, 9] },
        { op := GateOp.or, inputs := [8, 9] },
        { op := GateOp.and, inputs := [8, 10] },
        { op := GateOp.not, inputs := [11] },
        { op := GateOp.or, inputs := [12, 13] } ],
    output := 14 }

theorem upper_fanInTwo : PEqualNP.MetaComplexity.FanInTwo upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19077

theorem PEqualNP.Outside.L_meta_19077 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4813 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19077.upperC, PEqualNP.Outside.L_meta_19077.upper_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_19077.upper_rep⟩
