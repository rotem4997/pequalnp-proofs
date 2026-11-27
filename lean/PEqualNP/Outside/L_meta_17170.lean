import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17170_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [21, 25]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [24, 23]⟩, ⟨.or, [24, 22]⟩, ⟨.and, [16, 26]⟩, ⟨.and, [17, 27]⟩, ⟨.and, [18, 28]⟩, ⟨.and, [19, 29]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [34, 35]⟩], 36⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => decide (u.val / 4 = v.val / 4 ∧ u.val % 4 ≠ v.val % 4)) 21 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_17170_aux

theorem PEqualNP.Outside.L_meta_17170 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => decide (u.val / 4 = v.val / 4 ∧ u.val % 4 ≠ v.val % 4)) 21 :=
  PEqualNP.Outside.L_meta_17170_aux.main
