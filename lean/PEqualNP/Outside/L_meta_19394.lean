import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19394

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.and, [14, 18]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [19, 20]⟩], 21⟩

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

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19394

theorem PEqualNP.Outside.L_meta_19394 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_19394.main_aux
