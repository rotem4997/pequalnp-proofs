import Mathlib
import PEqualNP.Defs


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19298

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.not, [17]⟩, ⟨.and, [14, 18]⟩], 19⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19298

open PEqualNP.Outside.L_meta_19298 in
theorem PEqualNP.Outside.L_meta_19298 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237180 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
