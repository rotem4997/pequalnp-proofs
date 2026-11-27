import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 16 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_19231_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 12]⟩], 13⟩

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

end PEqualNP.Outside.L_meta_19231_aux

open PEqualNP.Outside.L_meta_19231_aux in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_19231 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13260 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨witness, witnessFit, by decide +kernel, ?_⟩
  intro u v
  revert u v
  decide +kernel
