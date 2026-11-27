import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19246_aux

def witness : Circuit :=
  ⟨[⟨.or, [0, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.not, [14]⟩, ⟨.and, [16, 18]⟩], 19⟩

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

end PEqualNP.Outside.L_meta_19246_aux

open PEqualNP.Outside.L_meta_19246_aux in
theorem PEqualNP.Outside.L_meta_19246 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247934 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
