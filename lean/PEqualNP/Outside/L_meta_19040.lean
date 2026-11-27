import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19040

def witness : Circuit :=
  ⟨[⟨.and, [0, 7]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 11]⟩,
    ⟨.or, [6, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩

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

end PEqualNP.Outside.L_meta_19040

open PEqualNP.Outside.L_meta_19040 in
theorem PEqualNP.Outside.L_meta_19040 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4733 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
