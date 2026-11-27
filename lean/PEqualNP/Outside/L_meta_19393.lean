import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19393

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [6, 17]⟩, ⟨.and, [16, 19]⟩, ⟨.or, [18, 20]⟩], 21⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19393

open PEqualNP.Outside.L_meta_19393 in
theorem PEqualNP.Outside.L_meta_19393 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12064434 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
