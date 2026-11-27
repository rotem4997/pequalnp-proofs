import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7163
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_7163

open PEqualNP.Outside.L_meta_7163 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7163 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Bool) (x5 x6 : ℕ), ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = (if x4 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [(x2.wires (List.ofFn x8)).getD x5 Bool.false, (x2.wires (List.ofFn x8)).getD x6 Bool.false] := by
  intro n C hm o a b
  refine ⟨⟨C.gates ++ [⟨if o = true then GateOp.and else GateOp.or, [a, b]⟩], n + C.gates.length⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hm g h
    · rw [List.mem_singleton.1 h]
      refine ⟨?_, by simp⟩
      cases o
      · exact Or.inr rfl
      · exact Or.inl rfl
  · show (C.gates ++ [(⟨if o = true then GateOp.and else GateOp.or, [a, b]⟩ : Gate)]).length
      ≤ C.gates.length + 1
    simp
  · intro x
    show (wf (C.gates ++ [(⟨if o = true then GateOp.and else GateOp.or, [a, b]⟩ : Gate)])
      (List.ofFn x)).getD (n + C.gates.length) false = _
    rw [wf_snoc]
    have hl : (wf C.gates (List.ofFn x)).length = n + C.gates.length := by
      rw [wf_len]; simp
    rw [← hl, getD_snoc_eq]
    rfl
