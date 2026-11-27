import Mathlib
import PEqualNP.Defs

/-! `C` outputs the NOT of wire `w`, so `!x p || C x` is the NOT of `x p && wire w`. Keep the
  gates `gs`, then add an AND of input `p` and wire `w`, and a NOT of that AND. -/

namespace PEqualNP.Outside.L_meta_200_aux

open PEqualNP.CircuitLowerBounds

/-- One evaluation step of a circuit, as in `Circuit.wires`. -/
def step (l : List Bool) (g : Gate) : List Bool :=
  l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]

lemma foldl_len (gs : List Gate) (l : List Bool) :
    (gs.foldl step l).length = l.length + gs.length := by
  induction gs generalizing l with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

lemma foldl_prefix (gs : List Gate) (l : List Bool) : ∃ t, gs.foldl step l = l ++ t := by
  induction gs generalizing l with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step l g)
    refine ⟨g.op.eval (g.inputs.map fun i => l.getD i false) :: t, ?_⟩
    rw [List.foldl_cons, ht, step, List.append_assoc, List.singleton_append]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

end PEqualNP.Outside.L_meta_200_aux

open PEqualNP.Outside.L_meta_200_aux in
theorem PEqualNP.Outside.L_meta_200 : ∀ (n : ℕ) (p : Fin n) (w : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit), C = { gates := gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [w]⟩], output := n + gs.length } → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.HasCircuitSize n (fun x => !x p || PEqualNP.MetaComplexity.circuitFun n C x) (C.size + 1)
 := by
  intro n p w gs C hC hfan
  subst hC
  refine ⟨⟨gs ++ [⟨.and, [p.val, w]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hfan g (List.mem_append_left _ hg)
    · simp
    · simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      wires_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨t, ht⟩ := foldl_prefix gs (List.ofFn x)
    have hlen := foldl_len gs (List.ofFn x)
    rw [ht] at hlen ⊢
    simp only [List.length_append, List.length_ofFn] at hlen
    have hW : (List.ofFn x ++ t).length = n + gs.length := by simp [hlen]
    have hp : (List.ofFn x ++ t)[p.val]?.getD false = x p := by
      rw [List.getElem?_append_left (by simp)]
      simp
    generalize List.ofFn x ++ t = W at hW hp ⊢
    simp [step, hW, hp, PEqualNP.CircuitLowerBounds.GateOp.eval]
