import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

end PEqualNP.Outside.L_meta_2878

open PEqualNP.Outside.L_meta_2878 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2878 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp), x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ (x6 x7 : ℕ), ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false, (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro n C hC op hop a b
  refine ⟨⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC g hg
    · refine ⟨?_, by simp⟩
      rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr h
  · simp [Circuit.size]
  · intro x
    show (wf (C.gates ++ [⟨op, [a, b]⟩]) (List.ofFn x)).getD (n + C.gates.length) false
      = op.eval [(wf C.gates (List.ofFn x)).getD a false, (wf C.gates (List.ofFn x)).getD b false]
    rw [wf_snoc]
    have hl : (wf C.gates (List.ofFn x)).length = n + C.gates.length := by
      rw [wf_len, List.length_ofFn]
    rw [← hl, getD_snoc_eq]
    rfl
