import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7093
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

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

end PEqualNP.Outside.L_meta_7093

open PEqualNP.Outside.L_meta_7093 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7093 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs.length ≤ (2 : ℕ) → (∀ x8 ∈ x3.inputs, x8 < x1 + x2.size) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x9 ∧ x9.size = x2.size + (1 : ℕ) ∧ ∀ (x10 : List Bool), x10.length = x1 → x9.eval x10 = x3.op.eval (List.map (fun (x12 : ℕ) => (x2.wires x10).getD x12 Bool.false) x3.inputs) := by
  intro n C g hm hrb hop hlen hin
  refine ⟨⟨C.gates ++ [g], n + C.gates.length⟩, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hm g' h
    · rw [List.mem_singleton.1 h]
      refine ⟨?_, hlen⟩
      rcases hop with h1 | h1
      · rw [h1]; exact Or.inl rfl
      · rw [h1]; exact Or.inr rfl
  · intro j hj i hi
    have hj' : j < C.gates.length + 1 := by simpa using hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    by_cases hjl : j < C.gates.length
    · have e : (C.gates ++ [g]).getD j ⟨GateOp.or, []⟩ = C.gates[j] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, List.getElem?_eq_getElem hjl]
      rw [e] at hi
      exact hrb j hjl i (by rw [gateAt_eq C j hjl]; exact hi)
    · have hje : j = C.gates.length := by omega
      have e : (C.gates ++ [g]).getD j ⟨GateOp.or, []⟩ = g := by
        subst hje
        simp [List.getD_eq_getElem?_getD]
      rw [e] at hi
      have := hin i hi
      have hs : C.size = C.gates.length := rfl
      omega
  · show (C.gates ++ [g]).length = C.gates.length + 1
    simp
  · intro x hx
    show (wf (C.gates ++ [g]) x).getD (n + C.gates.length) false
      = g.op.eval (g.inputs.map fun k => (wf C.gates x).getD k false)
    rw [wf_snoc]
    have hl : (wf C.gates x).length = n + C.gates.length := by rw [wf_len, hx]
    rw [← hl, getD_snoc_eq]
