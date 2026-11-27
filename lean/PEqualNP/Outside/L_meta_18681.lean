import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18681

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_18681

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18681 in
theorem PEqualNP.Outside.L_meta_18681 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 ∈ x2.gates, x6.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x2.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), (∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) ∧ PEqualNP.BlindGate.wireValue x10 x1 x11 (x1 + x2.size) = (PEqualNP.BlindGate.wireValue x2 x1 x11 x3 || PEqualNP.BlindGate.wireValue x2 x1 x11 x4)) := by
  intro n C a b h hn ha hb hab
  let g : Gate := ⟨.or, [a,b]⟩
  let D : Circuit := ⟨C.gates ++ [g], C.output⟩
  have size : D.size = C.size + 1 := by simp [D,Circuit.size]
  have oldSize : C.size = C.gates.length := rfl
  have mem (k : Gate) (hk : k ∈ D.gates) : k ∈ C.gates ∨ k = g := by simpa [D] using hk
  refine ⟨D,size,⟨?_,?_,?_⟩,?_,?_⟩
  · intro k hk
    rcases mem k hk with he | rfl
    · exact h.1 k he
    · exact Or.inr rfl
  · intro i hi w hw
    change i < (C.gates ++ [g]).length at hi
    change w ∈ ((C.gates ++ [g]).getD i ⟨.or,[]⟩).inputs at hw
    by_cases hi' : i < C.gates.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi'] at hw
      apply h.2.1 i hi' w
      simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] using hw
    · have e : i = C.gates.length := by simp at hi; omega
      subst i
      simp [List.getD_eq_getElem?_getD, g] at hw
      rcases hw with rfl | rfl
      · simpa [oldSize] using ha
      · simpa [oldSize] using hb
  · intro k hk
    rcases mem k hk with he | rfl
    · exact h.2.2 k he
    · rfl
  · intro k hk
    rcases mem k hk with he | rfl
    · exact hn k he
    · simp [g,hab]
  · intro x
    have len : (C.wires (List.ofFn x)).length = n + C.size := by
      change (run C.gates (List.ofFn x)).length = _
      rw [run_length, List.length_ofFn, oldSize]
    have eq : D.wires (List.ofFn x) = C.wires (List.ofFn x) ++
        [(C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false] := by
      simp [D,Circuit.wires,List.foldl_append,g,GateOp.eval]
    simp only [PEqualNP.BlindGate.wireValue,eq]
    constructor
    · intro i hi
      exact getD_lt _ _ _ (by omega)
    · rw [← len, getD_at]
