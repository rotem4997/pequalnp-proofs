import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6357

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton l a ih => rw [W_snoc]; simp [ih]; omega


theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem ao2_snoc {n : ℕ} {C : Circuit} (hok : PEqualNP.TopForm.IsAO2 n C) {a b o : ℕ}
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    PEqualNP.TopForm.IsAO2 n ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], o⟩ := by
  obtain ⟨h1, h2, h3⟩ := hok
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h1 g hg
    · exact Or.inl rfl
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < C.gates.length
    · apply h2 j hjl i
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hjl] using hi
    · have hje : j = C.gates.length := by omega
      subst hje
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at hi
      rcases hi with rfl | rfl <;> assumption
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h3 g hg
    · rfl

end PEqualNP.Outside.L_meta_6357

open PEqualNP.Outside.L_meta_6357 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6357 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     x3 < x1 + x2.size →       x4 < x1 + x2.size →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.TopForm.IsAO2 x1 x8 ∧           ∀ (x9 : Fin x1 → Bool),             have x10 : List Bool := x2.wires (List.ofFn x9);             have x11 : List Bool := x8.wires (List.ofFn x9);             x8.eval (List.ofFn x9) = (x10.getD x3 Bool.false && x10.getD x4 Bool.false) ∧ x11.getD x3 Bool.false = x10.getD x3 Bool.false ∧ x11.getD x4 Bool.false = x10.getD x4 Bool.false := by
  intro n C a b hok ha hb
  refine ⟨ao2_snoc hok ha hb, fun x => ?_⟩
  have hl : (W C.gates (List.ofFn x)).length = n + C.gates.length := by rw [W_length]; simp
  have ha' : a < (W C.gates (List.ofFn x)).length := by rw [hl]; exact ha
  have hb' : b < (W C.gates (List.ofFn x)).length := by rw [hl]; exact hb
  refine ⟨?_, ?_, ?_⟩
  · show (W (C.gates ++ [_]) (List.ofFn x)).getD (n + C.gates.length) false = _
    rw [W_snoc, wires_eq]
    simp [List.getD_eq_getElem?_getD, ← hl, GateOp.eval]
  · show (W (C.gates ++ [_]) (List.ofFn x)).getD a false = _
    rw [W_snoc, wires_eq]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · show (W (C.gates ++ [_]) (List.ofFn x)).getD b false = _
    rw [W_snoc, wires_eq]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hb']
