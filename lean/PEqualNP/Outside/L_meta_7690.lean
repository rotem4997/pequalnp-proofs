import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7690

open PEqualNP.CircuitLowerBounds

lemma length_foldl (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact length_foldl C.gates x

lemma wires_snoc (C : Circuit) (g : Gate) (o : ℕ) (x : List Bool) :
    ({ gates := C.gates ++ [g], output := o } : Circuit).wires x
      = C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

end PEqualNP.Outside.L_meta_7690

open PEqualNP.Outside.L_meta_7690 in
theorem PEqualNP.Outside.L_meta_7690 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.GateOp), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → x4 = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.and → x2 < (14 : ℕ) + x1.size → x3 < (14 : ℕ) + x1.size → x2 ≠ x3 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.size = x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x11 ∧ (∀ x12 ∈ x11.gates, x12.inputs.Nodup) ∧ x11.output = (14 : ℕ) + x1.size ∧ x11.gates[x1.size]? = Option.some { op := x4, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (14 : ℕ) → Bool), (∀ x13 < (14 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x11 (14 : ℕ) x12 x13 = PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x13) ∧ PEqualNP.BlindGate.wireValue x11 (14 : ℕ) x12 x11.output = x4.eval [PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x2, PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x3] := by
  intro C a b op hAO hnd hop ha hb hab
  obtain ⟨h1, h2, h3⟩ := hAO
  unfold PEqualNP.CircuitLowerBounds.Circuit.size at ha hb
  refine ⟨⟨C.gates ++ [⟨op, [a, b]⟩], 14 + C.size⟩, ?_, ⟨?_, ?_, ?_⟩, ?_, rfl, ?_, ?_⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h1 g hg
    · exact hop.symm
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < C.gates.length
    · have hg : PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨C.gates ++ [⟨op, [a, b]⟩], 14 + C.size⟩ j
          = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        exact List.getD_append _ _ _ _ hlt
      rw [hg] at hi
      exact h2 j hlt i hi
    · have hj' : j = C.gates.length := by omega
      subst hj'
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨C.gates ++ [⟨op, [a, b]⟩], 14 + C.size⟩ C.gates.length = ⟨op, [a, b]⟩ := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp
      rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h3 g hg
    · rfl
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hnd g hg
    · simp [hab]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    have hW := wires_snoc C ⟨op, [a, b]⟩ (14 + C.size) (List.ofFn x)
    have hL := wires_length C (List.ofFn x)
    simp only [List.length_ofFn] at hL
    refine ⟨?_, ?_⟩
    · intro w hw
      unfold PEqualNP.BlindGate.wireValue
      rw [hW]
      unfold PEqualNP.CircuitLowerBounds.Circuit.size at hw
      exact List.getD_append _ _ _ _ (by omega)
    · unfold PEqualNP.BlindGate.wireValue
      rw [hW]
      have hlen : 14 + C.size = (C.wires (List.ofFn x)).length := by
        rw [hL]; rfl
      show (C.wires (List.ofFn x) ++ _).getD (14 + C.size) false = _
      rw [hlen]
      simp
