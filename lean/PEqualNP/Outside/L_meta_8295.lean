import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem split (l : List Gate) (h : ∃ g ∈ l, g.op = GateOp.not) :
    ∃ pre g suf, l = pre ++ g :: suf ∧ g.op = GateOp.not ∧ ∀ h ∈ suf, h.op ≠ GateOp.not := by
  induction l with
  | nil => obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons a l ih =>
    by_cases h' : ∃ g ∈ l, g.op = GateOp.not
    · obtain ⟨pre, g, suf, h1, h2, h3⟩ := ih h'
      exact ⟨a :: pre, g, suf, by rw [h1]; rfl, h2, h3⟩
    · push_neg at h'
      obtain ⟨g, hg, hn⟩ := h
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨[], g, l, rfl, hn, h'⟩
      · exact absurd hn (h' g hg)

theorem core (x1 : ℕ) (C : Circuit) (hF : FanInTwo C)
    (h : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ (x5 x6 : Circuit), FanInTwo x5 ∧ Monotone2 x6 ∧ x5.size + x6.size + 1 = C.size ∧
      ∀ (x7 : Fin x1 → Bool), C.eval (List.ofFn x7) =
        x6.eval (x5.wires (List.ofFn x7) ++ [!x5.eval (List.ofFn x7)]) := by
  obtain ⟨pre, g, suf, h1, h2, h3⟩ := split C.gates h
  refine ⟨⟨pre, g.inputs.headD (x1 + pre.length)⟩, ⟨suf, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact hF a (by rw [h1]; simp [show a ∈ pre from ha])
  · intro a ha
    have ha' : a ∈ suf := ha
    obtain ⟨ho, hl⟩ := hF a (by rw [h1]; simp [ha'])
    refine ⟨?_, hl⟩
    have := h3 a ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    tauto
  · simp [Circuit.size, h1]; omega
  · intro x
    simp only [Circuit.eval, wires_eq, h1, List.foldl_append, List.foldl_cons]
    congr 2
    have hl : (List.foldl step (List.ofFn x) pre).length = x1 + pre.length := by
      rw [fold_len]; simp
    generalize List.foldl step (List.ofFn x) pre = W at hl
    simp only [step, h2]
    congr 2
    rcases g.inputs with _ | ⟨a, t⟩
    · simp [GateOp.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none, hl]
    · simp [GateOp.eval]

end PEqualNP.Outside.L_meta_8295

open PEqualNP.Outside.L_meta_8295 in
theorem PEqualNP.Outside.L_meta_8295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ x4 ∈ x2.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ x5.size + x6.size + (1 : ℕ) = x2.size ∧ ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x6.eval (x5.wires (List.ofFn x7) ++ [!x5.eval (List.ofFn x7)]) := by
  intro x1 x2 hF h
  exact core x1 x2 hF h
