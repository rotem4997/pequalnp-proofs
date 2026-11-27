import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7340_aux

open PEqualNP.CircuitLowerBounds

def cg (N : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i N)⟩

theorem key (N : ℕ) (w : List Bool) (h : w.length ≤ N) (i : ℕ) :
    w.getD (min i N) false = w.getD i false := by
  by_cases hi : i ≤ N
  · rw [Nat.min_eq_left hi]
  · have h1 : w.length ≤ min i N := by omega
    have h2 : w.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

theorem fold (N : ℕ) (gs : List Gate) :
    ∀ w : List Bool, w.length + gs.length ≤ N →
      (gs.map (cg N)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w ∧
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        ≤ N := by
  induction gs with
  | nil => intro w h; exact ⟨rfl, by simpa using h⟩
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have e : (cg N g).op.eval ((cg N g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [cg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact key N w (by omega) i
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact ih _ (by simp; omega)

end PEqualNP.Outside.L_meta_7340_aux

open PEqualNP.Outside.L_meta_7340_aux in
theorem PEqualNP.Outside.L_meta_7340 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size ≤ x2 ∧ x6.output ≤ x1 + x2 ∧ (∀ x7 ∈ x6.gates, ∀ x9 ∈ x7.inputs, x9 ≤ x1 + x2) ∧ ∀ (x7 : List Bool), x7.length = x1 → x6.eval x7 = x3.eval x7 := by
  intro x1 x2 C hF hs
  refine ⟨⟨C.gates.map (cg (x1 + x2)), min C.output (x1 + x2)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hF g0 hg0
    simpa [cg] using this
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hs
  · exact Nat.min_le_right _ _
  · intro g hg i hi
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simp only [cg, List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Nat.min_le_right _ _
  · intro x hx
    have hs2 : C.gates.length ≤ x2 := hs
    obtain ⟨h1, h2⟩ := fold (x1 + x2) C.gates x (by omega)
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only []
    rw [h1]
    exact key (x1 + x2) _ h2 C.output
