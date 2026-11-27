import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2677_aux

open PEqualNP.CircuitLowerBounds

def cap (g : Gate) : Gate := ⟨g.op, g.inputs.map fun k => min k 24⟩

theorem getD_cap (w : List Bool) (h : w.length ≤ 24) (i : ℕ) :
    w.getD (min i 24) false = w.getD i false := by
  by_cases hi : i ≤ 24
  · rw [min_eq_left hi]
  · have h1 : min i 24 = 24 := min_eq_right (by omega)
    rw [h1, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem fold_cap (gs : List Gate) : ∀ (w : List Bool), w.length + gs.length ≤ 24 →
    (gs.map cap).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
      = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w ∧
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w _; simp
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    simp only [List.map_cons, List.foldl_cons]
    have e : (cap g).op.eval ((cap g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [cap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_cap w (by omega) i
    rw [e]
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    refine ⟨this.1, ?_⟩
    rw [this.2]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end PEqualNP.Outside.L_meta_2677_aux

open PEqualNP.Outside.L_meta_2677_aux in
theorem PEqualNP.Outside.L_meta_2677 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size = x1.size ∧ (PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2) ∧ (PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2) ∧ x2.output ≤ (24 : ℕ) ∧ (∀ x3 ∈ x2.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (24 : ℕ)) ∧ ∀ (x3 : List Bool), x3.length + x1.size ≤ (24 : ℕ) → x2.wires x3 = x1.wires x3 ∧ x2.eval x3 = x1.eval x3 ∧ (x1.wires x3).length = x3.length + x1.size := by
  intro x1
  refine ⟨⟨x1.gates.map cap, min x1.output 24⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro h g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := h g0 hg0
    simpa [cap] using this
  · intro h g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := h g0 hg0
    simpa [cap] using this
  · exact min_le_right _ _
  · intro g hg x5 hx5
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simp only [cap, List.mem_map] at hx5
    obtain ⟨k, _, rfl⟩ := hx5
    exact min_le_right _ _
  · intro x3 h
    have key := fold_cap x1.gates x3 h
    have hw : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨x1.gates.map cap, min x1.output 24⟩ x3 = x1.wires x3 := key.1
    have hl : (x1.wires x3).length = x3.length + x1.size := key.2
    refine ⟨hw, ?_, hl⟩
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [hw]
    exact getD_cap _ (by omega) _
