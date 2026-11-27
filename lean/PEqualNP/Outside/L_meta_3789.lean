import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3789_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge

theorem inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    (gs.foldl (orStep n) []).length = gs.length ∧
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = n + gs.length ∧
    ∀ k g, g ∈ (gs.foldl (orStep n) []).getD k [] → g ≤ k ∧
      ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
          (n + g) false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
          (n + k) false = true) := by
  refine List.reverseRecOn gs ?_ ?_
  · refine ⟨by simp, by simp [hx], ?_⟩
    intro k g h
    simp at h
  · intro gs a ih
    rw [List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize hcs : gs.foldl (orStep n) [] = cs at ih ⊢
    generalize hws : gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      = ws at ih ⊢
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨by simp [orStep, h1], by simp [h2]; omega, ?_⟩
    intro k g hg
    unfold orStep at hg
    rcases Nat.lt_trichotomy k cs.length with hk | hk | hk
    · rw [List.getD_append _ _ _ _ hk] at hg
      obtain ⟨hgk, himp⟩ := h3 k g hg
      refine ⟨hgk, ?_⟩
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact himp
    · subst hk
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hg
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons] at hg
      rcases hg with hg | hg
      · subst hg
        exact ⟨le_refl _, fun h => h⟩
      · split_ifs at hg with hop
        · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hg
          obtain ⟨w, ⟨hw, hw1, hw2⟩, hgw⟩ := hg
          obtain ⟨hgk, himp⟩ := h3 (w - n) g hgw
          refine ⟨by omega, ?_⟩
          rw [List.getD_append _ _ _ _ (by omega)]
          intro hgt
          have hwt := himp hgt
          rw [show n + (w - n) = w by omega] at hwt
          rw [List.getD_append_right _ _ _ _ (by omega)]
          rw [show n + cs.length - ws.length = 0 by omega]
          simp only [List.getD_cons_zero, hop, GateOp.eval, List.any_map, List.any_eq_true]
          exact ⟨w, hw, hwt⟩
        · simp at hg
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hg
      simp at hg

end PEqualNP.Outside.L_meta_3789_aux

theorem PEqualNP.Outside.L_meta_3789 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List Bool), x5.length = x1 → PEqualNP.CleanedNonEdge.OrReaches x1 x2 x4 x3 → (x2.wires x5).getD (x1 + x3) Bool.false = Bool.true → (x2.wires x5).getD x4 Bool.false = Bool.true := by
  intro n C g w x hx hr hg
  obtain ⟨hnw, hmem⟩ := hr
  have h := (PEqualNP.Outside.L_meta_3789_aux.inv n x hx C.gates).2.2 (w - n) g hmem
  have h2 := h.2 hg
  rw [show n + (w - n) = w by omega] at h2
  exact h2
