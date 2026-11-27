import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8079 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       (∀ (x5 : Fin (10 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];           x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) = (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5) →         PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) (19 : ℕ) := by
  intro C k hfan hsize hC
  refine ⟨⟨⟨GateOp.and, [0, 2]⟩ :: ⟨GateOp.not, [k.val]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact hfan g hg
  · simp only [Circuit.size, List.length_cons] at hsize ⊢
    omega
  · intro x
    have h := hC x
    dsimp only at h
    have h0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
    have h2 : (List.ofFn x).getD 2 false = x 2 := by simp [List.getD_eq_getElem?_getD]
    have hv1 : GateOp.and.eval ([0, 2].map fun i => (List.ofFn x).getD i false) = (x 0 && x 2) := by
      simp only [List.map_cons, List.map_nil, h0, h2, GateOp.eval, List.all_cons, List.all_nil, id,
        Bool.and_true]
    show C.eval ((List.ofFn x ++ [GateOp.and.eval ([0, 2].map fun i => (List.ofFn x).getD i false)]) ++
      [GateOp.not.eval ([k.val].map fun i =>
        (List.ofFn x ++ [GateOp.and.eval ([0, 2].map fun i => (List.ofFn x).getD i false)]).getD i false)]) = _
    rw [hv1]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    exact h
