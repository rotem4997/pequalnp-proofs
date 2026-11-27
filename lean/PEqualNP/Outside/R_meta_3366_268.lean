import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A cut of step L-meta-3366 by the operation of the next gate.
-- A circuit of at most 13 gates on the 11 wires of the step is either empty, or a first gate
-- (AND, OR or NOT of at most two wires) followed by a circuit of at most 12 gates on 12 wires.
-- The empty circuit is the case of a first gate that is never read.
theorem PEqualNP.Outside.R_meta_3366_268
    (hand : ∀ (l : List ℕ), l.length ≤ 2 → ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      (∀ (x5 : Fin (9 : ℕ) → Bool), D.eval ((List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (l.map fun i : ℕ => (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]).getD i false)]) =
        ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (p : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 p.1 && x5 p.2)) → False)
    (hor : ∀ (l : List ℕ), l.length ≤ 2 → ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      (∀ (x5 : Fin (9 : ℕ) → Bool), D.eval ((List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (l.map fun i : ℕ => (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]).getD i false)]) =
        ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (p : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 p.1 && x5 p.2)) → False)
    (hnot : ∀ (l : List ℕ), l.length ≤ 2 → ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 12 →
      (∀ (x5 : Fin (9 : ℕ) → Bool), D.eval ((List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (l.map fun i : ℕ => (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]).getD i false)]) =
        ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (p : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 p.1 && x5 p.2)) → False)
    :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  show ∀ (x2 : Circuit), FanInTwo x2 → x2.size ≤ 13 → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (p : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 p.1 && x5 p.2)) → False
  intro C hF hs hC
  have len : ∀ x5 : Fin (9 : ℕ) → Bool, (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]).length = 11 := by
    intro x5
    simp
  rcases hg : C.gates with _ | ⟨g, gs⟩
  · -- no gate at all: the output is one of the wires of the step, or reads nothing
    have ev : ∀ w : List Bool, C.eval w = w.getD C.output false := by
      intro w
      show (List.foldl _ w C.gates).getD C.output false = w.getD C.output false
      rw [hg]
      rfl
    have fan : ∀ o : ℕ, FanInTwo ⟨[], o⟩ := by
      intro o g' hg'
      exact absurd hg' (List.not_mem_nil)
    rcases Nat.lt_or_ge C.output 11 with ho | ho
    · refine hnot [] (Nat.zero_le _) ⟨[], C.output⟩ (fan _) (Nat.zero_le _) ?_
      intro x5
      rw [← hC x5, ev]
      show ((List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) ++ [_]).getD C.output false = _
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [len]; exact ho)]
    · refine hnot [] (Nat.zero_le _) ⟨[], C.output + 1⟩ (fan _) (Nat.zero_le _) ?_
      intro x5
      rw [← hC x5, ev]
      show ((List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) ++ [_]).getD (C.output + 1) false = _
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_append, len]; show 11 + 1 ≤ C.output + 1; omega),
        List.getElem?_eq_none (by rw [len]; exact ho)]
  · -- a first gate g, then the gates gs
    have hgm : g ∈ C.gates := by
      rw [hg]
      exact List.mem_cons_self
    have hFD : FanInTwo ⟨gs, C.output⟩ := by
      intro g' hg'
      exact hF g' (by rw [hg]; exact List.mem_cons_of_mem _ hg')
    have hsD : (⟨gs, C.output⟩ : Circuit).size ≤ 12 := by
      have h1 : C.size = gs.length + 1 := by
        show C.gates.length = gs.length + 1
        rw [hg]
        rfl
      show gs.length ≤ 12
      omega
    have ev : ∀ w : List Bool, C.eval w =
        (⟨gs, C.output⟩ : Circuit).eval (w ++ [g.op.eval (g.inputs.map fun i : ℕ => w.getD i false)]) := by
      intro w
      show (List.foldl _ w C.gates).getD C.output false =
        (List.foldl _ (w ++ [g.op.eval (g.inputs.map fun i : ℕ => w.getD i false)]) gs).getD C.output false
      rw [hg]
      rfl
    have hop := (hF g hgm).1
    have hlen := (hF g hgm).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · refine hand g.inputs hlen ⟨gs, C.output⟩ hFD hsD ?_
      intro x5
      rw [← h, ← ev]
      exact hC x5
    · refine hor g.inputs hlen ⟨gs, C.output⟩ hFD hsD ?_
      intro x5
      rw [← h, ← ev]
      exact hC x5
    · refine hnot g.inputs hlen ⟨gs, C.output⟩ hFD hsD ?_
      intro x5
      rw [← h, ← ev]
      exact hC x5
