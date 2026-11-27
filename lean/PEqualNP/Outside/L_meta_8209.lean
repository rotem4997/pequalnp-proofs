import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8209_aux

open PEqualNP.CircuitLowerBounds

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem step (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (w w' : List Bool) (k : ℕ) (v : Bool)
    (hw : w.length = x1 + k) (hw' : w'.length = x2 + k)
    (h : ∀ i, w'.getD (f i) false = w.getD i false) (i : ℕ) :
    (w' ++ [v]).getD (f i) false = (w ++ [v]).getD i false := by
  have hi := h i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at hi ⊢
  by_cases c : i < x1
  · have := hf1 i c
    have a1 : f i < w'.length := by omega
    have a2 : i < w.length := by omega
    simp only [a1, a2, if_true]
    exact hi
  · have e := hf2 i (by omega)
    by_cases d : i < x1 + k
    · have a1 : f i < w'.length := by omega
      have a2 : i < w.length := by omega
      simp only [a1, a2, if_true]
      exact hi
    · have a1 : ¬ f i < w'.length := by omega
      have a2 : ¬ i < w.length := by omega
      have a3 : f i - w'.length = i - w.length := by omega
      simp only [a1, a2, if_false, a3]

theorem main (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (gs : List Gate) :
    ∀ (w w' : List Bool) (k : ℕ), w.length = x1 + k → w'.length = x2 + k →
    (∀ i, w'.getD (f i) false = w.getD i false) → ∀ i,
    ((gs.map (rg f)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (f i) false
    = (gs.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs with
  | nil => intro w w' k _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' k hw hw' h i
    simp only [List.map_cons, List.foldl_cons]
    have e : (rg f g).op.eval ((rg f g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    rw [e]
    apply ih _ _ (k + 1)
    · simp [hw]; omega
    · simp [hw']; omega
    · exact step x1 x2 f hf1 hf2 w w' k _ hw hw' h

theorem pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, by rw [List.foldl_cons, ht]; simp⟩

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl]; rw [ih]; simp; omega

def ng (B fo : ℕ) : List Gate :=
  [⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 20]⟩, ⟨GateOp.or, [B, B + 1]⟩, ⟨GateOp.and, [0, B + 2]⟩,
   ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [B + 4, B + 5]⟩, ⟨GateOp.and, [1, B + 6]⟩,
   ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [B + 8, B + 9]⟩, ⟨GateOp.and, [6, B + 10]⟩,
   ⟨GateOp.or, [B + 3, B + 7]⟩, ⟨GateOp.or, [B + 12, B + 11]⟩, ⟨GateOp.or, [fo, B + 13]⟩]

theorem tail (W : List Bool) (fo : ℕ) (hfo : fo < W.length) (h21 : 21 ≤ W.length) :
    ((ng W.length fo).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD (W.length + 14) false
    = (W.getD fo false || (((W.getD 0 false && ((W.getD 9 false || W.getD 10 false) || (W.getD 14 false || W.getD 20 false)))
      || (W.getD 1 false && ((W.getD 9 false || W.getD 11 false) || (W.getD 12 false || W.getD 16 false))))
      || (W.getD 6 false && ((W.getD 9 false || W.getD 15 false) || (W.getD 17 false || W.getD 18 false))))) := by
  simp (disch := omega) only [ng, List.foldl, GateOp.eval, List.map, List.append_assoc, List.cons_append, List.nil_append,
    List.getD_append, List.getD_append_right, Nat.add_sub_cancel_left, Nat.sub_self, List.getD_cons_zero,
    List.getD_cons_succ, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]

end PEqualNP.Outside.L_meta_8209_aux

open PEqualNP.Outside.L_meta_8209_aux in
theorem PEqualNP.Outside.L_meta_8209 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (17 : ℕ) + x1.size → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.output < (21 : ℕ) + x4.size ∧ x4.size ≤ x1.size + (15 : ℕ) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)))) = (x1.eval (List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (9 : ℕ), (10 : ℕ), (13 : ℕ), (14 : ℕ)])) (List.finRange (26 : ℕ)))) || (x5 (2 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (15 : Fin (26 : ℕ)) || (x5 (19 : Fin (26 : ℕ)) || x5 (25 : Fin (26 : ℕ)))) || x5 (4 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (16 : Fin (26 : ℕ)) || (x5 (17 : Fin (26 : ℕ)) || x5 (21 : Fin (26 : ℕ)))) || x5 (10 : Fin (26 : ℕ)) && (x5 (14 : Fin (26 : ℕ)) || x5 (20 : Fin (26 : ℕ)) || (x5 (22 : Fin (26 : ℕ)) || x5 (23 : Fin (26 : ℕ)))))) := by
  intro x1 hm hout
  let f : ℕ → ℕ := fun i => if i < 4 then i + 2 else if i < 6 then i + 3 else i + 4
  have hf1 : ∀ i, i < 17 → f i < 21 := by
    intro i hi; simp only [f]; split_ifs <;> omega
  have hf2 : ∀ i, 17 ≤ i → f i = i - 17 + 21 := by
    intro i hi; simp only [f]; split_ifs <;> omega
  refine ⟨⟨x1.gates.map (rg f) ++ ng (21 + x1.size) (f x1.output), 21 + x1.size + 14⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | hg
    · have := hm g0 hg0
      simpa [rg] using this
    · simp only [ng, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, ng]; omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, ng]
  · intro x5
    have e21 : List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)))
        = [x5 2, x5 4, x5 5, x5 6, x5 7, x5 8, x5 10, x5 11, x5 12, x5 14, x5 15, x5 16, x5 17, x5 18, x5 19, x5 20, x5 21, x5 22, x5 23, x5 24, x5 25] := by
      rfl
    have e17 : List.map x5 (List.filter (fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (9 : ℕ), (10 : ℕ), (13 : ℕ), (14 : ℕ)])) (List.finRange (26 : ℕ)))
        = [x5 5, x5 6, x5 7, x5 8, x5 11, x5 12, x5 15, x5 16, x5 17, x5 18, x5 19, x5 20, x5 21, x5 22, x5 23, x5 24, x5 25] := by
      rfl
    rw [e21, e17]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_append]
    have hh : ∀ i, [x5 2, x5 4, x5 5, x5 6, x5 7, x5 8, x5 10, x5 11, x5 12, x5 14, x5 15, x5 16, x5 17, x5 18, x5 19, x5 20, x5 21, x5 22, x5 23, x5 24, x5 25].getD (f i) false
        = [x5 5, x5 6, x5 7, x5 8, x5 11, x5 12, x5 15, x5 16, x5 17, x5 18, x5 19, x5 20, x5 21, x5 22, x5 23, x5 24, x5 25].getD i false := by
      intro i
      by_cases c : i < 17
      · interval_cases i <;> rfl
      · rw [hf2 i (by omega)]
        rw [List.getD_eq_default _ _ (by simp; try omega), List.getD_eq_default _ _ (by simp; try omega)]
    have hmain := main 17 21 f hf1 hf2 x1.gates _ _ 0 (by simp) (by simp) hh x1.output
    obtain ⟨t, ht⟩ := pre (x1.gates.map (rg f)) [x5 2, x5 4, x5 5, x5 6, x5 7, x5 8, x5 10, x5 11, x5 12, x5 14, x5 15, x5 16, x5 17, x5 18, x5 19, x5 20, x5 21, x5 22, x5 23, x5 24, x5 25]
    have hl := fold_len (x1.gates.map (rg f)) [x5 2, x5 4, x5 5, x5 6, x5 7, x5 8, x5 10, x5 11, x5 12, x5 14, x5 15, x5 16, x5 17, x5 18, x5 19, x5 20, x5 21, x5 22, x5 23, x5 24, x5 25]
    simp only [List.length_cons, List.length_nil, List.length_map] at hl
    generalize hW : List.foldl _ _ (List.map (rg f) x1.gates) = W at hmain ht hl ⊢
    have hs : 21 + x1.size = W.length := by rw [hl]; simp [PEqualNP.CircuitLowerBounds.Circuit.size]; try omega
    rw [hs]
    have hfo : f x1.output < W.length := by
      rw [← hs]
      by_cases c : x1.output < 17
      · have := hf1 x1.output c; omega
      · have := hf2 x1.output (by omega); omega
    rw [tail W (f x1.output) hfo (by omega), hmain]
    subst ht
    simp (disch := simp) only [List.getD_append]
    rfl
