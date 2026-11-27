import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8409_aux

open PEqualNP.CircuitLowerBounds

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def og (p : ℕ × ℕ) : Gate := ⟨GateOp.or, [p.1, p.2]⟩

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
    simp only [a1, a2, ite_true]
    exact hi
  · have e := hf2 i (by omega)
    by_cases d : i < x1 + k
    · have a1 : f i < w'.length := by omega
      have a2 : i < w.length := by omega
      simp only [a1, a2, ite_true]
      exact hi
    · have a1 : ¬ f i < w'.length := by omega
      have a2 : ¬ i < w.length := by omega
      have a3 : f i - w'.length = i - w.length := by omega
      simp only [a1, a2, ite_false, a3]

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

theorem orfold (ps : List (ℕ × ℕ)) (w : List Bool) :
    ∀ u : List Bool, (∀ p ∈ ps, p.1 < w.length ∧ p.2 < w.length) →
    (ps.map og).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w ++ u)
    = w ++ u ++ ps.map (fun p => w.getD p.1 false || w.getD p.2 false) := by
  induction ps with
  | nil => intro u _; simp
  | cons p ps ih =>
    intro u hp
    have h1 := hp p (by simp)
    simp only [List.map_cons, List.foldl_cons]
    have e : (og p).op.eval ((og p).inputs.map fun i => (w ++ u).getD i false)
        = (w.getD p.1 false || w.getD p.2 false) := by
      simp [og, GateOp.eval, List.getElem?_append_left h1.1, List.getElem?_append_left h1.2]
    rw [e, List.append_assoc, ih (u ++ [_]) (fun q hq => hp q (by simp [hq]))]
    simp

end PEqualNP.Outside.L_meta_8409_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8409_aux in
theorem PEqualNP.Outside.L_meta_8409 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x1 × Fin x1) (x5 : Fin x3 → Fin (x1 + x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x3 x6 → x6.output < x3 + x6.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.output < x1 + x10.size ∧ x10.size ≤ x2 + x6.size ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn fun (x12 : Fin x3) => Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2) (x5 x12)) := by
  intro x1 x2 x3 x4 x5 x6 hm hr hout
  let f : ℕ → ℕ := fun i => if h : i < x3 then (x5 ⟨i, h⟩).val else i - x3 + (x1 + x2)
  have hf1 : ∀ i, i < x3 → f i < x1 + x2 := by
    intro i hi; simp only [f, dif_pos hi]; exact (x5 ⟨i, hi⟩).isLt
  have hf2 : ∀ i, x3 ≤ i → f i = i - x3 + (x1 + x2) := by
    intro i hi; simp only [f, dif_neg (show ¬ i < x3 by omega)]
  let ps : List (ℕ × ℕ) := List.ofFn fun k : Fin x2 => ((x4 k).1.val, (x4 k).2.val)
  have hps : ps.length = x2 := by simp [ps]
  refine ⟨⟨ps.map og ++ x6.gates.map (rg f), f x6.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨p, _, rfl⟩ | ⟨g0, hg0, rfl⟩
    · simp [og]
    · have := hm g0 hg0
      simpa [rg] using this
  · intro j hj i hi
    simp only [List.length_append, List.length_map, hps] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ (by simp [hps]; omega)] at hi
    by_cases c : j < x2
    · rw [List.getElem_append_left (by simp [hps]; omega)] at hi
      simp [ps, og] at hi
      rcases hi with rfl | rfl
      · have := (x4 ⟨j, c⟩).1.isLt; omega
      · have := (x4 ⟨j, c⟩).2.isLt; omega
    · rw [List.getElem_append_right (by simp [hps]; omega)] at hi
      simp only [List.getElem_map, rg, List.mem_map, List.length_map, hps] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      have hj2 : j - x2 < x6.gates.length := by omega
      have hb := hr (j - x2) hj2 a (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hj2]; exact ha)
      by_cases d : a < x3
      · have := hf1 a d; omega
      · have := hf2 a (by omega); omega
  · show f x6.output < x1 + (ps.map og ++ x6.gates.map (rg f)).length
    simp only [List.length_append, List.length_map, hps]
    simp only [Circuit.size] at hout
    by_cases d : x6.output < x3
    · have := hf1 x6.output d; omega
    · have := hf2 x6.output (by omega); omega
  · simp [Circuit.size, hps]
  · intro x11
    unfold Circuit.eval Circuit.wires
    simp only [List.foldl_append]
    have hW : (ps.map og).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x11)
        = List.ofFn (Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2)) := by
      have := orfold ps (List.ofFn x11) [] (by
        intro p hp
        simp only [ps, List.mem_ofFn] at hp
        obtain ⟨k, rfl⟩ := hp
        simp)
      rw [List.append_nil] at this
      rw [this, show Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2)
        = Fin.append x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2) from rfl, List.ofFn_fin_append]
      congr 1
      simp [ps, List.map_ofFn, List.getD_eq_getElem?_getD, Function.comp_def]
    rw [hW]
    refine main x3 (x1 + x2) f hf1 hf2 x6.gates _ _ 0 (by simp) (by simp) ?_ x6.output
    intro i
    by_cases c : i < x3
    · simp only [f, dif_pos c]
      simp [List.getD_eq_getElem?_getD, c]
    · rw [hf2 i (by omega)]
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
