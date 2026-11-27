import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7455_aux

open PEqualNP.CircuitLowerBounds

theorem fold_pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by simp only [List.foldl]; rw [ht, List.append_assoc]⟩

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl]; rw [ih]; simp; omega

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size := by
  unfold Circuit.wires Circuit.size; exact fold_len _ _

theorem wires_in (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  unfold Circuit.wires
  obtain ⟨t, ht⟩ := fold_pre C.gates (List.ofFn x)
  rw [ht, List.getD_append _ _ _ _ (by simp)]
  simp

end PEqualNP.Outside.L_meta_7455_aux

open PEqualNP.Outside.L_meta_7455_aux in
theorem PEqualNP.Outside.L_meta_7455 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.size = x4.size + (3 : ℕ) ∧ x10.output < x1 + x10.size ∧ (∀ x11 < x1 + x4.size, ∀ (x13 : Fin x1 → Bool), (x10.wires (List.ofFn x13)).getD x11 Bool.false = (x4.wires (List.ofFn x13)).getD x11 Bool.false) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = (x4.eval (List.ofFn x11) || x11 x3 && (x11 x2 || (x4.wires (List.ofFn x11)).getD x5 Bool.false)) := by
  intro x1 x2 x3 x4 x5 hm hr ho h5
  open PEqualNP.CircuitLowerBounds in
  let N := x1 + x4.size
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨x4.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [x2.val, x5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [x3.val, N]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [x4.output, N + 1]⟩], N + 2⟩
  have gd : ∀ (W t : List Bool) (i : ℕ), i < W.length → (W ++ t).getD i false = W.getD i false :=
    fun W t i h => List.getD_append _ _ _ _ h
  have hw : ∀ x : Fin x1 → Bool, C.wires (List.ofFn x) =
      (x4.wires (List.ofFn x)) ++ [(x4.wires (List.ofFn x)).getD x2.val false || (x4.wires (List.ofFn x)).getD x5 false,
        (x4.wires (List.ofFn x)).getD x3.val false && ((x4.wires (List.ofFn x)).getD x2.val false || (x4.wires (List.ofFn x)).getD x5 false),
        (x4.wires (List.ofFn x)).getD x4.output false || ((x4.wires (List.ofFn x)).getD x3.val false && ((x4.wires (List.ofFn x)).getD x2.val false || (x4.wires (List.ofFn x)).getD x5 false))] := by
    intro x
    have hl := wires_len x4 (List.ofFn x)
    simp only [List.length_ofFn] at hl
    show List.foldl _ _ (x4.gates ++ _) = _
    rw [List.foldl_append]
    change List.foldl _ (x4.wires (List.ofFn x)) _ = _
    generalize x4.wires (List.ofFn x) = W at hl ⊢
    simp only [List.foldl, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
    have h2 : x2.val < W.length := by omega
    have h3 : x3.val < W.length := by omega
    have h5 : x5 < W.length := by omega
    have h4 : x4.output < W.length := by omega
    have hN : W.length = N := by omega
    have e1 : ∀ a : Bool, (W ++ [a]).getD N false = a := fun a => by
      rw [← hN]; simp
    have e2 : ∀ a b : Bool, (W ++ [a, b]).getD (N + 1) false = b := fun a b => by
      rw [← hN]; simp
    have e3 : ∀ a : Bool, (W ++ [a]).getD x3.val false = W.getD x3.val false := fun a => gd _ _ _ h3
    have e4 : ∀ a b : Bool, (W ++ [a, b]).getD x4.output false = W.getD x4.output false := fun a b => gd _ _ _ h4
    simp only [e1, e2, e3, e4, PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl | rfl
    · exact hm g hg
    all_goals simp
  · intro j hj i hi
    simp only [C, List.length_append, List.length_cons, List.length_nil] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    simp only [C] at hi
    by_cases hjl : j < x4.gates.length
    · rw [List.getD_append _ _ _ _ hjl] at hi
      have := hr j hjl i hi
      omega
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have hs : x4.size = x4.gates.length := rfl
      have : j - x4.gates.length = 0 ∨ j - x4.gates.length = 1 ∨ j - x4.gates.length = 2 := by omega
      rcases this with h | h | h <;> rw [h] at hi <;> simp at hi <;> omega
  · simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp only [N, C, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_cons, List.length_nil]; omega
  · intro i hi x
    rw [hw x]
    apply gd
    rw [wires_len]; simpa using hi
  · intro x
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [hw x]
    have hl := wires_len x4 (List.ofFn x)
    simp only [List.length_ofFn] at hl
    have e : ∀ (W : List Bool) (a b c : Bool), W.length = N → (W ++ [a, b, c]).getD (N + 2) false = c := by
      intro W a b c h; rw [← h]; simp
    simp only [C]
    rw [e _ _ _ _ hl, wires_in, wires_in]
