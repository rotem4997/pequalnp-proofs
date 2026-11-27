import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3907

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [F, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [F, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem take_getD (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k ≤ gs.length) (i : ℕ) :
    ((gs.take k).foldl F w).getD i false
      = if i < w.length + k then (gs.foldl F w).getD i false else false := by
  have hsplit : gs.foldl F w = (gs.drop k).foldl F ((gs.take k).foldl F w) := by
    rw [← List.foldl_append, List.take_append_drop]
  have hlen : ((gs.take k).foldl F w).length = w.length + k := by
    rw [fold_len, List.length_take]; omega
  split_ifs with h
  · rw [hsplit]
    exact (fold_pre (gs.drop k) _ i (by omega)).symm
  · exact List.getD_eq_default _ _ (by omega)

theorem gate_val (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl F w).getD (w.length + k) false
      = gs[k].op.eval (gs[k].inputs.map fun i =>
          if i < w.length + k then (gs.foldl F w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hk]
  have hlen : ((gs.take k).foldl F w).length = w.length + k := by
    rw [fold_len, List.length_take]; omega
  have e1 : (gs.foldl F w).getD (w.length + k) false
      = gs[k].op.eval (gs[k].inputs.map fun i => ((gs.take k).foldl F w).getD i false) := by
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [fold_pre _ _ _ (by simp only [F, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [F]
    rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i _
  exact take_getD gs w k (le_of_lt hk) i

end PEqualNP.Outside.L_meta_3907

theorem PEqualNP.Outside.L_meta_3907 : have x1 : (Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) → Bool ⊕ Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) (x2 : Bool ⊕ Fin (17 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => Sum.elim id (fun (x4 : Fin (17 : ℕ)) => x1 x4 x3) x2; have x2 : (Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) → Fin (17 : ℕ) → Prop := fun (x2 : Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) (x3 : Fin (17 : ℕ)) => ∃ (x4 : Bool ⊕ Fin (17 : ℕ)) (x5 : Bool ⊕ Fin (17 : ℕ)), (∀ (x6 : Fin (17 : ℕ)), x4 = Sum.inr x6 ∨ x5 = Sum.inr x6 → x6 < x3) ∧ ((∀ (x6 : Fin (9 : ℕ) → Bool), x2 x3 x6 = (x1 x2 x4 x6 && x1 x2 x5 x6)) ∨ ∀ (x6 : Fin (9 : ℕ) → Bool), x2 x3 x6 = (x1 x2 x4 x6 || x1 x2 x5 x6)); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size = (8 : ℕ) → ∀ (x6 : Fin (17 : ℕ)), (9 : ℕ) < ↑x6 → x2 (fun (x8 : Fin (17 : ℕ)) (x9 : Fin (9 : ℕ) → Bool) => (x3.wires (List.ofFn x9)).getD (↑x8) Bool.false) x6 := by
  intro x1 x2 C hm hs x6 hx6
  simp only [x1, x2]
  set W : (Fin 9 → Bool) → List Bool := fun y => C.wires (List.ofFn y) with hW
  have hk : x6.val - 9 < C.gates.length := by
    have := x6.isLt
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hs
    omega
  set g := C.gates[x6.val - 9] with hg
  have hgm : g ∈ C.gates := List.getElem_mem hk
  obtain ⟨hop, hlen⟩ := hm g hgm
  have hval : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD x6.val false
      = g.op.eval (g.inputs.map fun i => if i < x6.val then (C.wires (List.ofFn y)).getD i false else false) := by
    intro y
    have e := PEqualNP.Outside.L_meta_3907.gate_val C.gates (List.ofFn y) (x6.val - 9) hk
    simp only [List.length_ofFn] at e
    have h9 : 9 + (x6.val - 9) = x6.val := by omega
    rw [h9] at e
    exact e
  let tok : ℕ → Bool ⊕ Fin 17 := fun i => if h : i < x6.val then Sum.inr ⟨i, by omega⟩ else Sum.inl false
  have htok : ∀ (i : ℕ) (y : Fin 9 → Bool),
      Sum.elim id (fun x4 : Fin 17 => (C.wires (List.ofFn y)).getD x4.val false) (tok i)
        = if i < x6.val then (C.wires (List.ofFn y)).getD i false else false := by
    intro i y
    by_cases h : i < x6.val
    · simp [tok, h]
    · simp [tok, h]
  have htokl : ∀ (i : ℕ) (z : Fin 17), tok i = Sum.inr z → z < x6 := by
    intro i z hz
    by_cases h : i < x6.val
    · simp only [tok, h, dite_true, Sum.inr.injEq] at hz
      subst hz
      exact h
    · simp [tok, h] at hz
  have hop' : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    simpa using hop
  rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop' with ho | ho
    · refine ⟨Sum.inl true, Sum.inl true, by simp, Or.inl ?_⟩
      intro y
      rw [hval y, hinp, ho]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · refine ⟨Sum.inl false, Sum.inl false, by simp, Or.inr ?_⟩
      intro y
      rw [hval y, hinp, ho]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · refine ⟨tok a, tok a, ?_, ?_⟩
    · intro z hz
      rcases hz with hz | hz <;> exact htokl a z hz
    · rcases hop' with ho | ho
      · left
        intro y
        rw [hval y, hinp, ho, htok a y]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      · right
        intro y
        rw [hval y, hinp, ho, htok a y]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · refine ⟨tok a, tok b, ?_, ?_⟩
    · intro z hz
      rcases hz with hz | hz
      · exact htokl a z hz
      · exact htokl b z hz
    · rcases hop' with ho | ho
      · left
        intro y
        rw [hval y, hinp, ho, htok a y, htok b y]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      · right
        intro y
        rw [hval y, hinp, ho, htok a y, htok b y]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · rw [hinp] at hlen
    simp at hlen
