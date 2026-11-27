import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1926

open PEqualNP.CircuitLowerBounds

theorem wires_prefix (gs : List Gate) (o : ℕ) (w : List Bool) :
    ∃ t : List Bool, (Circuit.mk gs o).wires w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [Circuit.wires]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
    have hw : (Circuit.mk (g :: gs) o).wires w =
        (Circuit.mk gs o).wires (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [hw, ht]
    simp

theorem getD_nine (x : Fin 9 → Bool) (v : Bool) (t : List Bool) :
    (List.ofFn x ++ [v] ++ t).getD 9 false = v := by
  rw [List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_1926

theorem PEqualNP.Outside.L_meta_1926 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)))) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size + (1 : ℕ) = x1.size ∧ ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ))]) = x1.eval (List.ofFn x5) := by
  intro C hC hfirst
  obtain ⟨gates, o⟩ := C
  cases gates with
  | nil =>
    exfalso
    have h := hfirst (fun _ => true)
    simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil] at h
    exact absurd h (by decide)
  | cons g gs =>
    refine ⟨⟨gs, o⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      exact hC g' (List.mem_cons_of_mem _ hg')
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro x
      have h := hfirst x
      have hw : (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) o).wires (List.ofFn x) =
          (PEqualNP.CircuitLowerBounds.Circuit.mk gs o).wires
            (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) := rfl
      obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_1926.wires_prefix gs o
        (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])
      have hv : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 4) := by
        rw [hw, ht, PEqualNP.Outside.L_meta_1926.getD_nine] at h
        exact h
      show ((PEqualNP.CircuitLowerBounds.Circuit.mk gs o).wires _).getD o false =
        ((PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) o).wires _).getD o false
      rw [hw, hv]
