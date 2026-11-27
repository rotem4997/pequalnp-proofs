import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4001_aux

open PEqualNP.CircuitLowerBounds

def rw (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (i : ℕ) : ℕ :=
  if h : i < x1 then (x3 ⟨i, h⟩).val else i - x1 + x2

def rg (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rw x1 x2 x3)⟩

theorem key (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x : Fin x2 → Bool) (v : List Bool) (i : ℕ) :
    (List.ofFn (fun j : Fin x1 => x (x3 j)) ++ v).getD i false
      = (List.ofFn x ++ v).getD (rw x1 x2 x3 i) false := by
  unfold rw
  by_cases h : i < x1
  · have h2 : (x3 ⟨i, h⟩).val < x2 := (x3 ⟨i, h⟩).isLt
    rw [dif_pos h,  List.getD_append _ _ _ _ (by simpa using h),
      List.getD_append _ _ _ _ (by simpa using h2)]
    simp [List.getD_eq_getElem?_getD, h, h2]
  · rw [dif_neg h, List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp)]
    simp

theorem fold (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x : Fin x2 → Bool) (gs : List Gate) :
    ∀ v : List Bool, ∃ v' : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn (fun j : Fin x1 => x (x3 j)) ++ v)
        = List.ofFn (fun j : Fin x1 => x (x3 j)) ++ v' ∧
      (gs.map (rg x1 x2 x3)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x ++ v)
        = List.ofFn x ++ v' := by
  induction gs with
  | nil => intro v; exact ⟨v, rfl, rfl⟩
  | cons g gs ih =>
    intro v
    obtain ⟨v', h1, h2⟩ := ih (v ++ [g.op.eval (g.inputs.map fun i =>
      (List.ofFn (fun j : Fin x1 => x (x3 j)) ++ v).getD i false)])
    refine ⟨v', ?_, ?_⟩
    · rw [List.foldl_cons, List.append_assoc]; exact h1
    · rw [List.map_cons, List.foldl_cons, List.append_assoc]
      have e : (rg x1 x2 x3 g).op.eval ((rg x1 x2 x3 g).inputs.map fun i =>
          (List.ofFn x ++ v).getD i false)
          = g.op.eval (g.inputs.map fun i =>
            (List.ofFn (fun j : Fin x1 => x (x3 j)) ++ v).getD i false) := by
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact (key x1 x2 x3 x v i).symm
      rw [e]; exact h2

end PEqualNP.Outside.L_meta_4001_aux

open PEqualNP.Outside.L_meta_4001_aux in
theorem PEqualNP.Outside.L_meta_4001 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : (Fin x1 → Bool) → Bool) (x5 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x5 → PEqualNP.MetaComplexity.HasCircuitSize x2 (fun (x7 : Fin x2 → Bool) => x4 fun (x8 : Fin x1) => x7 (x3 x8)) x5 := by
  intro x1 x2 x3 x4 x5 h
  obtain ⟨C, hF, hs, hC⟩ := h
  refine ⟨⟨C.gates.map (rg x1 x2 x3), rw x1 x2 x3 C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hF g0 hg0
    simpa [rg] using this
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hs
  · intro x
    show _ = x4 (fun x8 => x (x3 x8))
    rw [← hC]
    obtain ⟨v', h1, h2⟩ := fold x1 x2 x3 x C.gates []
    simp only [List.append_nil] at h1 h2
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [h1]
    simp only []
    rw [h2]
    exact (key x1 x2 x3 x v' C.output).symm
