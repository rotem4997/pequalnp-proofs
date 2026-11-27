import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3809

open PEqualNP.CircuitLowerBounds

-- Renaming the nine inputs: every reference to an input wire k below 9 is replaced by s k.
-- The two extra inputs and all gate wires keep their numbers, so the gates stay in place.

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

def ren (s : Fin 9 → Fin 9) (k : ℕ) : ℕ := if h : k < 9 then (s ⟨k, h⟩ : ℕ) else k

def reGate (s : Fin 9 → Fin 9) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren s)⟩

lemma getD_ren (s : Fin 9 → Fin 9) (x : Fin 9 → Bool) (t : List Bool) (k : ℕ) :
    (List.ofFn (x ∘ s) ++ t).getD k false = (List.ofFn x ++ t).getD (ren s k) false := by
  unfold ren
  by_cases h : k < 9
  · simp only [h, ↓reduceDIte]
    have h1 : k < (List.ofFn (x ∘ s)).length := by rw [List.length_ofFn]; exact h
    have h2 : (s ⟨k, h⟩ : ℕ) < (List.ofFn x).length := by
      rw [List.length_ofFn]; exact (s ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · simp only [h, ↓reduceDIte]
    have h1 : (List.ofFn (x ∘ s)).length ≤ k := by rw [List.length_ofFn]; omega
    have h2 : (List.ofFn x).length ≤ k := by rw [List.length_ofFn]; omega
    rw [List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
    simp

lemma step_ren (s : Fin 9 → Fin 9) (x : Fin 9 → Bool) (t : List Bool) (g : Gate) :
    stepW (List.ofFn x ++ t) (reGate s g) =
      List.ofFn x ++ (t ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn (x ∘ s) ++ t).getD i false)]) := by
  have hm : ((g.inputs.map (ren s)).map fun i => (List.ofFn x ++ t).getD i false)
      = g.inputs.map fun i => (List.ofFn (x ∘ s) ++ t).getD i false := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => (getD_ren s x t i).symm)
  show (List.ofFn x ++ t) ++
    [g.op.eval ((g.inputs.map (ren s)).map fun i => (List.ofFn x ++ t).getD i false)] = _
  rw [hm, List.append_assoc]

lemma step_orig (s : Fin 9 → Fin 9) (x : Fin 9 → Bool) (t : List Bool) (g : Gate) :
    stepW (List.ofFn (x ∘ s) ++ t) g =
      List.ofFn (x ∘ s) ++ (t ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn (x ∘ s) ++ t).getD i false)]) := by
  show (List.ofFn (x ∘ s) ++ t) ++
    [g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ s) ++ t).getD i false)] = _
  rw [List.append_assoc]

lemma fold_ren (s : Fin 9 → Fin 9) (x : Fin 9 → Bool) (gs : List Gate) :
    ∀ t : List Bool, ∃ t' : List Bool,
      (gs.map (reGate s)).foldl stepW (List.ofFn x ++ t) = List.ofFn x ++ t' ∧
      gs.foldl stepW (List.ofFn (x ∘ s) ++ t) = List.ofFn (x ∘ s) ++ t' := by
  induction gs with
  | nil => intro t; exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    intro t
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_ren, step_orig]
    exact ih _

lemma main (s : Fin 9 → Fin 9) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size ∧
      ∀ (x : Fin 9 → Bool) (b c : Bool),
        D.eval (List.ofFn x ++ [b, c]) = C.eval (List.ofFn (x ∘ s) ++ [b, c]) := by
  refine ⟨⟨C.gates.map (reGate s), ren s C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have := hC g' hg'
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro x b c
    obtain ⟨t', h1, h2⟩ := fold_ren s x C.gates [b, c]
    unfold Circuit.eval
    rw [wires_eq, wires_eq]
    show ((C.gates.map (reGate s)).foldl stepW (List.ofFn x ++ [b, c])).getD (ren s C.output) false
      = (C.gates.foldl stepW (List.ofFn (x ∘ s) ++ [b, c])).getD C.output false
    rw [h1, h2]
    exact (getD_ren s x t' C.output).symm

end PEqualNP.Outside.L_meta_3809

theorem PEqualNP.Outside.L_meta_3809 : ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x2.size ∧ ∀ (x5 : Fin (9 : ℕ) → Bool) (x6 x7 : Bool), x4.eval (List.ofFn x5 ++ [x6, x7]) = x2.eval (List.ofFn (x5 ∘ x1) ++ [x6, x7]) := by
  intro s C hC
  exact PEqualNP.Outside.L_meta_3809.main s C hC
