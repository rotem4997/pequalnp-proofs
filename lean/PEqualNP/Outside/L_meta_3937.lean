import Mathlib
import PEqualNP.Defs

-- With no second gate the circuit is its first gate OR(x0, x1) on the inputs, so its output is an
-- input, that OR, or a missing wire; none of these is the edge function.
namespace PEqualNP.Outside.L_meta_3937
open PEqualNP.CircuitLowerBounds

theorem wires_one (g : Gate) (o : ℕ) (w : List Bool) :
    (Circuit.mk [g] o).wires w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

end PEqualNP.Outside.L_meta_3937

theorem PEqualNP.Outside.L_meta_3937 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size := by
  intro C _ hw9 hf _ hnone
  exfalso
  obtain ⟨gs, o⟩ := C
  have hlen : gs.length ≤ 1 := by
    have h : gs[1]? = none := hnone
    rw [List.getElem?_eq_none_iff] at h; omega
  match gs, hlen with
  | [], _ =>
    have h := hw9 (fun _ => true)
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires] at h
  | [g], _ =>
    have hv : ∀ y : Fin 9 → Bool,
        g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) = (y 0 || y 1) := by
      intro y
      have h := hw9 y
      rw [PEqualNP.Outside.L_meta_3937.wires_one, List.getD_append_right _ _ _ _ (by simp)] at h
      simpa using h
    have hf' : ∀ y : Fin 9 → Bool, (List.ofFn y ++ [y 0 || y 1]).getD o false =
        PEqualNP.MetaComplexity.circuitFun 9 ⟨[g], o⟩ y := by
      intro y
      show _ = ((PEqualNP.CircuitLowerBounds.Circuit.mk [g] o).wires (List.ofFn y)).getD o false
      rw [PEqualNP.Outside.L_meta_3937.wires_one, hv y]
    rw [hf] at hf'
    by_cases ho : o < 9
    · have h := hf' (fun i => decide (i.val = o))
      rw [List.getD_append _ _ _ _ (by simpa using ho),
        List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn] at h
      interval_cases o <;> simp (config := {decide := true}) at h
    · by_cases h9 : o = 9
      · subst h9
        have h := hf' (fun i => decide (i.val = 0))
        rw [List.getD_append_right _ _ _ _ (by simp)] at h
        revert h; decide
      · have h := hf' (fun _ => true)
        rw [List.getD_eq_default _ _ (by simp; omega)] at h
        revert h; decide
