import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2746

private lemma L (x : Fin 9 → Bool) (v : Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn x ++ [v]).getD i false = x ⟨i, hi⟩ := by
  interval_cases i <;> simp [List.getD_eq_getElem?_getD]

private lemma L9 (x : Fin 9 → Bool) (v : Bool) :
    (List.ofFn x ++ [v]).getD 9 false = v := by
  simp [List.getD_eq_getElem?_getD]

private lemma Lout (x : Fin 9 → Bool) (v : Bool) (i : ℕ) (hi : 9 < i) :
    (List.ofFn x ++ [v]).getD i false = false := by
  apply List.getD_eq_default
  simp
  omega

private theorem aux (f : (Fin 9 → Bool) → Bool)
    (hf0 : ∀ i : Fin 9, f (fun j => decide (j = i)) = false)
    (hf01 : f (fun j => decide (j = 0 ∨ j = 1)) = true)
    (C : Circuit)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6))
    (hf : circuitFun 9 C = f)
    (hno : ¬∃ g : Gate, C.gates[1]? = some g) : False := by
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil =>
    have h := h9 (fun _ => true)
    rw [show (Circuit.wires ⟨[], out⟩ (List.ofFn fun _ : Fin 9 => true))
      = List.ofFn (fun _ : Fin 9 => true) from rfl, List.getD_eq_default _ _ (by simp)] at h
    simp at h
  | cons g rest =>
    cases rest with
    | cons g2 r => exact hno ⟨g2, by simp⟩
    | nil =>
      have hw : ∀ x : Fin 9 → Bool, Circuit.wires ⟨[g], out⟩ (List.ofFn x)
          = List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)] :=
        fun x => rfl
      have hv : ∀ x : Fin 9 → Bool,
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
        intro x
        have := h9 x
        rw [hw, L9] at this
        exact this
      have hE : ∀ x : Fin 9 → Bool, (List.ofFn x ++ [(x 4 || x 6)]).getD out false = f x := by
        intro x
        have := congrFun hf x
        simp only [circuitFun, Circuit.eval] at this
        rw [hw, hv] at this
        exact this
      rcases Nat.lt_trichotomy out 9 with h | h | h
      · have := hE (fun j => decide (j = ⟨out, h⟩))
        rw [L _ _ _ h, hf0] at this
        simp at this
      · subst h
        have := hE (fun j => decide (j = 4))
        rw [L9, hf0] at this
        simp at this
      · have := hE (fun j => decide (j = 0 ∨ j = 1))
        rw [Lout _ _ _ h, hf01] at this
        simp at this

end PEqualNP.Outside.L_meta_2746

theorem PEqualNP.Outside.L_meta_2746 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (¬∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C _ h9 hf hno
  exact (PEqualNP.Outside.L_meta_2746.aux _ (by decide) (by decide) C h9 hf hno).elim
