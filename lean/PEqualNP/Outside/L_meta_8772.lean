import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8772

/-! With no gates the circuit outputs a single input bit (or false); some incident pair
input has that bit off, so the circuit rejects an input it must accept. -/

end PEqualNP.Outside.L_meta_8772

theorem PEqualNP.Outside.L_meta_8772 :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Bool) (x6 : List Bool), x2 x5 x6 → x3.eval x6 = x5) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x3 (1 : ℕ) → x3.gates = [] → (64 : ℕ) ≤ x3.size := by
  dsimp only
  intro x3 _ hc _ hg
  have key : ∀ l : List Bool, x3.eval l = l.getD x3.output false := by
    intro l
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hg]
  have hpair : ∀ j : Fin 26, ∃ a b : Fin 13, a - b ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      ((List.ofFn fun x6 : Fin 13 => decide (x6 = a)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = b)).getD j.val false = false := by
    decide
  obtain ⟨a, b, hab, hz⟩ : ∃ a b : Fin 13, a - b ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      ((List.ofFn fun x6 : Fin 13 => decide (x6 = a)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = b)).getD x3.output false = false := by
    by_cases ho : x3.output < 26
    · exact hpair ⟨x3.output, ho⟩
    · refine ⟨0, 0, by decide, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  have h := hc true _ (by rw [if_pos rfl]; exact ⟨a, b, hab, rfl⟩)
  rw [key, hz] at h
  exact absurd h (by decide)
