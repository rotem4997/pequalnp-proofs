import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8425

def P (x2 : Fin (14 : ℕ) → Bool) : Bool :=
  decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true)

def inp (x3 x4 : ℕ) (x5 : Fin (14 : ℕ)) : Bool :=
  x3.testBit (↑x5 / (7 : ℕ) * (7 : ℕ) + (↑x5 % (7 : ℕ) + x4) % (7 : ℕ))

def chkB : Bool :=
  decide (∀ s : Fin 7, (∀ m ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ)], P (inp m s) = true) ∧
    ∀ m ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], P (inp m s) = false)

theorem chkB_true : chkB = true := by decide +kernel

theorem chk : ∀ s : Fin 7, (∀ m ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ)], P (inp m s) = true) ∧
    ∀ m ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], P (inp m s) = false :=
  of_decide_eq_true chkB_true

end PEqualNP.Outside.L_meta_8425

theorem PEqualNP.Outside.L_meta_8425 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) →     have x3 : ℕ → ℕ → Fin (14 : ℕ) → Bool := fun (x3 x4 : ℕ) (x5 : Fin (14 : ℕ)) => x3.testBit (↑x5 / (7 : ℕ) * (7 : ℕ) + (↑x5 % (7 : ℕ) + x4) % (7 : ℕ));     ∀ x4 < (7 : ℕ), (∀ x6 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ)], x1.eval (List.ofFn (x3 x6 x4)) = Bool.true) ∧ ∀ x6 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], x1.eval (List.ofFn (x3 x6 x4)) = Bool.false := by
  intro x1 h x3 x4 hx4
  obtain ⟨a, b⟩ := PEqualNP.Outside.L_meta_8425.chk ⟨x4, hx4⟩
  refine ⟨fun m hm => (h _).mpr (of_decide_eq_true (a m hm)), fun m hm => ?_⟩
  rw [Bool.eq_false_iff]
  intro hh
  exact of_decide_eq_false (b m hm) ((h _).mp hh)
