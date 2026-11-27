import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7223

def W (m s : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun i : Fin 13 => m.testBit (((i : ℕ) + s) % 13))

end PEqualNP.Outside.L_meta_7223

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_7223 : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ x9 ∈ [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (23871497 : ℕ), (6815755 : ℕ), (22839313 : ℕ), (20529185 : ℕ), (18350129 : ℕ), (24166465 : ℕ), (4489361 : ℕ), (2179233 : ℕ), (6291663 : ℕ), (20971869 : ℕ), (4227539 : ℕ), (17826421 : ℕ), (16794473 : ℕ), (2163879 : ℕ), (16779133 : ℕ), (8191 : ℕ)], ∀ (x11 : Fin (13 : ℕ)), ∃ (x12 : Finset x1), x8 x12 ∧ x7 x12 = fun (x13 : Fin (26 : ℕ)) => x9.testBit ((if ↑x13 < (13 : ℕ) then (0 : ℕ) else (13 : ℕ)) + (↑x13 + ↑x11) % (13 : ℕ)) := by
  dsimp only
  intro x9 hx9 x11
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx9
  refine ⟨PEqualNP.Outside.L_meta_7223.W x9 x11, ⟨?a, ?b⟩, funext fun x13 => ?c⟩
  case a =>
    rcases hx9 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (revert x11; decide +kernel)
  case b =>
    rcases hx9 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (revert x11; decide +kernel)
  case c =>
    rcases hx9 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (revert x13 x11; decide +kernel)
