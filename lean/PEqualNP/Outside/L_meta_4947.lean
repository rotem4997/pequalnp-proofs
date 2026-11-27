import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4947

end PEqualNP.Outside.L_meta_4947

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_4947 : ∀ (x1 : ℕ) (x2 : Fin (13 : ℕ)),   (x1 ∈       have x3 : List ℕ :=         have x3 : List ℕ :=           have x3 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];           (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x3;         have x4 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x3;         (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x4;       have x4 : List ℕ :=         have x4 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x3;         (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x4;       have x5 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x4;       (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x5) →     have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x1.testBit ↑(x4 - x2) = Bool.true};     have x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ));     have x6 : Fin (13 : ℕ) → Prop := fun (x6 : Fin (13 : ℕ)) => ∀ x7 ∈ x4, ¬x5 x7 x6;     (∀ x7 ∉ x4, ∃ (x9 : Fin (13 : ℕ)), x6 x9 ∧ x5 x7 x9) ∧ (¬∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x4, x5 x8 x7) ∧ ¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x6 x8 → x5 x7 x8 := by
  intro x1 x2 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only
    refine ⟨?_, ?_, ?_⟩ <;> revert x2 <;> decide +kernel
