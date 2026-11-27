import PEqualNP.Defs

set_option maxHeartbeats 10000 in
theorem PEqualNP.Outside.L_meta_18825 : ∀ (x1 x2 : Fin (13 : ℕ)), x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 ↔ x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)) := by
  first
  | solve | rfl
  | solve | intros; assumption
  | solve | intro prior; intros; apply prior <;> first | assumption | exact le_rfl | omega
  | solve | dsimp only; intros; grind only
  | solve | intros; omega
  | solve | simp_all
  | solve | decide +revert +kernel
