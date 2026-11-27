import Mathlib.Data.Fin.Basic

set_option maxHeartbeats 10000 in
theorem PEqualNP.Outside.L_meta_18876 : ∃ (x1 : Fin (12 : ℕ)) (x2 : Fin (13 : ℕ)), x1.succ = x2 ∨ x1.succ = x2 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (9 : Fin ((12 : ℕ) + (1 : ℕ))) := by
  first
  | solve | rfl
  | solve | intros; assumption
  | solve | intro prior; intros; apply prior <;> first | assumption | exact le_rfl | omega
  | solve | dsimp only; intros; grind only
  | solve | intros; omega
  | solve | simp_all
  | solve | decide +revert +kernel
