import PEqualNP.Defs
import PEqualNP.Outside.L_meta_723

theorem PEqualNP.MetaComplexity.L583Refutation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  by
  rintro ⟨C, h0, h1, h2⟩
  have hC := PEqualNP.Outside.L_meta_723 C h0 h2
  omega
