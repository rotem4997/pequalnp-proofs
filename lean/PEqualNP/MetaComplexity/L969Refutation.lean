import PEqualNP.Defs
import PEqualNP.Outside.L_meta_970

theorem PEqualNP.MetaComplexity.L969Refutation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  by
  rintro ⟨C, h0, h1, h2⟩
  have hC := PEqualNP.Outside.L_meta_970 C h0 h2
  omega
