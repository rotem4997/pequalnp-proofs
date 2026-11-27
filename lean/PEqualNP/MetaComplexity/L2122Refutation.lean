import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2121

theorem PEqualNP.MetaComplexity.L2122Refutation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 4 C ∧ C.size ≤ 2 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun z : Fin 4 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)) x) :=
  by
  rintro ⟨C, h0, h1, h2, h3⟩
  have hC := PEqualNP.Outside.L_meta_2121 C h0 h1 h3
  omega
