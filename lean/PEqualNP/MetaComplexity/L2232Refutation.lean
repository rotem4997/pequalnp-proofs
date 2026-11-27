import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2229

theorem PEqualNP.MetaComplexity.L2232Refutation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) :=
  by
  rintro ⟨C, h0, h1, h2, h3⟩
  have hC := PEqualNP.Outside.L_meta_2229 C h0 h1 h3
  omega
