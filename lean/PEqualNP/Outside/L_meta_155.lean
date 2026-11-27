import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_155 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
      (∀ i, r i ≠ 0) →
      LinearIndependent ℚ
        (fun i : {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} => r i.val) := by
  intro k m r _
  apply linearIndependent_iff_notMem_span.mpr
  intro i hi
  apply i.property
  apply Submodule.span_mono _ hi
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨j.val, ?_, rfl⟩
  intro h
  exact hj.2 (Subtype.ext h)
