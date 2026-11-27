import PEqualNP.ProofComplexity.Helpers.DegSizeSim
import PEqualNP.ProofComplexity.Helpers.DegSizeRank
import PEqualNP.ProofComplexity.Helpers.DegSizeGain
import PEqualNP.ProofComplexity.Helpers.DegSizeArith

/-!
# Assembly of L-pcx-042 (degree to size for Res(⊕))

The common multiplier (Theorem 4.3 (b)) and the simulation (Proposition 5.1) give the size
criterion with `η` explicit; the arithmetic then gives the recorded bound.
-/

namespace PEqualNP.ProofComplexity.DegSizeAssembly

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan

/-- The size criterion with `η` explicit. -/
theorem assembly :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
      (w D K t : ℕ),
      (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π → ¬ PCRefutable (cnfSystem F) D →
      1 ≤ K → K + max (2 * t + 2) (t + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - eta (Fintype.card V) K) ^ t := by
  classical
  intro V _ _ F π w D K t hw href hnr hK hB
  by_contra hlt
  rw [not_le] at hlt
  have hD2 : 2 ≤ D := by omega
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure (cnfSystem F) D hD2 (fun v => Or.inl ⟨v, rfl⟩)
  have h1 : (1 : MvPolynomial V (ZMod 2)) ∉ pcClosure (cnfSystem F) D := hnr
  have hnn : (0 : ℝ) ≤ (1 - eta (Fintype.card V) K) ^ t :=
    pow_nonneg (sub_nonneg.mpr (DegSizeArith.eta_le_one _ K hK)) t
  have hcard : (π.toFinset.card : ℝ) ≤ (π.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le π
  have hS : (π.toFinset.card : ℝ) * (1 - eta (Fintype.card V) K) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hnn) hlt
  obtain ⟨f, qs, hf, hfC, hspan, hmem⟩ :=
    DegSizeGain.common DegSizeRank.monoRank_used DegSizeRank.rankRetention_used
      V (pcClosure (cnfSystem F) D) D K t (LinClause V) π.toFinset
      (fun L => L.image (fun q => eqPoly q)) hC h1
      (by
        intro L _ g hg
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hg
        exact totalDegree_eqPoly_le q)
      hK (by omega) hS
  apply hfC
  refine DegSizeSim.simulation_refutation V F π w D K t f qs hw href hB hf ?_ ?_
  · intro L hL j
    have := hspan L (List.mem_toFinset.mpr hL) j
    simpa [Finset.coe_image] using this
  · intro L hL q hq
    exact hmem L (List.mem_toFinset.mpr hL) (eqPoly q) (Finset.mem_image_of_mem _ hq)

/-- The recorded bound of L-pcx-042. -/
theorem degree_to_size :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
      (w D : ℕ), (∀ C ∈ F, C.card ≤ w) → 32 * w ≤ D → 32 ≤ D → IsLinRefutation F π →
      ¬ PCRefutable (cnfSystem F) D →
      Real.exp (((D : ℝ) ^ 2) / (1024 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ) := by
  intro V _ _ F π w D hw hwD hD href hnr
  exact DegSizeArith.final_of_assembly V F π w D hw hwD hD hnr href
    (fun K t hK hB => assembly V F π w D K t hw href hnr hK hB)

/-- The stronger form: width up to `D / 2`, constant `256`. -/
theorem degree_to_size_256 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
      (w D : ℕ), (∀ C ∈ F, C.card ≤ w) → 2 * w ≤ D → 32 ≤ D → IsLinRefutation F π →
      ¬ PCRefutable (cnfSystem F) D →
      Real.exp (((D : ℝ) ^ 2) / (256 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ) := by
  intro V _ _ F π w D hw hwD hD href hnr
  exact DegSizeArith.final_of_assembly_256 V F π w D hw hwD hD hnr href
    (fun K t hK hB => assembly V F π w D K t hw href hnr hK hB)

end PEqualNP.ProofComplexity.DegSizeAssembly
