import PEqualNP.ProofComplexity.Helpers.DegSizeSim

/-!
# Helpers for L-lib-109: a width `k` Res(⊕) refutation gives a polynomial calculus refutation

The approximator of a line `L` sends position `j < k` to the affine form of the `j`-th equation
of `L` (in the order of `L.toList`) and pads with `0`. With `f = 1`, `K = 0` and `t = k`, the
theorem `DegSizeSim.simulation_refutation` gives the refutation in degree
`max (2 * k + 2) (k + w)`, once each line's approximator times the affine form of any of its
equations is in the closure: that product is `P * (e * e + e)` with `P` of degree at most `k`.
-/

namespace PEqualNP.Search.Helpers.PCSim

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan PEqualNP.ProofComplexity.DegSizeSim

variable {V : Type}

/-- The approximator of a line: the affine form of its `j`-th equation, or `0`. -/
noncomputable def appr (k : ℕ) (L : PEqualNP.ProofComplexity.LinClause V) (j : Fin k) :
    MvPolynomial V (ZMod 2) :=
  Option.elim (L.toList[j.1]?) 0 (fun q => eqPoly q)

theorem appr_mem_span (k : ℕ) (L : PEqualNP.ProofComplexity.LinClause V) (j : Fin k) :
    appr k L j ∈ Submodule.span (ZMod 2)
      ((fun q => eqPoly q) '' (↑L : Set (PEqualNP.ProofComplexity.LinEq V))) := by
  unfold appr
  cases h : L.toList[j.1]? with
  | none => exact Submodule.zero_mem _
  | some q =>
    refine Submodule.subset_span ⟨q, ?_, rfl⟩
    exact Finset.mem_toList.mp (List.mem_of_getElem? h)

theorem appr_side [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V))
    (k D : ℕ) (hD : 2 * k + 2 ≤ D) (L : PEqualNP.ProofComplexity.LinClause V)
    (hL : L.card ≤ k) (q : PEqualNP.ProofComplexity.LinEq V) (hq : q ∈ L) :
    PCDerivable (cnfSystem F) D ((∏ j, (1 + appr k L j)) * eqPoly q * 1) := by
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ (by omega) fun v => Or.inl ⟨v, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (Finset.mem_toList.mpr hq)
  have hlt : i < L.toList.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [Finset.length_toList] at hlt
  let j0 : Fin k := ⟨i, by omega⟩
  have hj0 : appr k L j0 = eqPoly q := by
    unfold appr
    simp only [j0, hi, Option.elim]
  have hdeg : ∀ j, (appr k L j).totalDegree ≤ 1 := fun j =>
    totalDegree_span_le (totalDegree_eqImage_le L) (appr_mem_span k L j)
  have hP : (∏ j ∈ Finset.univ.erase j0, (1 + appr k L j)).totalDegree ≤ k := by
    refine (totalDegree_prod_le _ _ fun j _ => hdeg j).trans ?_
    exact (Finset.card_le_univ _).trans (by simp)
  have hidem := affine_idem' hC (totalDegree_eqPoly_le q)
  have hdi : (eqPoly q * eqPoly q + eqPoly q).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans
      (max_le (totalDegree_mul_le' (totalDegree_eqPoly_le q) (totalDegree_eqPoly_le q))
        ((totalDegree_eqPoly_le q).trans (by norm_num)))
  have h := absorb_le hC _ hidem hP hdi (by omega)
  have e : (∏ j, (1 + appr k L j)) * eqPoly q * 1
      = (∏ j ∈ Finset.univ.erase j0, (1 + appr k L j)) * (eqPoly q * eqPoly q + eqPoly q) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => 1 + appr k L j) (Finset.mem_univ j0), hj0]
    ring
  rw [e]
  exact h

/-- The simulation for L-lib-109. -/
theorem sim (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V))
    (π : List (PEqualNP.ProofComplexity.LinClause V)) (w k : ℕ) (hw : ∀ C ∈ F, C.card ≤ w)
    (href : IsLinRefutation F π)
    (hk : ∀ L ∈ π, L.card ≤ k) :
    PCRefutable (cnfSystem F) (max (2 * k + 2) (k + w)) := by
  have hD : 2 * k + 2 ≤ max (2 * k + 2) (k + w) := le_max_left _ _
  exact simulation_refutation V F π w (max (2 * k + 2) (k + w)) 0 k 1 (appr k) hw href
    (by omega) (by rw [totalDegree_one]) (fun L _ j => appr_mem_span k L j)
    (fun L hL q hq => appr_side F k _ hD L (hk L hL) q hq)

end PEqualNP.Search.Helpers.PCSim
