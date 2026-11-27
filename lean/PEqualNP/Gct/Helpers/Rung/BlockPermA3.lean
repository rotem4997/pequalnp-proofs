import Mathlib
import PEqualNP.Gct.Helpers.Rung.BlockPermA1
import PEqualNP.Gct.Helpers.Rung.BlockPermA2

/-!
# Helper module (proofs only): the padding columns

`coeff_pad`: for an `a × r` matrix `Y`, the coefficient of the squarefree monomial of full
degree in `(∑ i, X i) ^ (a - r) * ∏ n, ∑ i, Y i n * X i` (which is the permanent of `Y`
padded with `a - r` columns of ones) is a positive integer times the sum of the permanents of
the `r × r` submatrices of `Y`.
-/

namespace PEqualNP.Gct.Rung.BPA

open MvPolynomial Finset

variable {R : Type*} [CommRing R]

/-- The permanent as the coefficient of the squarefree monomial of full degree. -/
theorem pm_coeff_ones {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
    (W : ρ → κ → R) :
    pm W = (∏ j, ∑ i, C (W i j) * X i : MvPolynomial ρ R).coeff (∑ i, Finsupp.single i 1) := by
  have h := pm_group (id : ρ → ρ) W
  simpa [stab_id] using h

/-- The group map of the padded matrix: the `a - r` padding rows form one group. -/
def pad (a r : ℕ) : Fin r ⊕ Fin (a - r) → Fin r ⊕ Unit := Sum.map id (fun _ => ())

theorem coeff_pad (a r : ℕ) (hra : r ≤ a) (Y : Fin a → Fin r → R) :
    ((∑ i, X i) ^ (a - r) * ∏ n : Fin r, ∑ i, C (Y i n) * X i : MvPolynomial (Fin a) R).coeff
      (∑ i, Finsupp.single i 1) =
    (stab (pad a r) : R) * ∑ I : {I : Finset (Fin a) // I.card = r},
      Matrix.permanent (Matrix.of fun m n : Fin r => Y (I.1.orderEmbOfFin I.2 m) n) := by
  classical
  set W1 : Fin a → Fin r ⊕ Fin (a - r) → R := fun i => Sum.elim (fun n => Y i n) (fun _ => 1)
    with hW1
  set W2 : Fin r ⊕ Unit → Fin a → R := fun γ i => Sum.elim (fun n => Y i n) (fun _ => 1) γ
    with hW2
  have ha : ((∑ i, X i) ^ (a - r) * ∏ n : Fin r, ∑ i, C (Y i n) * X i : MvPolynomial (Fin a) R)
      = ∏ j : Fin r ⊕ Fin (a - r), ∑ i, C (W1 i j) * X i := by
    rw [Fintype.prod_sum_type, mul_comm]
    simp [hW1]
  have hT : (fun (j : Fin r ⊕ Fin (a - r)) (i : Fin a) => W1 i j) =
      fun j i => W2 (pad a r j) i := by
    funext j i
    cases j <;> rfl
  rw [ha, ← pm_coeff_ones W1, ← pm_transpose W1, hT, pm_group]
  congr 1
  have hprof : (∑ j : Fin r ⊕ Fin (a - r), Finsupp.single (pad a r j) 1) =
      Finsupp.sumElim (∑ n : Fin r, Finsupp.single n 1) (Finsupp.single () (a - r)) := by
    ext (n | u)
    · simp [Fintype.sum_sum_type, Finsupp.single_apply, pad]
    · simp [Fintype.sum_sum_type, pad]
  have h1 : ∀ i : Fin a, (∑ γ : Fin r ⊕ Unit, C (W2 γ i) * X γ : MvPolynomial (Fin r ⊕ Unit) R)
      = rename Sum.inl (∑ n, C (Y i n) * X n) + X (Sum.inr ()) := by
    intro i
    simp [Fintype.sum_sum_type, hW2]
  have hpoly : (∏ i : Fin a, ∑ γ : Fin r ⊕ Unit, C (W2 γ i) * X γ :
      MvPolynomial (Fin r ⊕ Unit) R) =
      rename Sum.inl (1 : MvPolynomial (Fin r) R) *
        ∏ u : Unit, ∑ t ∈ (univ : Finset (Fin a)).powerset,
          rename Sum.inl (∏ i ∈ t, ∑ n, C (Y i n) * X n) * X (Sum.inr u) ^ (univ \ t).card := by
    simp only [h1]
    rw [Finset.prod_add, map_one, one_mul, Fintype.prod_unique]
    refine sum_congr rfl fun t _ => ?_
    rw [map_prod, Finset.prod_const]
  rw [hprof, hpoly, coeff_sep, one_mul, Fintype.prod_unique]
  have hfilter : ((univ : Finset (Fin a)).powerset.filter
      fun t => (univ \ t).card = (Finsupp.single () (a - r) : Unit →₀ ℕ) default) =
      univ.filter (fun t : Finset (Fin a) => t.card = r) := by
    ext t
    simp only [mem_filter, mem_powerset, subset_univ, mem_univ, true_and]
    rw [Finset.card_univ_sdiff, Fintype.card_fin]
    have h2 := Finset.card_le_univ t
    simp only [Fintype.card_fin] at h2
    have hs : (Finsupp.single () (a - r) : Unit →₀ ℕ) default = a - r := by simp
    rw [hs]
    omega
  rw [hfilter, coeff_sum, Finset.sum_subtype (p := fun t : Finset (Fin a) => t.card = r) _
    (by simp)]
  refine sum_congr rfl fun I _ => ?_
  have hprod : (∏ i ∈ I.1, ∑ n, C (Y i n) * X n : MvPolynomial (Fin r) R) =
      ∏ m : Fin r, ∑ n, C (Y (I.1.orderEmbOfFin I.2 m) n) * X n := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I.1 I.2, Finset.prod_map]
    rfl
  rw [hprod]
  exact ((pm_coeff_ones fun n m => Y (I.1.orderEmbOfFin I.2 m) n).symm.trans
    (by rw [← Matrix.permanent_transpose]; rfl))

end PEqualNP.Gct.Rung.BPA
