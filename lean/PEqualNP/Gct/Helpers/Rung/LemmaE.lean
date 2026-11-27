import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# The superquadratic rung: proof of `LemmaE`

Helper module, proofs only. It proves the step `LemmaE` of `Statements.lean`: a point at which
all partial derivatives of the elementary symmetric polynomial `e_r` (`r ≥ 2`) vanish takes at
most `r - 1` distinct coordinate values.

Route. Write `esymmOn s k` for the `k`-th elementary symmetric polynomial in the variables of a
finite set `s`. Then `∂ e_{k+1} / ∂ z_i = esymmOn (univ.erase i) k` (`pderiv_esymm_succ`), and
`e_{k+1} = esymmOn (univ.erase i) (k+1) + z_i * esymmOn (univ.erase i) k`, which unrolls to
`esymmOn (univ.erase i) k = ∑_{l ≤ k} e_{k-l} (-z_i)^l` (`eval_esymmOn_erase`). So at a singular
point every coordinate is a root of one polynomial of degree `r - 1` with leading coefficient
`± 1`.
-/

namespace PEqualNP.Gct.Rung

open MvPolynomial

namespace LemE

/-- The `k`-th elementary symmetric polynomial in the variables indexed by the finite set `s`. -/
noncomputable def esymmOn {σ : Type} (s : Finset σ) (k : ℕ) : MvPolynomial σ ℂ :=
  ∑ t ∈ s.powersetCard k, ∏ j ∈ t, X j

theorem esymmOn_univ {σ : Type} [Fintype σ] (k : ℕ) :
    esymmOn (Finset.univ : Finset σ) k = esymm σ ℂ k := rfl

theorem esymmOn_zero {σ : Type} (s : Finset σ) : esymmOn s 0 = 1 := by
  simp [esymmOn]

/-- Splitting the subsets of `insert i s` by membership of `i`. -/
theorem esymmOn_insert {σ : Type} [DecidableEq σ] {i : σ} {s : Finset σ} (hi : i ∉ s) (k : ℕ) :
    esymmOn (insert i s) (k + 1) = esymmOn s (k + 1) + X i * esymmOn s k := by
  unfold esymmOn
  rw [Finset.powersetCard_succ_insert hi, Finset.sum_union, Finset.sum_image, Finset.mul_sum]
  · congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_insert]
    exact fun h => hi ((Finset.mem_powersetCard.1 ht).1 h)
  · intro t ht u hu h
    have ht' : i ∉ t := fun h => hi ((Finset.mem_powersetCard.1 ht).1 h)
    have hu' : i ∉ u := fun h => hi ((Finset.mem_powersetCard.1 hu).1 h)
    have := congrArg (fun w => w.erase i) h
    simpa [Finset.erase_insert ht', Finset.erase_insert hu'] using this
  · rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 ha'
    exact hi ((Finset.mem_powersetCard.1 ha).1 (Finset.mem_insert_self i t))

theorem pderiv_prod_X {σ : Type} {i : σ} {t : Finset σ} (hi : i ∉ t) :
    pderiv i (∏ j ∈ t, (X j : MvPolynomial σ ℂ)) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hia : a ≠ i := fun h => hi (h ▸ Finset.mem_insert_self a t)
    have hit : i ∉ t := fun h => hi (Finset.mem_insert_of_mem h)
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hit, pderiv_X, Pi.single_eq_of_ne hia]
    simp

theorem pderiv_esymmOn {σ : Type} {i : σ} {s : Finset σ} (hi : i ∉ s) (k : ℕ) :
    pderiv i (esymmOn s k) = 0 := by
  unfold esymmOn
  rw [map_sum]
  refine Finset.sum_eq_zero fun t ht => pderiv_prod_X ?_
  exact fun h => hi ((Finset.mem_powersetCard.1 ht).1 h)

/-- The recursion `e_{k+1} = e_{k+1}(without i) + z_i e_k(without i)`. -/
theorem esymm_succ_eq {σ : Type} [Fintype σ] [DecidableEq σ] (i : σ) (k : ℕ) :
    esymm σ ℂ (k + 1) =
      esymmOn (Finset.univ.erase i) (k + 1) + X i * esymmOn (Finset.univ.erase i) k := by
  rw [← esymmOn_univ, ← esymmOn_insert (Finset.notMem_erase i _),
    Finset.insert_erase (Finset.mem_univ i)]

/-- The partial derivative of `e_{k+1}` in the variable `i` is `e_k` of the other variables. -/
theorem pderiv_esymm_succ {σ : Type} [Fintype σ] [DecidableEq σ] (i : σ) (k : ℕ) :
    pderiv i (esymm σ ℂ (k + 1)) = esymmOn (Finset.univ.erase i) k := by
  have hi : i ∉ Finset.univ.erase i := Finset.notMem_erase i _
  rw [esymm_succ_eq i k, map_add, Derivation.leibniz, pderiv_esymmOn hi, pderiv_esymmOn hi,
    pderiv_X_self]
  simp

/-- `e_k(z without z_i) = ∑_{l ≤ k} e_{k-l}(z) (-z_i)^l`. -/
theorem eval_esymmOn_erase {σ : Type} [Fintype σ] [DecidableEq σ] (z : σ → ℂ) (i : σ) (k : ℕ) :
    eval z (esymmOn (Finset.univ.erase i) k) =
      ∑ l ∈ Finset.range (k + 1), eval z (esymm σ ℂ (k - l)) * (-z i) ^ l := by
  induction k with
  | zero => simp [esymmOn_zero, esymm_zero]
  | succ k ih =>
    have h := congrArg (eval z) (esymm_succ_eq (σ := σ) i k)
    rw [map_add, map_mul, eval_X] at h
    have h2 : eval z (esymmOn (Finset.univ.erase i) (k + 1)) =
        eval z (esymm σ ℂ (k + 1)) - z i * eval z (esymmOn (Finset.univ.erase i) k) :=
      eq_sub_of_add_eq h.symm
    rw [h2, ih, Finset.sum_range_succ' _ (k + 1), Finset.mul_sum]
    simp only [Nat.succ_sub_succ, Nat.sub_zero, pow_zero, mul_one]
    rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- The one-variable polynomial `∑_{l < r} e_{r-1-l}(z) (-1)^l u^l` whose roots contain the
coordinates of a singular point of `e_r`. -/
noncomputable def rootPoly {σ : Type} [Fintype σ] (z : σ → ℂ) (r : ℕ) : Polynomial ℂ :=
  ∑ l ∈ Finset.range r,
    Polynomial.C (eval z (esymm σ ℂ (r - 1 - l)) * (-1) ^ l) * Polynomial.X ^ l

theorem eval_rootPoly {σ : Type} [Fintype σ] [DecidableEq σ] (z : σ → ℂ) (i : σ) (k : ℕ) :
    (rootPoly z (k + 1)).eval (z i) = eval z (pderiv i (esymm σ ℂ (k + 1))) := by
  rw [pderiv_esymm_succ, eval_esymmOn_erase, rootPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Nat.add_sub_cancel]
  rw [neg_pow]
  ring

theorem coeff_rootPoly {σ : Type} [Fintype σ] (z : σ → ℂ) (k : ℕ) :
    (rootPoly z (k + 1)).coeff k = (-1) ^ k := by
  rw [rootPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (k + 1)) k]
  simp [esymm_zero]

theorem rootPoly_ne_zero {σ : Type} [Fintype σ] (z : σ → ℂ) (k : ℕ) :
    rootPoly z (k + 1) ≠ 0 := by
  intro h
  have := coeff_rootPoly z k
  rw [h, Polynomial.coeff_zero] at this
  exact pow_ne_zero k (neg_ne_zero.2 one_ne_zero) this.symm

theorem natDegree_rootPoly_le {σ : Type} [Fintype σ] (z : σ → ℂ) (k : ℕ) :
    (rootPoly z (k + 1)).natDegree ≤ k := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))

/-- `LemmaE` for an arbitrary finite index type and degree `k + 1 ≥ 1`. -/
theorem card_image_le {σ : Type} [Fintype σ] [DecidableEq σ] (z : σ → ℂ) (k : ℕ)
    (h : GradZero (esymm σ ℂ (k + 1)) z) : (Finset.univ.image z).card ≤ k := by
  have hsub : Finset.univ.image z ⊆ (rootPoly z (k + 1)).roots.toFinset := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (rootPoly_ne_zero z k),
      Polynomial.IsRoot.def, eval_rootPoly]
    exact h i
  calc (Finset.univ.image z).card ≤ (rootPoly z (k + 1)).roots.toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ Multiset.card (rootPoly z (k + 1)).roots := Multiset.toFinset_card_le _
    _ ≤ (rootPoly z (k + 1)).natDegree := Polynomial.card_roots' _
    _ ≤ k := natDegree_rootPoly_le z k

end LemE

theorem lemmaE : LemmaE := by
  intro b r z hr h
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact LemE.card_image_le z k h

end PEqualNP.Gct.Rung
