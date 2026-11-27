import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# Few rows, from the row system and Fact Z

`fewRows : RowSystem → BoundedZeros → FewRows`. Restrict the row system to the row space: the
forms `g_j = ∂_j e_r ∘ P` are homogeneous of degree `r - 1` in `l` variables, with only the
common zero `0` by `RowSpaceGood`; the restricted system `f_j ∘ P` differs from them in degree
below `r - 1`; the parameters of the rows are common zeros of it, so there are at most `M` of
them, and so at most `M` distinct rows.
-/

namespace PEqualNP.Gct.Rung

open MvPolynomial

/-- The elementary symmetric polynomial `e_n` is homogeneous of degree `n`. -/
theorem esymm_isHomogeneous' (σ : Type) [Fintype σ] (n : ℕ) :
    (esymm σ ℂ n).IsHomogeneous n := by
  rw [esymm]
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have h := IsHomogeneous.prod t (fun i => (X i : MvPolynomial σ ℂ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ i)
  simpa [(Finset.mem_powersetCard.mp ht).2] using h

/-- Substituting polynomials of total degree at most one does not raise the total degree. -/
theorem totalDegree_bind₁_le' {σ τ : Type} (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (bind₁ g p).totalDegree ≤ p.totalDegree := by
  rw [bind₁, aeval_def, eval₂_eq]
  refine totalDegree_finsetSum_le fun d hd => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow (g i) (d i)).trans
    (Nat.mul_le_mul_left (d i) (hg i))) ?_
  simp only [mul_one]
  exact le_totalDegree hd

/-- The linear substitution of the column space: `X n ↦ ∑ s, P n s * X s`. -/
noncomputable def linSub {b l : ℕ} (P : Fin b → Fin l → ℂ) : Fin b → MvPolynomial (Fin l) ℂ :=
  fun n => ∑ s, C (P n s) * X s

theorem eval_linSub {b l : ℕ} (P : Fin b → Fin l → ℂ) (y : Fin l → ℂ)
    (p : MvPolynomial (Fin b) ℂ) :
    eval y (bind₁ (linSub P) p) = eval (fun n => ∑ s, P n s * y s) p := by
  change eval₂Hom (RingHom.id ℂ) y (bind₁ (linSub P) p) = _
  rw [eval₂Hom_bind₁]
  change eval₂Hom (RingHom.id ℂ) _ p = eval₂Hom (RingHom.id ℂ) _ p
  congr 2
  funext n
  change eval y (linSub P n) = _
  simp [linSub]

theorem linSub_isHomogeneous {b l : ℕ} (P : Fin b → Fin l → ℂ) (n : Fin b) :
    (linSub P n).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun s _ => (isHomogeneous_X ℂ s).C_mul _

theorem linSub_totalDegree {b l : ℕ} (P : Fin b → Fin l → ℂ) (n : Fin b) :
    (linSub P n).totalDegree ≤ 1 :=
  (linSub_isHomogeneous P n).totalDegree_le

theorem fewRows (hR : RowSystem) (hB : BoundedZeros) : FewRows := by
  intro b r l P hr hP
  classical
  have hhom : ∀ j, (bind₁ (linSub P) (pderiv j (esymm (Fin b) ℂ r))).IsHomogeneous (r - 1) := by
    intro j
    have h := ((esymm_isHomogeneous' (Fin b) r).pderiv (i := j)).aeval (linSub P)
      (linSub_isHomogeneous P)
    rw [one_mul] at h
    exact h
  have hzero : ∀ y : Fin l → ℂ,
      (∀ j, eval y (bind₁ (linSub P) (pderiv j (esymm (Fin b) ℂ r))) = 0) → y = 0 := by
    intro y hy
    refine hP y fun j => ?_
    have := hy j
    rw [eval_linSub] at this
    exact this
  obtain ⟨M, hM⟩ := hB l b (r - 1) _ hhom hzero
  refine ⟨M, ?_⟩
  intro a X hrow hgrad
  obtain ⟨f, hfdeg, hfzero⟩ := hR a b r X hr hgrad
  choose y hy using hrow
  have hFdeg : ∀ j, (bind₁ (linSub P) (f j) -
      bind₁ (linSub P) (pderiv j (esymm (Fin b) ℂ r))).totalDegree < r - 1 := by
    intro j
    rw [← map_sub]
    exact lt_of_le_of_lt (totalDegree_bind₁_le' _ (linSub_totalDegree P) _) (hfdeg j)
  have hrowfun : ∀ i, (fun j : Fin b => X (i, j)) = fun n => ∑ s, P n s * y i s := by
    intro i
    funext j
    exact hy i j
  have hs : ∀ z ∈ Finset.univ.image y, ∀ j, eval z (bind₁ (linSub P) (f j)) = 0 := by
    intro z hz j
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [eval_linSub, ← hrowfun i]
    exact hfzero i j
  have hcard := hM (fun j => bind₁ (linSub P) (f j)) hFdeg (Finset.univ.image y) hs
  have himage : (Finset.univ.image fun i : Fin a => fun j : Fin b => X (i, j)) =
      (Finset.univ.image y).image (fun z : Fin l → ℂ => fun n => ∑ s, P n s * z s) := by
    rw [Finset.image_image]
    congr 1
    funext i
    exact hrowfun i
  rw [himage]
  exact Finset.card_image_le.trans hcard

end PEqualNP.Gct.Rung
