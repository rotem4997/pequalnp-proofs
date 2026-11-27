import Mathlib
import PEqualNP.Defs.Gct

/-! Helpers for L-gct-079 (product-type linear spaces through Sigma_m inside the permanent
hypersurface have dimension at most 2m - 2).

The permanent of a matrix whose rows outside a set `T` are all ones is handled without any
sum over injections: `sum_mul_permanent` (multiply one row at a time pointwise by a vector) and
invariance under row swaps give the recursion `rowMat_rec`, and the closed formula
`rowMat_perm_formula` follows by induction on the set of special rows.

The main theorem `main` takes the chain inequality (proved by another module) as a hypothesis. -/

namespace PEqualNP.Gct.Helpers.ProdSigma

open Finset

variable {m : ℕ}

theorem eval_permPoly (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- Multiplying the rows one at a time pointwise by `v` and adding the permanents gives the sum
of the entries of `v` times the permanent. -/
theorem sum_mul_permanent (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    (∑ c, v c) * A.permanent = ∑ j, (A.updateRow j (A j * v)).permanent := by
  unfold Matrix.permanent
  rw [mul_sum, sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  have h : ∀ j, ∏ i, (A.updateRow j (A j * v)) (σ i) i = v (σ.symm j) * ∏ i, A (σ i) i := by
    intro j
    have h1 : ∀ i, (A.updateRow j (A j * v)) (σ i) i =
        (if i = σ.symm j then v i else 1) * A (σ i) i := by
      intro i
      by_cases hi : i = σ.symm j
      · subst hi
        simp [Matrix.updateRow_self, mul_comm]
      · have hne : σ i ≠ j := fun h => hi (by rw [← h]; simp)
        rw [Matrix.updateRow_ne hne]
        simp [hi]
    simp_rw [h1, prod_mul_distrib]
    simp
  simp_rw [h, ← sum_mul]
  congr 1
  exact (Equiv.sum_comp σ.symm v).symm

/-- The matrix with row `i` equal to `r i` for `i ∈ T` and all ones otherwise. -/
def rowMat (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i ∈ T then r i j else 1

theorem rowMat_apply (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (i j : Fin m) :
    rowMat T r i j = if i ∈ T then r i j else 1 := rfl

/-- The recursion: making one more row special. -/
theorem rowMat_rec (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (i0 : Fin m) (hi0 : i0 ∉ T) :
    (∑ c, r i0 c) * (rowMat T r).permanent =
      ((Tᶜ.card : ℕ) : ℂ) * (rowMat (insert i0 T) r).permanent +
        ∑ k ∈ T, (rowMat T (fun i j => if i = k then r k j * r i0 j else r i j)).permanent := by
  rw [sum_mul_permanent, ← sum_add_sum_compl T, add_comm]
  congr 1
  · rw [← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun j hj => ?_
    have hjT : j ∉ T := mem_compl.1 hj
    rw [← Matrix.permanent_permute_cols (Equiv.swap j i0)]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, Matrix.updateRow_apply, rowMat_apply, Pi.mul_apply,
      mem_insert]
    by_cases ha : a = i0
    · subst ha
      simp [hjT]
    · by_cases haj : a = j
      · subst haj
        have : i0 ≠ a := fun h => ha h.symm
        simp [hjT, hi0, this, ha]
      · rw [Equiv.swap_apply_of_ne_of_ne haj ha]
        simp [haj, ha]
  · refine sum_congr rfl fun k hk => ?_
    congr 1
    ext a b
    simp only [Matrix.updateRow_apply, rowMat_apply, Pi.mul_apply]
    by_cases ha : a = k
    · subst ha
      simp [hk]
    · simp [ha]

theorem permanent_ones : (rowMat (∅ : Finset (Fin m)) fun _ _ => 0).permanent
    = (m.factorial : ℂ) := by
  simp [Matrix.permanent, rowMat, Fintype.card_perm]

theorem rowMat_empty (r r' : Fin m → Fin m → ℂ) :
    rowMat (∅ : Finset (Fin m)) r = rowMat ∅ r' := by
  ext a b
  simp [rowMat_apply]

/-- One special row. -/
theorem rowMat_single (a : Fin m) (d : ℕ) (hd : 1 + d = m) (r : Fin m → Fin m → ℂ) :
    (rowMat {a} r).permanent = (d.factorial : ℂ) * ∑ j, r a j := by
  have h := rowMat_rec (∅ : Finset (Fin m)) r a (notMem_empty a)
  rw [rowMat_empty r (fun _ _ => 0), permanent_ones] at h
  simp only [sum_empty, add_zero, compl_empty, card_univ, Fintype.card_fin,
    insert_empty_eq] at h
  have hfac : m.factorial = m * d.factorial := by
    rw [← hd, add_comm, Nat.factorial_succ]
  have hne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  apply mul_left_cancel₀ hne
  rw [← h, hfac]
  push_cast
  ring

theorem prod_ite_mul (Q : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (k i0 j : Fin m) :
    ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) =
      (∏ i ∈ Q, r i j) * (if k ∈ Q then r i0 j else 1) := by
  have h : ∀ i, (if i = k then r k j * r i0 j else r i j) =
      r i j * (if i = k then r i0 j else 1) := by
    intro i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  simp_rw [h, prod_mul_distrib]
  congr 1
  simp

/-- The closed formula. Rows in `S` are `r i`, row `a` is `r a`, the other `d` rows are all
ones. If the sum of the entries of the pointwise product of the rows of every nonempty proper
subset of `S` vanishes, and either the row `a` or the product over `S` has entry sum zero, then
the permanent is `d! (-1)^s s!` times the sum of the entries of the product of all rows. -/
theorem rowMat_perm_formula (a : Fin m) : ∀ S : Finset (Fin m), a ∉ S → ∀ d : ℕ,
    S.card + 1 + d = m → ∀ r : Fin m → Fin m → ℂ,
    (∀ Q : Finset (Fin m), Q ⊆ S → Q.Nonempty → Q ≠ S → ∑ j, ∏ i ∈ Q, r i j = 0) →
    (S.Nonempty → (∑ j, r a j = 0) ∨ (∑ j, ∏ i ∈ S, r i j = 0)) →
    (rowMat (insert a S) r).permanent =
      (d.factorial : ℂ) * (-1) ^ S.card * (S.card.factorial : ℂ) *
        ∑ j, r a j * ∏ i ∈ S, r i j := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ d hd r _ _
    have := rowMat_single a d (by simpa [add_comm] using hd) r
    simpa using this
  | insert i0 S' hi0 ih =>
    intro ha d hd r h1 h2
    have hai : a ≠ i0 := fun h => ha (h ▸ mem_insert_self _ _)
    have haS : a ∉ S' := fun h => ha (mem_insert_of_mem h)
    have hcard : (insert i0 S').card = S'.card + 1 := card_insert_of_notMem hi0
    rw [hcard] at hd
    have hd' : S'.card + 1 + (d + 1) = m := by omega
    have hi0T : i0 ∉ insert a S' := by
      simp only [mem_insert, not_or]
      exact ⟨fun h => hai h.symm, hi0⟩
    have hrec := rowMat_rec (insert a S') r i0 hi0T
    set X : ℂ := ∑ j, r a j * ∏ i ∈ insert i0 S', r i j with hX
    set C : ℂ := ((d + 1).factorial : ℂ) * (-1) ^ S'.card * (S'.card.factorial : ℂ) with hC
    -- the left side vanishes
    have hleft : (∑ c, r i0 c) * (rowMat (insert a S') r).permanent = 0 := by
      rcases S'.eq_empty_or_nonempty with hS | hS
      · subst hS
        rw [insert_empty_eq, rowMat_single a (d + 1) (by simpa [add_comm] using hd') r]
        rcases h2 (insert_nonempty _ _) with h | h
        · rw [h]; ring
        · have : ∑ c, r i0 c = 0 := by simpa using h
          rw [this]; ring
      · have : ∑ c, r i0 c = 0 := by
          have := h1 {i0} (by simp) (singleton_nonempty _) (by
            intro h
            obtain ⟨x, hx⟩ := hS
            have : x ∈ ({i0} : Finset (Fin m)) := h ▸ mem_insert_of_mem hx
            rw [mem_singleton] at this
            exact hi0 (this ▸ hx))
          simpa using this
        rw [this]; ring
    -- hypotheses about subsets of S'
    have hsub : ∀ Q : Finset (Fin m), Q ⊆ S' → Q.Nonempty → ∑ j, ∏ i ∈ Q, r i j = 0 := by
      intro Q hQ hne
      refine h1 Q (hQ.trans (subset_insert _ _)) hne ?_
      intro h
      exact hi0 (hQ (h ▸ mem_insert_self _ _))
    have hsub2 : ∀ Q : Finset (Fin m), Q ⊆ S' → Q ≠ S' →
        ∑ j, ∏ i ∈ insert i0 Q, r i j = 0 := by
      intro Q hQ hne
      refine h1 (insert i0 Q) (insert_subset_insert _ hQ) (insert_nonempty _ _) ?_
      intro h
      apply hne
      have hi0Q : i0 ∉ Q := fun h => hi0 (hQ h)
      rw [← erase_insert hi0Q, h, erase_insert hi0]
    have hprodins : ∀ (Q : Finset (Fin m)), Q ⊆ S' → ∀ j,
        ∏ i ∈ insert i0 Q, r i j = (∏ i ∈ Q, r i j) * r i0 j := by
      intro Q hQ j
      rw [prod_insert (fun h => hi0 (hQ h)), mul_comm]
    -- the term k = a
    have hta : (rowMat (insert a S')
        (fun i j => if i = a then r a j * r i0 j else r i j)).permanent = C * X := by
      rw [ih haS (d + 1) hd' _ ?_ ?_]
      · rw [hC, hX]
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [prod_ite_mul, if_neg haS, if_pos rfl, hprodins S' subset_rfl]
        ring
      · intro Q hQ hne _
        have : ∀ j, ∏ i ∈ Q, (if i = a then r a j * r i0 j else r i j) = ∏ i ∈ Q, r i j := by
          intro j
          rw [prod_ite_mul, if_neg (fun h => haS (hQ h)), mul_one]
        simp_rw [this]
        exact hsub Q hQ hne
      · intro hne
        right
        have : ∀ j, ∏ i ∈ S', (if i = a then r a j * r i0 j else r i j) = ∏ i ∈ S', r i j := by
          intro j
          rw [prod_ite_mul, if_neg haS, mul_one]
        simp_rw [this]
        exact hsub S' subset_rfl hne
    -- the terms k ∈ S'
    have htk : ∀ k ∈ S', (rowMat (insert a S')
        (fun i j => if i = k then r k j * r i0 j else r i j)).permanent = C * X := by
      intro k hk
      have hak : a ≠ k := fun h => haS (h ▸ hk)
      rw [ih haS (d + 1) hd' _ ?_ ?_]
      · rw [hC, hX]
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [prod_ite_mul, if_pos hk, if_neg hak, hprodins S' subset_rfl]
      · intro Q hQ hne hneq
        by_cases hkQ : k ∈ Q
        · have : ∀ j, ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) =
              ∏ i ∈ insert i0 Q, r i j := by
            intro j
            rw [prod_ite_mul, if_pos hkQ, hprodins Q hQ]
          simp_rw [this]
          exact hsub2 Q hQ hneq
        · have : ∀ j, ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) = ∏ i ∈ Q, r i j := by
            intro j
            rw [prod_ite_mul, if_neg hkQ, mul_one]
          simp_rw [this]
          exact hsub Q hQ hne
      · intro _
        rcases h2 (insert_nonempty _ _) with h | h
        · left
          simpa [hak] using h
        · right
          have : ∀ j, ∏ i ∈ S', (if i = k then r k j * r i0 j else r i j) =
              ∏ i ∈ insert i0 S', r i j := by
            intro j
            rw [prod_ite_mul, if_pos hk, hprodins S' subset_rfl]
          simp_rw [this]
          exact h
    have hcompl : (insert a S')ᶜ.card = d + 1 := by
      rw [card_compl, Fintype.card_fin, card_insert_of_notMem haS]
      omega
    rw [hleft, hcompl, sum_insert haS, hta, sum_congr rfl htk, sum_const, nsmul_eq_mul,
      Finset.insert_comm] at hrec
    have hne : ((d : ℂ) + 1) ≠ 0 := by
      have : (((d + 1 : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simpa using this
    apply mul_left_cancel₀ hne
    rw [hcard]
    have hC' : C = ((d : ℂ) + 1) * (d.factorial : ℂ) * (-1) ^ S'.card *
        (S'.card.factorial : ℂ) := by
      rw [hC, Nat.factorial_succ]
      push_cast
      ring
    rw [Nat.factorial_succ S'.card]
    push_cast at hrec ⊢
    rw [hC'] at hrec
    linear_combination -hrec

/-- The standard bilinear form as a map into the dual. -/
noncomputable def dot : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun u v => ∑ j, u j * v j)
    (fun u u' v => by simp [add_mul, sum_add_distrib])
    (fun c u v => by simp [mul_sum, mul_assoc])
    (fun u v v' => by simp [mul_add, sum_add_distrib])
    (fun c u v => by simp [mul_sum, mul_left_comm])

theorem dot_apply (u v : Fin m → ℂ) : dot u v = ∑ j, u j * v j := rfl

theorem dot_injective : Function.Injective (dot (m := m)) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  ext j
  have h : dot u (Pi.single j 1) = 0 := by rw [hu]; rfl
  rw [dot_apply] at h
  simpa [Pi.single_apply] using h

/-- A subspace orthogonal to `Z` has dimension at most the codimension of `Z`. -/
theorem finrank_add_le_of_orth (W Z : Submodule ℂ (Fin m → ℂ))
    (h : ∀ u ∈ W, ∀ v ∈ Z, ∑ j, u j * v j = 0) :
    Module.finrank ℂ W + Module.finrank ℂ Z ≤ m := by
  have hr : ∀ u : W, dot.domRestrict W u ∈ Z.dualAnnihilator := fun u =>
    (Submodule.mem_dualAnnihilator _).2 fun v hv => h u u.2 v hv
  have hinj : Function.Injective ((dot.domRestrict W).codRestrict Z.dualAnnihilator hr) :=
    fun a b hab => Subtype.ext (dot_injective (congrArg Subtype.val hab))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq Z
  have h3 : Module.finrank ℂ (Fin m → ℂ) = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

/-- A subspace containing a vector with coordinate `z` equal to one is at most one dimension
larger than its part with coordinate `z` zero. -/
theorem finrank_le_succ (U : Submodule ℂ (Fin m → ℂ)) (z : Fin m) (e : Fin m → ℂ) (he : e ∈ U)
    (hez : e z = 1) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ (U ⊓ LinearMap.ker (LinearMap.proj z : (Fin m → ℂ) →ₗ[ℂ] ℂ) :
        Submodule ℂ (Fin m → ℂ)) + 1 := by
  have hle : U ≤ (U ⊓ LinearMap.ker (LinearMap.proj z : (Fin m → ℂ) →ₗ[ℂ] ℂ)) ⊔
      Submodule.span ℂ {e} := by
    intro u hu
    have : u = (u - u z • e) + u z • e := by simp
    rw [this]
    refine Submodule.add_mem_sup ⟨U.sub_mem hu (U.smul_mem _ he), ?_⟩
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    simp [hez]
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (U ⊓ LinearMap.ker (LinearMap.proj z : (Fin m → ℂ) →ₗ[ℂ] ℂ)) (Submodule.span ℂ {e})
  have h3 : Module.finrank ℂ (Submodule.span ℂ {e}) = 1 :=
    finrank_span_singleton (fun h => by rw [h] at hez; simp at hez)
  omega

/-- L-gct-079 from the chain inequality. -/
theorem main
    (hchain : ∀ (n q : ℕ), 1 ≤ n → ∀ (V : Fin q → Submodule ℂ (Fin n → ℂ)),
      (∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
        (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0) →
      ∑ i : Fin q, Module.finrank ℂ (V i) + 1 ≤
        Module.finrank ℂ (Submodule.span ℂ
          {v : Fin n → ℂ | ∃ (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)),
            (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i}))
    (m : ℕ) (U : Fin m → Submodule ℂ (Fin m → ℂ)) (hm : 2 ≤ m)
    (hSig : ∀ i : Fin m, (fun j : Fin m =>
      if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℂ) - (m : ℂ) else 1) ∈ U i)
    (hperm : ∀ x : Fin m × Fin m → ℂ, (∀ i : Fin m, (fun j : Fin m => x (i, j)) ∈ U i) →
      MvPolynomial.eval x (PEqualNP.Gct.permPoly ℂ m) = 0) :
    ∑ i : Fin m, Module.finrank ℂ (U i) ≤ 2 * m - 2 := by
  classical
  set z : Fin m := ⟨0, by omega⟩ with hz
  have hzval : ∀ j : Fin m, (j : ℕ) = 0 ↔ j = z := fun j => by
    rw [hz, Fin.ext_iff]
  -- the rows of Sigma_m
  have hones : ∀ i : Fin m, i ≠ z → (fun _ : Fin m => (1 : ℂ)) ∈ U i := by
    intro i hi
    have h := hSig i
    have hi' : ¬ (i : ℕ) = 0 := fun h => hi ((hzval i).1 h)
    simpa [hi'] using h
  set y0 : Fin m → ℂ := fun j => if j = z then (1 : ℂ) - (m : ℂ) else 1 with hy0
  have hy0U : y0 ∈ U z := by
    have h := hSig z
    have : (fun j : Fin m => if ((z : Fin m) : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℂ) - (m : ℂ) else 1)
        = y0 := by
      funext j
      simp [hy0, hzval, hz]
    rwa [this] at h
  have hy0sum : ∑ j, y0 j = 0 := by
    have : ∀ j, y0 j = 1 - (if j = z then (m : ℂ) else 0) := by
      intro j
      by_cases hj : j = z <;> simp [hy0, hj]
    simp_rw [this]
    simp
  set K : Submodule ℂ (Fin m → ℂ) := LinearMap.ker (LinearMap.proj z : (Fin m → ℂ) →ₗ[ℂ] ℂ)
    with hK
  obtain ⟨V, hVdef⟩ : ∃ V : Fin m → Submodule ℂ (Fin m → ℂ),
      V = fun i => if i = z then ⊥ else U i ⊓ K := ⟨_, rfl⟩
  have hVz : V z = ⊥ := by rw [hVdef]; simp
  have hVne : ∀ i, i ≠ z → V i = U i ⊓ K := by
    intro i hi; rw [hVdef]; simp [hi]
  have hV0 : ∀ i (t : Fin m → ℂ), t ∈ V i → t z = 0 := by
    intro i t ht
    by_cases hi : i = z
    · subst hi
      rw [hVz, Submodule.mem_bot] at ht
      rw [ht]; rfl
    · rw [hVne i hi] at ht
      simpa [hK] using ht.2
  have hVU : ∀ i (t : Fin m → ℂ), i ≠ z → t ∈ V i → t ∈ U i := by
    intro i t hi ht
    rw [hVne i hi] at ht
    exact ht.1
  -- the permanent vanishes on the matrices built from the rows
  have key : ∀ (S : Finset (Fin m)) (w : Fin m → ℂ) (t : Fin m → Fin m → ℂ), z ∉ S → w ∈ U z →
      (∀ i ∈ S, t i ∈ V i) →
      (rowMat (insert z S) (fun i => if i = z then w else t i)).permanent = 0 := by
    intro S w t hzS hw ht
    have h := hperm (fun p => rowMat (insert z S) (fun i => if i = z then w else t i) p.1 p.2) ?_
    · rw [eval_permPoly] at h
      exact h
    · intro i
      by_cases hi : i = z
      · rw [hi]
        have : (fun j : Fin m => rowMat (insert z S) (fun i' => if i' = z then w else t i') z j)
            = w := by
          funext j; simp [rowMat_apply]
        rw [this]; exact hw
      · by_cases hiS : i ∈ S
        · have : (fun j : Fin m => rowMat (insert z S) (fun i' => if i' = z then w else t i') i j)
              = t i := by
            funext j; simp [rowMat_apply, hi, hiS]
          rw [this]; exact hVU i _ hi (ht i hiS)
        · have : (fun j : Fin m => rowMat (insert z S) (fun i' => if i' = z then w else t i') i j)
              = fun _ => 1 := by
            funext j; simp [rowMat_apply, hi, hiS]
          rw [this]; exact hones i hi
  have hprodeq : ∀ (S : Finset (Fin m)) (w : Fin m → ℂ) (t : Fin m → Fin m → ℂ), z ∉ S → ∀ j,
      ∏ i ∈ S, (if i = z then w else t i) j = ∏ i ∈ S, t i j := by
    intro S w t hzS j
    refine prod_congr rfl fun i hi => ?_
    rw [if_neg (fun h : i = z => hzS (h ▸ hi))]
  have hcardS : ∀ S : Finset (Fin m), z ∉ S → S.card + 1 + (m - 1 - S.card) = m := by
    intro S hzS
    have h1 : (insert z S).card ≤ m := by
      simpa using card_le_univ (insert z S)
    rw [card_insert_of_notMem hzS] at h1
    omega
  have hconst : ∀ (d s : ℕ), (d.factorial : ℂ) * (-1) ^ s * (s.factorial : ℂ) ≠ 0 := by
    intro d s
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    · exact pow_ne_zero _ (by norm_num)
    · exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  -- (I): the entry sum of a product over a nonempty set of rows vanishes
  have hI0 : ∀ (n : ℕ) (S : Finset (Fin m)), S.card = n → z ∉ S → S.Nonempty →
      ∀ t : Fin m → Fin m → ℂ, (∀ i ∈ S, t i ∈ V i) → ∑ j, ∏ i ∈ S, t i j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hSn hzS hSne t ht
      have hform := rowMat_perm_formula z S hzS (m - 1 - S.card) (hcardS S hzS)
        (fun i => if i = z then y0 else t i) ?_ ?_
      · rw [key S y0 t hzS hy0U ht] at hform
        have hsum := (mul_eq_zero.1 hform.symm).resolve_left (hconst _ _)
        rw [← hsum]
        refine sum_congr rfl fun j _ => ?_
        rw [if_pos rfl, hprodeq S y0 t hzS j]
        by_cases hj : j = z
        · subst hj
          obtain ⟨x, hx⟩ := hSne
          rw [prod_eq_zero hx (hV0 x _ (ht x hx))]
          ring
        · simp [hy0, hj]
      · intro Q hQ hQne hQS
        simp_rw [hprodeq Q y0 t (fun h => hzS (hQ h))]
        have hlt : Q.card < S.card := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hQ, hQS⟩)
        exact ih Q.card (hSn ▸ hlt) Q rfl (fun h => hzS (hQ h)) hQne t (fun i hi => ht i (hQ hi))
      · intro _
        left
        simpa using hy0sum
  have hI : ∀ S : Finset (Fin m), S.Nonempty → ∀ t : Fin m → (Fin m → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin m, ∏ i ∈ S, t i j = 0 := by
    intro S hSne t ht
    by_cases hzS : z ∈ S
    · refine sum_eq_zero fun j _ => prod_eq_zero hzS ?_
      have := ht z hzS
      rw [hVz, Submodule.mem_bot] at this
      rw [this]; rfl
    · exact hI0 S.card S rfl hzS hSne t ht
  have hch := hchain m m (by omega) V hI
  set Z : Submodule ℂ (Fin m → ℂ) := Submodule.span ℂ
    {v : Fin m → ℂ | ∃ (S : Finset (Fin m)) (t : Fin m → (Fin m → ℂ)),
      (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i} with hZ
  -- row zero is orthogonal to Z
  have horth : ∀ u ∈ U z, ∀ v ∈ Z, ∑ j, u j * v j = 0 := by
    intro u hu v hv
    have hle : Z ≤ LinearMap.ker (dot u) := by
      rw [hZ, Submodule.span_le]
      rintro v ⟨S, t, ht, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, dot_apply]
      simp_rw [Finset.prod_apply]
      by_cases hzS : z ∈ S
      · refine sum_eq_zero fun j _ => ?_
        have := ht z hzS
        rw [hVz, Submodule.mem_bot] at this
        rw [prod_eq_zero hzS (by rw [this]; rfl), mul_zero]
      · have hform := rowMat_perm_formula z S hzS (m - 1 - S.card) (hcardS S hzS)
          (fun i => if i = z then u else t i) ?_ ?_
        · rw [key S u t hzS hu ht] at hform
          have hsum := (mul_eq_zero.1 hform.symm).resolve_left (hconst _ _)
          rw [← hsum]
          refine sum_congr rfl fun j _ => ?_
          rw [if_pos rfl, hprodeq S u t hzS j]
        · intro Q hQ hQne _
          simp_rw [hprodeq Q u t (fun h => hzS (hQ h))]
          exact hI Q hQne t (fun i hi => ht i (hQ hi))
        · intro hSne
          right
          simp_rw [hprodeq S u t hzS]
          exact hI S hSne t ht
    have := hle hv
    rwa [LinearMap.mem_ker, dot_apply] at this
  have hdim0 := finrank_add_le_of_orth (U z) Z horth
  -- the other rows
  have hrow : ∀ i ∈ univ.erase z, Module.finrank ℂ (U i) ≤ Module.finrank ℂ (V i) + 1 := by
    intro i hi
    have hiz : i ≠ z := (mem_erase.1 hi).1
    rw [hVne i hiz]
    exact finrank_le_succ (U i) z (fun _ => 1) (hones i hiz) rfl
  have hsumU : ∑ i, Module.finrank ℂ (U i) =
      Module.finrank ℂ (U z) + ∑ i ∈ univ.erase z, Module.finrank ℂ (U i) :=
    (add_sum_erase univ _ (mem_univ z)).symm
  have hsumV : ∑ i, Module.finrank ℂ (V i) = ∑ i ∈ univ.erase z, Module.finrank ℂ (V i) := by
    rw [← add_sum_erase univ _ (mem_univ z), hVz, finrank_bot, zero_add]
  have hle := sum_le_sum hrow
  rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at hle
  omega

end PEqualNP.Gct.Helpers.ProdSigma
