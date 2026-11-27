import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L090

namespace PEqualNP.Outside.RowProduct

/- The row expansion below follows `PEqualNP.Gct.Helpers.ProdSigma` through
`rowMat_perm_formula`. It expresses the permanent with selected rows replaced
in terms of sums of coordinatewise row products. -/

open Finset

variable {m : ℕ}

private theorem eval_permPoly (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- Multiplying the rows one at a time pointwise by `v` and adding the permanents gives the sum
of the entries of `v` times the permanent. -/
private theorem sum_mul_permanent (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
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
private def rowMat (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i ∈ T then r i j else 1

private theorem rowMat_apply (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (i j : Fin m) :
    rowMat T r i j = if i ∈ T then r i j else 1 := rfl

/-- The recursion: making one more row special. -/
private theorem rowMat_rec (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (i0 : Fin m) (hi0 : i0 ∉ T) :
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

private theorem permanent_ones : (rowMat (∅ : Finset (Fin m)) fun _ _ => 0).permanent
    = (m.factorial : ℂ) := by
  simp [Matrix.permanent, rowMat, Fintype.card_perm]

private theorem rowMat_empty (r r' : Fin m → Fin m → ℂ) :
    rowMat (∅ : Finset (Fin m)) r = rowMat ∅ r' := by
  ext a b
  simp [rowMat_apply]

/-- One special row. -/
private theorem rowMat_single (a : Fin m) (d : ℕ) (hd : 1 + d = m) (r : Fin m → Fin m → ℂ) :
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

private theorem prod_ite_mul (Q : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (k i0 j : Fin m) :
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
private theorem rowMat_perm_formula (a : Fin m) : ∀ S : Finset (Fin m), a ∉ S → ∀ d : ℕ,
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
        rw [prod_ite_mul, ite_eq_right haS, ite_eq_left rfl, hprodins S' subset_rfl]
        ring
      · intro Q hQ hne _
        have : ∀ j, ∏ i ∈ Q, (if i = a then r a j * r i0 j else r i j) = ∏ i ∈ Q, r i j := by
          intro j
          rw [prod_ite_mul, ite_eq_right (fun h => haS (hQ h)), mul_one]
        simp_rw [this]
        exact hsub Q hQ hne
      · intro hne
        right
        have : ∀ j, ∏ i ∈ S', (if i = a then r a j * r i0 j else r i j) = ∏ i ∈ S', r i j := by
          intro j
          rw [prod_ite_mul, ite_eq_right haS, mul_one]
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
        rw [prod_ite_mul, ite_eq_left hk, ite_eq_right hak, hprodins S' subset_rfl]
      · intro Q hQ hne hneq
        by_cases hkQ : k ∈ Q
        · have : ∀ j, ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) =
              ∏ i ∈ insert i0 Q, r i j := by
            intro j
            rw [prod_ite_mul, ite_eq_left hkQ, hprodins Q hQ]
          simp_rw [this]
          exact hsub2 Q hQ hneq
        · have : ∀ j, ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) = ∏ i ∈ Q, r i j := by
            intro j
            rw [prod_ite_mul, ite_eq_right hkQ, mul_one]
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
            rw [prod_ite_mul, ite_eq_left hk, hprodins S' subset_rfl]
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

/-- Expanding the permanent after perturbing any subset of rows gives the same
constant term. Induction on that subset forces every nonempty mixed term to vanish. -/
private theorem mixed_vanish {n : ℕ} (V : Fin n → Submodule ℂ (Fin n → ℂ))
    (hlevel : ∀ t : Fin n × Fin n → ℂ,
      (∀ i : Fin n, (fun j : Fin n => t (i, j)) ∈ V i) →
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
        (Nat.factorial n : ℂ)) (A : Finset (Fin n)) (hA : A.Nonempty)
    (r : Fin n → Fin n → ℂ) (hr : ∀ i ∈ A, r i ∈ V i) :
    (rowMat A r).permanent = 0 := by
  classical
  have horder (M : Matrix (Fin n) (Fin n) ℂ) :
      M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ.symm i) := by
    unfold Matrix.permanent
    refine sum_congr rfl fun σ _ => ?_
    simpa using (Equiv.prod_comp σ (fun i => M i (σ.symm i)))
  have hrow (B : Finset (Fin n)) :
      (rowMat B r).permanent =
        ∑ σ : Equiv.Perm (Fin n), ∏ i ∈ B, r i (σ.symm i) := by
    rw [horder]
    refine sum_congr rfl fun σ _ => ?_
    simp only [rowMat_apply]
    exact prod_ite_mem_eq B _
  have hsum (B : Finset (Fin n)) (hBA : B ⊆ A) :
      ∑ T ∈ B.powerset, (rowMat T r).permanent = (n.factorial : ℂ) := by
    let t : Fin n × Fin n → ℂ := fun p => if p.1 ∈ B then r p.1 p.2 else 0
    have ht (i : Fin n) : (fun j : Fin n => t (i, j)) ∈ V i := by
      by_cases hi : i ∈ B
      · simpa [t, hi] using hr i (hBA hi)
      · simp only [t, hi, ite_false]
        exact (V i).zero_mem
    have h := hlevel t ht
    rw [eval_permPoly, horder] at h
    rw [← h]
    simp_rw [hrow]
    rw [sum_comm]
    refine sum_congr rfl fun σ _ => ?_
    rw [← prod_one_add]
    change (∏ i ∈ B, (1 + r i (σ.symm i))) =
      ∏ i : Fin n, (1 + (if i ∈ B then r i (σ.symm i) else 0))
    calc
      _ = ∏ i : Fin n, (if i ∈ B then 1 + r i (σ.symm i) else 1) :=
        (prod_ite_mem_eq B _).symm
      _ = _ := prod_congr rfl fun i _ => by split_ifs <;> simp
  have hzero (k : ℕ) : ∀ B : Finset (Fin n), B.card = k → B ⊆ A → B.Nonempty →
      (rowMat B r).permanent = 0 := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro B hk hBA hB
      have hfull := hsum B hBA
      have hempty := hsum ∅ (empty_subset A)
      simp only [powerset_empty, sum_singleton] at hempty
      have hb : B ∈ B.powerset := mem_powerset.mpr (Subset.rfl)
      have he : ∅ ∈ B.powerset.erase B :=
        mem_erase.mpr ⟨Ne.symm hB.ne_empty, mem_powerset.mpr (empty_subset _)⟩
      rw [← add_sum_erase _ _ hb] at hfull
      have hrest : ∑ T ∈ B.powerset.erase B, (rowMat T r).permanent =
          (rowMat ∅ r).permanent := by
        apply sum_eq_single_of_mem ∅ he
        intro T hT hn
        obtain ⟨hne, hsub⟩ := mem_erase.mp hT
        have hTB := mem_powerset.mp hsub
        have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTB, hne⟩)
        exact ih T.card (hk ▸ hlt) T rfl (hTB.trans hBA) (nonempty_iff_ne_empty.mpr hn)
      rw [hrest, hempty] at hfull
      linear_combination hfull
  exact hzero A.card A rfl (Subset.rfl) hA

end PEqualNP.Outside.RowProduct

open Finset PEqualNP.Outside.RowProduct

theorem PEqualNP.Outside.L_gct_111 : ∀ (n : ℕ) (V : Fin n → Submodule ℂ (Fin n → ℂ)), (∀ t : Fin n × Fin n → ℂ, (∀ i : Fin n, (fun j : Fin n => t (i, j)) ∈ V i) → MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → ∑ i : Fin n, Module.finrank ℂ (V i) ≤ n - 1 := by
  classical
  intro n V hlevel
  apply PEqualNP.Gct.L090 n V
  -- The row expansion has a nonzero factorial coefficient on the full product
  -- once the coordinate sums for all proper nonempty subsets have vanished.
  have vanishing : ∀ (k : ℕ) (A : Finset (Fin n)), A.card = k → A.Nonempty →
      ∀ r : Fin n → Fin n → ℂ, (∀ i ∈ A, r i ∈ V i) → ∑ j, ∏ i ∈ A, r i j = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro A hAk hA r hr
      obtain ⟨a, ha⟩ := hA
      let S := A.erase a
      have haS : a ∉ S := by simp [S]
      have hSA : S ⊆ A := erase_subset _ _
      have hAS : insert a S = A := insert_erase ha
      have hcard : S.card + 1 = k := by
        rw [← card_insert_of_notMem haS, hAS, hAk]
      have hle : A.card ≤ n := by simpa using card_le_univ A
      have hd : S.card + 1 + (n - k) = n := by omega
      have smaller : ∀ Q : Finset (Fin n), Q ⊆ S → Q.Nonempty → ∑ j, ∏ i ∈ Q, r i j = 0 := by
        intro Q hQ hnQ
        have hleQ := card_le_card hQ
        exact ih Q.card (by omega) Q rfl hnQ r (fun i hi => hr i (hSA (hQ hi)))
      have hform := rowMat_perm_formula a S haS (n - k) hd r
        (fun Q hQ hnQ _ => smaller Q hQ hnQ)
        (fun hnS => Or.inr (smaller S (fun _ hi => hi) hnS))
      rw [hAS, mixed_vanish V hlevel A ⟨a, ha⟩ r hr] at hform
      have hcoef : ((n - k).factorial : ℂ) * (-1) ^ S.card * (S.card.factorial : ℂ) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
        · exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
        · exact pow_ne_zero _ (by norm_num)
        · exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hsum := (mul_eq_zero.1 hform.symm).resolve_left hcoef
      rw [← hAS]
      simpa only [prod_insert haS] using hsum
  exact fun A hA r hr => vanishing A.card A rfl hA r hr
