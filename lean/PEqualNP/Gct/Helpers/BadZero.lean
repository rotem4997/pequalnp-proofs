import PEqualNP.Gct.Helpers.MethodCeiling

/-! Helper module, proofs only. A zero of the permanent with a large linear space through it
inside the permanent hypersurface. For `m = k + 2` the point `badZero k` is the matrix in blocks
`[[-1, e1ᵀ], [e1, I]]`: entry `(0, 0)` is `-1`, entries `(0, 1)` and `(1, 0)` are `1`, the
diagonal entries `(i, i)` with `0 < i` are `1`, and every other entry is `0`. The space
`upperSpace k` is the space of points supported on the pairs `(i, j)` with `0 < i < j`. The
permanent vanishes on `badZero k + t` for every `t` in `upperSpace k`, and `upperSpace k` has
dimension `(k + 1) * k / 2`. -/

namespace PEqualNP.Gct.Helpers.BadZero

open Finset

/-- A permutation of `Fin n` that moves no index up is the identity. -/
theorem perm_eq_one_of_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : ∀ c, σ c ≤ c) : σ = 1 := by
  have key : ∀ N : ℕ, ∀ c : Fin n, (c : ℕ) = N → σ c = c := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro c hc
      rcases (h c).eq_or_lt with h1 | h1
      · exact h1
      · exfalso
        have h2 : σ (σ c) = σ c := ih (σ c : ℕ) (by rw [← hc]; exact h1) (σ c) rfl
        exact h1.ne (σ.injective h2)
  exact Equiv.ext fun c => key c c rfl

/-- The zero: the matrix in blocks `[[-1, e1ᵀ], [e1, I]]`. -/
def badZero (k : ℕ) : Fin (k + 2) × Fin (k + 2) → ℂ :=
  fun p => if p = (0, 0) then -1 else if p.1 = p.2 ∨ p = (0, 1) ∨ p = (1, 0) then 1 else 0

/-- The points supported on the strictly upper triangle of the lower right block. -/
def upperSpace (k : ℕ) : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ) where
  carrier := {t | ∀ p : Fin (k + 2) × Fin (k + 2), ¬ (0 < p.1 ∧ p.1 < p.2) → t p = 0}
  add_mem' := by
    intro a b ha hb p hp
    simp [ha p hp, hb p hp]
  zero_mem' := by
    intro p _
    rfl
  smul_mem' := by
    intro c a ha p hp
    simp [ha p hp]

theorem mem_upperSpace {k : ℕ} {t : Fin (k + 2) × Fin (k + 2) → ℂ} :
    t ∈ upperSpace k ↔ ∀ p : Fin (k + 2) × Fin (k + 2), ¬ (0 < p.1 ∧ p.1 < p.2) → t p = 0 :=
  Iff.rfl

/-- Where the entries of `badZero k + t` can be nonzero. -/
theorem entry_ne_zero {k : ℕ} {t : Fin (k + 2) × Fin (k + 2) → ℂ} (ht : t ∈ upperSpace k)
    (r c : Fin (k + 2)) (h : (badZero k + t) (r, c) ≠ 0) :
    (r = 0 ∧ c = 0) ∨ (r = 0 ∧ c = 1) ∨ (r = 1 ∧ c = 0) ∨ (0 < r ∧ r ≤ c) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  apply h
  have ht0 : t (r, c) = 0 := by
    apply ht
    rintro ⟨ha, hb⟩
    exact lt_asymm (h4 ha) hb
  have hrc : r ≠ c := by
    rintro rfl
    rcases eq_or_ne r 0 with h0 | h0
    · exact h1 h0 h0
    · exact lt_irrefl _ (h4 (Fin.pos_iff_ne_zero.mpr h0))
  have hb : badZero k (r, c) = 0 := by
    unfold badZero
    rw [ite_eq_right, ite_eq_right]
    · rintro (h5 | h5 | h5)
      · exact hrc h5
      · exact h2 (congrArg Prod.fst h5) (congrArg Prod.snd h5)
      · exact h3 (congrArg Prod.fst h5) (congrArg Prod.snd h5)
    · intro h5
      exact h1 (congrArg Prod.fst h5) (congrArg Prod.snd h5)
  rw [Pi.add_apply, hb, ht0, add_zero]

/-- A permutation along which no entry of `badZero k + t` vanishes is the identity or the
transposition of `0` and `1`. -/
theorem perm_eq_of_entries_ne_zero {k : ℕ} {t : Fin (k + 2) × Fin (k + 2) → ℂ}
    (ht : t ∈ upperSpace k) (σ : Equiv.Perm (Fin (k + 2)))
    (h : ∀ c, (badZero k + t) (σ c, c) ≠ 0) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  have h01 : (0 : Fin (k + 2)) ≠ 1 := by
    intro h0
    have := congrArg Fin.val h0
    simp at this
  have hE := fun c => entry_ne_zero ht (σ c) c (h c)
  have hs0 : σ 0 = 0 ∨ σ 0 = 1 := by
    rcases hE 0 with h0 | h0 | h0 | h0
    · exact Or.inl h0.1
    · exact Or.inl h0.1
    · exact Or.inr h0.1
    · exact absurd (lt_of_lt_of_le h0.1 h0.2) (lt_irrefl _)
  rcases hs0 with hs0 | hs0
  · left
    apply perm_eq_one_of_le
    intro c
    rcases hE c with h0 | h0 | h0 | h0
    · rw [h0.1]; exact Fin.zero_le _
    · rw [h0.1]; exact Fin.zero_le _
    · exfalso
      rw [h0.2, hs0] at h0
      exact h01 h0.1
    · exact h0.2
  · right
    have hs1 : σ 1 = 0 := by
      rcases hE 1 with h0 | h0 | h0 | h0
      · exact h0.1
      · exact h0.1
      · exact absurd h0.2.symm h01
      · exfalso
        have h5 : σ 1 = 1 := le_antisymm h0.2 (Fin.one_le_of_ne_zero h0.1.ne')
        exact h01 (σ.injective (hs0.trans h5.symm))
    have hτ : σ * Equiv.swap 0 1 = 1 := by
      apply perm_eq_one_of_le
      intro c
      rw [Equiv.Perm.mul_apply]
      by_cases hc0 : c = 0
      · subst hc0
        rw [Equiv.swap_apply_left, hs1]
      by_cases hc1 : c = 1
      · subst hc1
        rw [Equiv.swap_apply_right, hs0]
      rw [Equiv.swap_apply_of_ne_of_ne hc0 hc1]
      rcases hE c with h0 | h0 | h0 | h0
      · exact absurd h0.2 hc0
      · exact absurd h0.2 hc1
      · exact absurd h0.2 hc0
      · exact h0.2
    have h6 : σ = (σ * Equiv.swap 0 1) * Equiv.swap 0 1 := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    rw [h6, hτ, one_mul]

/-- The permanent vanishes on `badZero k + t` for every `t` in `upperSpace k`. -/
theorem eval_badZero_add {k : ℕ} {t : Fin (k + 2) × Fin (k + 2) → ℂ} (ht : t ∈ upperSpace k) :
    MvPolynomial.eval (badZero k + t) (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0 := by
  have h01 : (0 : Fin (k + 2)) ≠ 1 := by
    intro h0
    have := congrArg Fin.val h0
    simp at this
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly]
  unfold Matrix.permanent
  simp only [Matrix.of_apply]
  have hsub : ∑ σ : Equiv.Perm (Fin (k + 2)), ∏ c, (badZero k + t) (σ c, c) =
      ∑ σ ∈ ({1, Equiv.swap 0 1} : Finset (Equiv.Perm (Fin (k + 2)))),
        ∏ c, (badZero k + t) (σ c, c) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro σ _ hσ
    by_contra hne
    have hall : ∀ c, (badZero k + t) (σ c, c) ≠ 0 := by
      intro c hc
      exact hne (Finset.prod_eq_zero (Finset.mem_univ c) hc)
    rcases perm_eq_of_entries_ne_zero ht σ hall with h1 | h1
    · exact hσ (by simp [h1])
    · exact hσ (by simp [h1])
  have hswap : (1 : Equiv.Perm (Fin (k + 2))) ≠ Equiv.swap 0 1 := by
    intro h0
    have := congrArg (fun τ : Equiv.Perm (Fin (k + 2)) => τ 0) h0
    simp at this
  have hdiag : ∀ c : Fin (k + 2), c ≠ 0 → (badZero k + t) (c, c) = 1 := by
    intro c hc
    have ht0 : t (c, c) = 0 := ht _ (fun h => lt_irrefl _ h.2)
    have hb : badZero k (c, c) = 1 := by
      unfold badZero
      rw [ite_eq_right (fun h5 => hc (congrArg Prod.fst h5)), ite_eq_left (Or.inl rfl)]
    rw [Pi.add_apply, hb, ht0, add_zero]
  have h00 : (badZero k + t) (0, 0) = -1 := by
    have ht0 : t ((0 : Fin (k + 2)), (0 : Fin (k + 2))) = 0 := ht _ (fun h => lt_irrefl _ h.2)
    rw [Pi.add_apply, ht0, add_zero]
    simp [badZero]
  have h0l : (badZero k + t) (0, 1) = 1 := by
    have ht0 : t ((0 : Fin (k + 2)), (1 : Fin (k + 2))) = 0 := ht _ (fun h => lt_irrefl _ h.1)
    have hb : badZero k (0, 1) = 1 := by
      unfold badZero
      rw [ite_eq_right (fun h5 => h01 (congrArg Prod.snd h5).symm), ite_eq_left (Or.inr (Or.inl rfl))]
    rw [Pi.add_apply, hb, ht0, add_zero]
  have h10 : (badZero k + t) (1, 0) = 1 := by
    have ht0 : t ((1 : Fin (k + 2)), (0 : Fin (k + 2))) = 0 :=
      ht _ (fun h => absurd h.2 (Fin.not_lt_zero _))
    have hb : badZero k (1, 0) = 1 := by
      unfold badZero
      rw [ite_eq_right (fun h5 => h01 (congrArg Prod.fst h5).symm), ite_eq_left (Or.inr (Or.inr rfl))]
    rw [Pi.add_apply, hb, ht0, add_zero]
  have hone : ∏ c : Fin (k + 2), (badZero k + t) ((1 : Equiv.Perm (Fin (k + 2))) c, c) = -1 := by
    rw [Fin.prod_univ_succ]
    simp only [Equiv.Perm.one_apply]
    rw [h00, Finset.prod_eq_one (fun c _ => hdiag _ (Fin.succ_ne_zero c)), mul_one]
  have htwo : ∏ c : Fin (k + 2), (badZero k + t) (Equiv.swap (0 : Fin (k + 2)) 1 c, c) = 1 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have hs1 : (Fin.succ (0 : Fin (k + 1)) : Fin (k + 2)) = 1 := rfl
    rw [Equiv.swap_apply_left, hs1, Equiv.swap_apply_right, h10, h0l]
    rw [Finset.prod_eq_one, mul_one, mul_one]
    intro c _
    have hc0 : (Fin.succ (Fin.succ c) : Fin (k + 2)) ≠ 0 := Fin.succ_ne_zero _
    have hc1 : (Fin.succ (Fin.succ c) : Fin (k + 2)) ≠ 1 := by
      intro h5
      rw [← hs1] at h5
      exact Fin.succ_ne_zero c (Fin.succ_injective _ h5)
    rw [Equiv.swap_apply_of_ne_of_ne hc0 hc1]
    exact hdiag _ hc0
  rw [hsub, Finset.sum_pair hswap, hone, htwo]
  norm_num

/-- The permanent vanishes at `badZero k`. -/
theorem eval_badZero (k : ℕ) :
    MvPolynomial.eval (badZero k) (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0 := by
  have h := eval_badZero_add (k := k) (upperSpace k).zero_mem
  rwa [add_zero] at h

/-- `upperSpace k` is the space of functions on its support. -/
noncomputable def upperSpaceEquiv (k : ℕ) :
    upperSpace k ≃ₗ[ℂ]
      ({p : Fin (k + 2) × Fin (k + 2) // 0 < p.1 ∧ p.1 < p.2} → ℂ) where
  toFun t := fun s => t.1 s.1
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro c a
    rfl
  invFun g := ⟨fun p => if h : 0 < p.1 ∧ p.1 < p.2 then g ⟨p, h⟩ else 0, by
    intro p hp
    simp only [dite_eq_right hp]⟩
  left_inv := by
    intro t
    apply Subtype.ext
    funext p
    by_cases hp : 0 < p.1 ∧ p.1 < p.2
    · simp only [dite_eq_left hp]
    · simp only [dite_eq_right hp]
      exact (t.2 p hp).symm
  right_inv := by
    intro g
    funext s
    simp only [dite_eq_left s.2]

/-- The number of pairs `(i, j)` with `0 < i < j` in `Fin (k + 2)`, doubled. -/
theorem two_mul_card_support (k : ℕ) :
    2 * Fintype.card {p : Fin (k + 2) × Fin (k + 2) // 0 < p.1 ∧ p.1 < p.2} = (k + 1) * k := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have hinner : ∀ j : Fin (k + 2),
      (∑ i : Fin (k + 2), if 0 < i ∧ i < j then 1 else 0) = (j : ℕ) - 1 := by
    intro j
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun i : Fin (k + 2) => 0 < i ∧ i < j) = Finset.Ioo 0 j := by
      ext i
      simp
    rw [this, Fin.card_Ioo]
    simp
  simp only [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun j => j - 1) (k + 2), Finset.sum_range_succ',
    Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.zero_sub, add_zero, zero_add, Nat.sub_self]
  have h := Finset.sum_range_id_mul_two (k + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [mul_comm]
  rw [Finset.sum_range_succ'] at h
  simpa using h

/-- The dimension of `upperSpace k`, doubled. -/
theorem two_mul_finrank_upperSpace (k : ℕ) :
    2 * Module.finrank ℂ (upperSpace k) = (k + 1) * k := by
  rw [LinearEquiv.finrank_eq (upperSpaceEquiv k), Module.finrank_fintype_fun_eq_card]
  exact two_mul_card_support k

/-- A zero of the permanent of size `k + 2` with a linear space of dimension `(k + 1) * k / 2`
through it inside the permanent hypersurface. -/
theorem bad_zero : ∀ k : ℕ, ∃ (y : Fin (k + 2) × Fin (k + 2) → ℂ)
    (L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ)),
    MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0 ∧
    (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0) ∧
    2 * Module.finrank ℂ L = (k + 1) * k :=
  fun k => ⟨badZero k, upperSpace k, eval_badZero k, fun _ ht => eval_badZero_add ht,
    two_mul_finrank_upperSpace k⟩

end PEqualNP.Gct.Helpers.BadZero
