import Mathlib

/-!
# Matchings of the complete bipartite graph, for the row system of the rung

Helper for `PEqualNP.Gct.Rung.RowSystem` (statement in `Rung/Statements.lean`). Nothing here is a
result until the lemma that rests on it is checked.

A matching is a finite set of edges `(row, column)` with distinct rows and distinct columns.
`mpOn rows cols s W` is the sum over matchings of size `s` inside `rows × cols` of the product
of the weights `W` of the edges. Main facts: expansion along a row (`mpOn_row_expand`) and the
bijection that removes one edge (`sum_erase_bij`).
-/

namespace PEqualNP.Gct.Rung.RowSys

open Finset

variable {a b : ℕ}

/-- Distinct edges have distinct rows and distinct columns. -/
def IsMatch (M : Finset (Fin a × Fin b)) : Prop :=
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

noncomputable instance (M : Finset (Fin a × Fin b)) : Decidable (IsMatch M) :=
  Classical.dec _

/-- The matchings of size `s` with rows in `rows` and columns in `cols`. -/
noncomputable def matchings (rows : Finset (Fin a)) (cols : Finset (Fin b)) (s : ℕ) :
    Finset (Finset (Fin a × Fin b)) :=
  ((rows ×ˢ cols).powersetCard s).filter IsMatch

/-- The matching sum of size `s` inside `rows × cols` with edge weights `W`. -/
noncomputable def mpOn {R : Type*} [CommRing R] (rows : Finset (Fin a)) (cols : Finset (Fin b)) (s : ℕ)
    (W : Fin a × Fin b → R) : R :=
  ∑ M ∈ matchings rows cols s, ∏ e ∈ M, W e

theorem mem_matchings {rows : Finset (Fin a)} {cols : Finset (Fin b)} {s : ℕ}
    {M : Finset (Fin a × Fin b)} :
    M ∈ matchings rows cols s ↔ (M ⊆ rows ×ˢ cols ∧ M.card = s) ∧ IsMatch M := by
  simp [matchings, mem_powersetCard]

/-- Removing the edge `(i, c)` is a bijection from the matchings of size `s + 1` that contain it
to the matchings of size `s` that avoid row `i` and column `c`. -/
theorem sum_erase_bij {β : Type*} [AddCommMonoid β] {rows : Finset (Fin a)}
    {cols : Finset (Fin b)} {s : ℕ} {i : Fin a} {c : Fin b} (hi : i ∈ rows) (hc : c ∈ cols)
    (F : Finset (Fin a × Fin b) → β) :
    ∑ M ∈ (matchings rows cols (s + 1)).filter (fun M => (i, c) ∈ M), F (M.erase (i, c))
      = ∑ M' ∈ matchings (rows.erase i) (cols.erase c) s, F M' := by
  have hnot : ∀ M' ∈ matchings (rows.erase i) (cols.erase c) s, (i, c) ∉ M' := by
    intro M' hM' h
    have := (mem_matchings.mp hM').1.1 h
    simp at this
  refine Finset.sum_bij' (fun M _ => M.erase (i, c)) (fun M' _ => insert (i, c) M') ?_ ?_ ?_ ?_ ?_
  · intro M hM
    rw [mem_filter, mem_matchings] at hM
    obtain ⟨⟨⟨hsub, hcard⟩, hm1, hm2⟩, hmem⟩ := hM
    rw [mem_matchings]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro e he
      rw [mem_erase] at he
      have h := hsub he.2
      rw [mem_product] at h ⊢
      rw [mem_erase, mem_erase]
      exact ⟨⟨fun h' => he.1 (hm1 e he.2 (i, c) hmem h'), h.1⟩,
        ⟨fun h' => he.1 (hm2 e he.2 (i, c) hmem h'), h.2⟩⟩
    · rw [card_erase_of_mem hmem, hcard]; rfl
    · intro e he e' he' h
      exact hm1 e (mem_of_mem_erase he) e' (mem_of_mem_erase he') h
    · intro e he e' he' h
      exact hm2 e (mem_of_mem_erase he) e' (mem_of_mem_erase he') h
  · intro M' hM'
    have hn := hnot M' hM'
    rw [mem_matchings] at hM'
    obtain ⟨⟨hsub, hcard⟩, hm1, hm2⟩ := hM'
    have hrow : ∀ e ∈ M', e.1 ≠ i ∧ e.2 ≠ c := by
      intro e he
      have h := hsub he
      rw [mem_product, mem_erase, mem_erase] at h
      exact ⟨h.1.1, h.2.1⟩
    rw [mem_filter, mem_matchings]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, mem_insert_self _ _⟩
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · exact mem_product.mpr ⟨hi, hc⟩
      · have h := hsub he
        rw [mem_product, mem_erase, mem_erase] at h
        exact mem_product.mpr ⟨h.1.2, h.2.2⟩
    · rw [card_insert_of_notMem hn, hcard]
    · intro e he e' he' h
      rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp he' with rfl | he'
      · rfl
      · exact absurd h.symm (hrow e' he').1
      · exact absurd h (hrow e he).1
      · exact hm1 e he e' he' h
    · intro e he e' he' h
      rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp he' with rfl | he'
      · rfl
      · exact absurd h.symm (hrow e' he').2
      · exact absurd h (hrow e he).2
      · exact hm2 e he e' he' h
  · intro M hM
    exact insert_erase (mem_filter.mp hM).2
  · intro M' hM'
    exact erase_insert (hnot M' hM')
  · intro M _
    rfl

/-- The matchings with no edge in row `i` are the matchings on the other rows. -/
theorem matchings_filter_row {rows : Finset (Fin a)} {cols : Finset (Fin b)} {s : ℕ} (i : Fin a) :
    (matchings rows cols s).filter (fun M => ∀ e ∈ M, e.1 ≠ i) = matchings (rows.erase i) cols s := by
  ext M
  rw [mem_filter, mem_matchings, mem_matchings]
  constructor
  · rintro ⟨⟨⟨hsub, hcard⟩, hm⟩, hrow⟩
    refine ⟨⟨fun e he => ?_, hcard⟩, hm⟩
    have h := hsub he
    rw [mem_product] at h ⊢
    exact ⟨mem_erase.mpr ⟨hrow e he, h.1⟩, h.2⟩
  · rintro ⟨⟨hsub, hcard⟩, hm⟩
    refine ⟨⟨⟨fun e he => ?_, hcard⟩, hm⟩, fun e he => ?_⟩
    · have h := hsub he
      rw [mem_product] at h ⊢
      exact ⟨mem_of_mem_erase h.1, h.2⟩
    · have h := hsub he
      rw [mem_product] at h
      exact (mem_erase.mp h.1).1

/-- Expansion of the matching sum along a row. -/
theorem mpOn_row_expand {R : Type*} [CommRing R] {rows : Finset (Fin a)} {cols : Finset (Fin b)}
    {s : ℕ} {i : Fin a} (hi : i ∈ rows) (W : Fin a × Fin b → R) :
    mpOn rows cols (s + 1) W = mpOn (rows.erase i) cols (s + 1) W
      + ∑ c ∈ cols, W (i, c) * mpOn (rows.erase i) (cols.erase c) s W := by
  have key : ∀ M ∈ matchings rows cols (s + 1), ∏ e ∈ M, W e
      = (if ∀ e ∈ M, e.1 ≠ i then ∏ e ∈ M, W e else 0)
        + ∑ c ∈ cols, if (i, c) ∈ M then ∏ e ∈ M, W e else 0 := by
    intro M hM
    rw [mem_matchings] at hM
    obtain ⟨⟨hsub, _⟩, hm1, _⟩ := hM
    by_cases h : ∀ e ∈ M, e.1 ≠ i
    · rw [if_pos h, Finset.sum_eq_zero, add_zero]
      intro c _
      rw [if_neg]
      exact fun hc => h (i, c) hc rfl
    · rw [if_neg h, zero_add]
      push_neg at h
      obtain ⟨e, he, hei⟩ := h
      obtain ⟨p, c0⟩ := e
      simp only at hei
      subst hei
      have hc0 : c0 ∈ cols := (mem_product.mp (hsub he)).2
      rw [Finset.sum_eq_single c0, if_pos he]
      · intro c _ hne
        rw [if_neg]
        intro hc
        exact hne (congrArg Prod.snd (hm1 (p, c) hc (p, c0) he rfl))
      · intro h; exact absurd hc0 h
  unfold mpOn
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_filter, matchings_filter_row,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [← Finset.sum_filter, Finset.mul_sum, ← sum_erase_bij hi hc]
  refine Finset.sum_congr rfl fun M hM => ?_
  exact (Finset.mul_prod_erase M W (mem_filter.mp hM).2).symm

/-- The derivative of a product of distinct variables. -/
theorem pderiv_prod_X {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] (v : σ)
    (M : Finset σ) :
    MvPolynomial.pderiv v (∏ e ∈ M, (MvPolynomial.X e : MvPolynomial σ R))
      = if v ∈ M then ∏ e ∈ M.erase v, MvPolynomial.X e else 0 := by
  induction M using Finset.induction_on with
  | empty => simp
  | insert x M hx ih =>
    rw [Finset.prod_insert hx, Derivation.leibniz, ih, MvPolynomial.pderiv_X]
    by_cases hvx : v = x
    · subst hvx
      simp [hx]
    · have hxv : x ≠ v := fun h => hvx h.symm
      by_cases hvM : v ∈ M
      · have hxe : x ∉ M.erase v := fun h => hx (mem_of_mem_erase h)
        rw [if_pos hvM, if_pos (mem_insert_of_mem hvM), erase_insert_of_ne hxv,
          Finset.prod_insert hxe]
        simp [Pi.single_apply, hxv]
      · rw [if_neg hvM, if_neg (by simp [hvx, hvM])]
        simp [Pi.single_apply, hxv]

end PEqualNP.Gct.Rung.RowSys
