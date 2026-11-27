import PEqualNP.ProofComplexity.Helpers.Critical
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify

/-!
# Helpers: a medium clause is wide

For a clause `C` whose least implying set `S` has `t` pigeons, with `f` free pigeons, the
monotone image of `C` holds at least `t * (f - t)` pairs of a free pigeon and a free hole:
for `i` in `S` take a critical assignment leaving `i` out and falsifying `C`, and swap `i`
with each free pigeon `j` outside `S`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

/-- The swap step: `e` leaves `i` out and falsifies `C`; seating `i` in the hole `l` of a
free pigeon `j` satisfies `C`; then `(i, l)` is in the monotone image of `C`. -/
theorem mem_mono_of_swap {n : ℕ} {C : Clause (PVar n)} {e : Crit n} {i j : Fin (n + 1)}
    {l : Fin n} (hei : e i = none) (hej : e j = some l) (hfalse : ¬ ClauseSat (asg e) C)
    (hsat : ClauseSat (asg ((Equiv.swap i j).trans e)) C) : (i, l) ∈ mono C := by
  obtain ⟨⟨⟨p, q⟩, s⟩, hlit, hval⟩ := hsat
  have hval' : asg e (p, q) ≠ s := fun h => hfalse ⟨((p, q), s), hlit, h⟩
  cases s
  · have h1 : e (Equiv.swap i j p) ≠ some q := of_decide_eq_false hval
    have h2 : e p = some q := by simpa [asg] using hval'
    by_cases hpi : p = i
    · subst hpi
      rw [hei] at h2
      exact absurd h2 (Option.some_ne_none q).symm
    · by_cases hpj : p = j
      · subst hpj
        have hq : l = q := Option.some.inj (hej.symm.trans h2)
        subst hq
        exact mem_mono.mpr (Or.inr ⟨p, hpi, hlit⟩)
      · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at h1
        exact absurd h2 h1
  · have h1 : e (Equiv.swap i j p) = some q := of_decide_eq_true hval
    have h2 : e p ≠ some q := by simpa [asg] using hval'
    by_cases hpi : p = i
    · subst hpi
      rw [Equiv.swap_apply_left, hej] at h1
      have hq : l = q := Option.some.inj h1
      subst hq
      exact mem_mono.mpr (Or.inl hlit)
    · by_cases hpj : p = j
      · subst hpj
        rw [Equiv.swap_apply_right, hei] at h1
        exact absurd h1 (Option.some_ne_none q).symm
      · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at h1
        exact absurd h1 h2

theorem medium_wide {n : ℕ} {ρ : Finset (PVar n)} {C : Clause (PVar n)} (hmed : Medium ρ C) :
    (∀ p ∈ ρ, p ∉ mono C) ∧ 2 * (freeP ρ).card ^ 2 ≤ 9 * (monoFree ρ C).card := by
  classical
  obtain ⟨S, hS, hmin, hlo, hhi⟩ := hmed
  refine ⟨?_, ?_⟩
  · intro p hpρ hp
    have h0 : Imp ρ ∅ C := fun e he _ => sat_of_mem_mono hp (he p hpρ)
    have := hmin ∅ h0
    rw [Finset.card_empty] at this
    omega
  -- for each pigeon of `S`, a critical assignment leaving it out and falsifying `C`
  have key : ∀ i ∈ S, ∃ e : Crit n, Ext ρ e ∧ e i = none ∧ ¬ ClauseSat (asg e) C ∧
      ∀ i' ∈ S, i' ≠ i → e i' ≠ none := by
    intro i hi
    have hnot : ¬ Imp ρ (S.erase i) C := by
      intro h
      have h1 := hmin _ h
      have h2 := Finset.card_erase_lt_of_mem hi
      omega
    simp only [Imp, not_forall] at hnot
    obtain ⟨e, he, herase, hfalse⟩ := hnot
    have hrest : ∀ i' ∈ S, i' ≠ i → e i' ≠ none :=
      fun i' hi' hne => herase i' (Finset.mem_erase.mpr ⟨hne, hi'⟩)
    refine ⟨e, he, ?_, hfalse, hrest⟩
    by_contra hei
    apply hfalse
    apply hS e he
    intro i' hi'
    by_cases h : i' = i
    · rw [h]; exact hei
    · exact hrest i' hi' h
  have hSfree : S ⊆ freeP ρ := by
    intro i hi
    obtain ⟨e, he, hei, -, -⟩ := key i hi
    refine mem_freeP.mpr fun p hp hpi => ?_
    have := he p hp
    rw [hpi, hei] at this
    exact Option.some_ne_none _ this.symm
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hlo
  obtain ⟨i₀, hi₀⟩ := hSne
  obtain ⟨e₀, -⟩ := key i₀ hi₀
  have : Nonempty (Crit n) := ⟨e₀⟩
  choose! E hE using key
  -- the injection
  let g : Fin (n + 1) × Fin (n + 1) → Fin (n + 1) × Option (Fin n) := fun x => (x.1, E x.1 x.2)
  let emb : PVar n → Fin (n + 1) × Option (Fin n) := fun p => (p.1, some p.2)
  have hsub : (S ×ˢ (freeP ρ \ S)).image g ⊆ (monoFree ρ C).image emb := by
    intro y hy
    obtain ⟨⟨i, j⟩, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hx
    obtain ⟨hjfree, hjS⟩ := Finset.mem_sdiff.mp hj
    simp only at hi hjfree hjS
    obtain ⟨hext, hei, hfalse, hrest⟩ := hE i hi
    have hij : i ≠ j := fun h => hjS (h ▸ hi)
    have hejne : E i j ≠ none := fun h => hij ((E i).injective (hei.trans h.symm))
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hejne
    have hifree := hSfree hi
    have hsat : ClauseSat (asg ((Equiv.swap i j).trans (E i))) C := by
      apply hS
      · intro p hp
        have h1 : p.1 ≠ i := mem_freeP.mp hifree p hp
        have h2 : p.1 ≠ j := mem_freeP.mp hjfree p hp
        rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact hext p hp
      · intro i' hi'
        rw [Equiv.trans_apply]
        by_cases h : i' = i
        · rw [h, Equiv.swap_apply_left, hl]; exact Option.some_ne_none l
        · have h2 : i' ≠ j := fun h' => hjS (h' ▸ hi')
          rw [Equiv.swap_apply_of_ne_of_ne h h2]
          exact hrest i' hi' h
    have hmem := mem_mono_of_swap hei hl hfalse hsat
    have hlfree : l ∈ freeH ρ := by
      refine mem_freeH.mpr fun p hp hpl => ?_
      have h1 := hext p hp
      rw [hpl, ← hl] at h1
      exact mem_freeP.mp hjfree p hp ((E i).injective h1)
    refine Finset.mem_image.mpr ⟨(i, l), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hmem, hifree, hlfree⟩
    · simp [emb, g, hl]
  have hginj : Set.InjOn g ↑(S ×ˢ (freeP ρ \ S)) := by
    rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [(E i).injective h2]
  have hcard : S.card * ((freeP ρ).card - S.card) ≤ (monoFree ρ C).card := by
    calc S.card * ((freeP ρ).card - S.card)
        = (S ×ˢ (freeP ρ \ S)).card := by
          rw [Finset.card_product, Finset.card_sdiff_of_subset hSfree]
      _ = ((S ×ˢ (freeP ρ \ S)).image g).card := (Finset.card_image_of_injOn hginj).symm
      _ ≤ ((monoFree ρ C).image emb).card := Finset.card_le_card hsub
      _ ≤ (monoFree ρ C).card := Finset.card_image_le
  have hle := Finset.card_le_card hSfree
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hle
  rw [hu] at hlo hhi ⊢
  rw [hu, Nat.add_sub_cancel_left] at hcard
  have h1 : u ≤ 2 * S.card := by omega
  have h2 : S.card ≤ 2 * u := by omega
  have h3 : 2 * (S.card + u) ^ 2 ≤ 9 * (S.card * u) := by
    zify at h1 h2 ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  omega

end PEqualNP.ProofComplexity.Helpers
