import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6692

-- The line through two distinct points.
noncomputable def ln {N : ℕ} (L : Fin N → Finset (Fin N))
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) (p p' : Fin N) : Fin N :=
  if h : p ≠ p' then Classical.choose (h2 p p' h).exists else p

theorem ln_spec {N : ℕ} (L : Fin N → Finset (Fin N))
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) {p p' : Fin N}
    (h : p ≠ p') : p ∈ L (ln L h2 p p') ∧ p' ∈ L (ln L h2 p p') := by
  unfold ln
  rw [dif_pos h]
  exact Classical.choose_spec (h2 p p' h).exists

theorem ln_eq {N : ℕ} (L : Fin N → Finset (Fin N))
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) {p p' : Fin N}
    (h : p ≠ p') (l : Fin N) (hp : p ∈ L l) (hp' : p' ∈ L l) : ln L h2 p p' = l :=
  (h2 p p' h).unique (ln_spec L h2 h) ⟨hp, hp'⟩

-- Every point lies on q + 1 lines: the other points split into the lines through it.
theorem ptA (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (h1 : ∀ l : Fin N, (L l).card = q + 1)
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) (p : Fin N) :
    ({l : Fin N | p ∈ L l} : Finset (Fin N)).card = q + 1 := by
  classical
  have hmaps : ∀ p' ∈ (Finset.univ.erase p : Finset (Fin N)),
      ln L h2 p p' ∈ ({l : Fin N | p ∈ L l} : Finset (Fin N)) := by
    intro p' hp'
    have hne : p ≠ p' := (Finset.ne_of_mem_erase hp').symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ln_spec L h2 hne).1
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ l ∈ ({l : Fin N | p ∈ L l} : Finset (Fin N)),
      ((Finset.univ.erase p).filter (fun p' => ln L h2 p p' = l)).card = q := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have he : (Finset.univ.erase p).filter (fun p' => ln L h2 p p' = l) = (L l).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hne, he⟩
        exact ⟨hne, by rw [← he]; exact (ln_spec L h2 (Ne.symm hne)).2⟩
      · rintro ⟨hne, hm⟩
        exact ⟨hne, ln_eq L h2 (Ne.symm hne) l hl hm⟩
    rw [he, Finset.card_erase_of_mem hl, h1 l]
    simp
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hsum
  have hN1 : N = (q + 1) * q + 1 := by rw [hN]; ring
  have hmul : ({l : Fin N | p ∈ L l} : Finset (Fin N)).card * q = (q + 1) * q := by
    rw [← hsum, hN1]
    simp
  exact Nat.eq_of_mul_eq_mul_right hq hmul

-- Two distinct lines meet in exactly one point.
theorem lnB (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (h1 : ∀ l : Fin N, (L l).card = q + 1)
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) (l l' : Fin N)
    (hne : l ≠ l') : ∃! x : Fin N, x ∈ L l ∧ x ∈ L l' := by
  classical
  have two : ∀ x y, x ∈ L l → x ∈ L l' → y ∈ L l → y ∈ L l' → x = y := by
    intro x y hx hx' hy hy'
    by_contra hxy
    exact hne ((h2 x y hxy).unique ⟨hx, hy⟩ ⟨hx', hy'⟩)
  have hp : ∃ p ∈ L l', p ∉ L l := by
    by_contra hcon
    have hall : ∀ p ∈ L l', p ∈ L l := by
      intro p hp
      by_contra hpn
      exact hcon ⟨p, hp, hpn⟩
    have hle : (L l').card ≤ 1 :=
      Finset.card_le_one.mpr (fun x hx y hy => two x y (hall x hx) hx (hall y hy) hy)
    rw [h1] at hle
    omega
  obtain ⟨p, hpl', hpl⟩ := hp
  have hxne : ∀ x ∈ L l, p ≠ x := fun x hx h => hpl (h ▸ hx)
  have hinj : Set.InjOn (ln L h2 p) (L l : Set (Fin N)) := by
    intro x hx y hy hxy
    by_contra hne'
    have sx := ln_spec L h2 (hxne x hx)
    have sy := ln_spec L h2 (hxne y hy)
    rw [← hxy] at sy
    have hm : ln L h2 p x = l := (h2 x y hne').unique ⟨sx.2, sy.2⟩ ⟨hx, hy⟩
    rw [hm] at sx
    exact hpl sx.1
  have himg : (L l).image (ln L h2 p) = ({m : Fin N | p ∈ L m} : Finset (Fin N)) := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (ln_spec L h2 (hxne x hx)).1
    · rw [ptA q N L hq hN h1 h2 p, Finset.card_image_of_injOn hinj, h1]
  have hl' : l' ∈ (L l).image (ln L h2 p) := by
    rw [himg]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpl'
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hl'
  have hxl' : x ∈ L l' := by
    rw [← hxe]
    exact (ln_spec L h2 (hxne x hx)).2
  exact ⟨x, ⟨hx, hxl'⟩, fun y hy => two y x hy.1 hy.2 hx hxl'⟩

-- k lines cover at most k q + 1 points.
theorem cover (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (h1 : ∀ l : Fin N, (L l).card = q + 1)
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) (X : Finset (Fin N)) :
    (X.biUnion L).card ≤ X.card * q + 1 := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | insert l' X hnot ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hnot]
    have hexp : (X.card + 1) * q = X.card * q + q := by ring
    rw [hexp]
    by_cases hX : X = ∅
    · subst hX
      simp [h1]
    · obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hX
      have hne : l ≠ l' := fun h => hnot (h ▸ hl)
      obtain ⟨x, ⟨hx, hx'⟩, _⟩ := lnB q N L hq hN h1 h2 l l' hne
      have hin : 1 ≤ (L l' ∩ X.biUnion L).card :=
        Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx', Finset.mem_biUnion.mpr ⟨l, hl, hx⟩⟩⟩
      have hu := Finset.card_union_add_card_inter (L l') (X.biUnion L)
      rw [h1] at hu
      omega

theorem mainC (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (h1 : ∀ l : Fin N, (L l).card = q + 1)
    (h2 : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) (X : Finset (Fin N))
    (hX : X.card ≤ q) :
    q ≤ ({p : Fin N | ∀ l ∈ X, p ∉ L l} : Finset (Fin N)).card := by
  classical
  have hcov := cover q N L hq hN h1 h2 X
  have hsub : (Finset.univ : Finset (Fin N)) ⊆
      ({p : Fin N | ∀ l ∈ X, p ∉ L l} : Finset (Fin N)) ∪ X.biUnion L := by
    intro p _
    rw [Finset.mem_union]
    by_cases h : ∃ l ∈ X, p ∈ L l
    · right
      obtain ⟨l, hl, hp⟩ := h
      exact Finset.mem_biUnion.mpr ⟨l, hl, hp⟩
    · left
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro l hl hp
      exact h ⟨l, hl, hp⟩
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h3
  have h4 := Finset.card_union_le ({p : Fin N | ∀ l ∈ X, p ∉ L l} : Finset (Fin N)) (X.biUnion L)
  have h5 : X.card * q ≤ q * q := Nat.mul_le_mul_right q hX
  have h6 : N = q * q + q + 1 := by rw [hN]; ring
  omega

end PEqualNP.Outside.L_meta_6692

theorem PEqualNP.Outside.L_meta_6692 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)),   (0 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x6 : Fin x2), (x3 x6).card = x1 + (1 : ℕ)) →         (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x7 ∈ x3 x10 ∧ x8 ∈ x3 x10) →           (∀ (x8 : Fin x2),               have x9 : Finset (Fin x2) := {x9 : Fin x2 | x8 ∈ x3 x9};               x9.card = x1 + (1 : ℕ)) ∧             (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x11 ∈ x3 x8 ∧ x11 ∈ x3 x9) ∧               ∀ (x8 : Finset (Fin x2)),                 x8.card ≤ x1 →                   have x10 : Finset (Fin x2) := {x10 : Fin x2 | ∀ x11 ∈ x8, x10 ∉ x3 x11};                   x1 ≤ x10.card := by
  intro q N L hq hN h1 h2
  exact ⟨fun p => PEqualNP.Outside.L_meta_6692.ptA q N L hq hN h1 h2 p,
    fun l l' hne => PEqualNP.Outside.L_meta_6692.lnB q N L hq hN h1 h2 l l' hne,
    fun X hX => PEqualNP.Outside.L_meta_6692.mainC q N L hq hN h1 h2 X hX⟩
