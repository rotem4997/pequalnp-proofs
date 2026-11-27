import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7714

theorem core {α β : Type} [Finite α] (J : α → β → Prop) (q : ℕ) (S : Set α) (a b : α)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (meet : ∃ l, J a l ∧ J b l)
    (uniq : ∀ x y : α, x ≠ y → ∀ l l' : β, J x l → J y l → J x l' → J y l' → l = l')
    (card : ∀ l, {x | J x l}.ncard ≤ q + 1) :
    (∃ l, (∀ x ∈ S, J x l) ∧ S.ncard ≤ q + 1 ∧ ∀ m, m ≠ l → (S ∩ {x | J x m}).ncard ≤ 1) ∨
      ∃ c ∈ S, c ≠ a ∧ c ≠ b ∧ ∀ m, ¬(J a m ∧ J b m ∧ J c m) := by
  obtain ⟨l, hal, hbl⟩ := meet
  by_cases hall : ∀ x ∈ S, J x l
  · left
    refine ⟨l, hall, ?_, ?_⟩
    · exact (Set.ncard_le_ncard (fun x hx => hall x hx) (Set.toFinite _)).trans (card l)
    · intro m hm
      rw [Set.ncard_le_one (Set.toFinite _)]
      intro x hx y hy
      by_contra hxy
      exact hm (uniq x y hxy m l hx.2 hy.2 (hall x hx.1) (hall y hy.1))
  · right
    push Not at hall
    obtain ⟨c, hc, hcl⟩ := hall
    refine ⟨c, hc, ?_, ?_, ?_⟩
    · rintro rfl; exact hcl hal
    · rintro rfl; exact hcl hbl
    · rintro m ⟨ham, hbm, hcm⟩
      have := uniq a b hab m l ham hbm hal hbl
      subst this
      exact hcl hcm

theorem lines_through {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) : (Finset.univ.filter (fun l => I p0 l)).card = q + 1 := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
      ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card = 1 := by
    intro p hp
    have hne : p0 ≠ p := (Finset.ne_of_mem_erase hp).symm
    obtain ⟨l, hl, hu⟩ := huniq p0 p hne
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      exact hu x hx
    · intro hx
      rw [hx]
      exact hl
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card = q := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have e : ((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)
        = (Finset.univ.filter (fun p => I p l)).erase p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    have hmem : p0 ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
    rw [e, Finset.card_erase_of_mem hmem, hline l]
    rfl
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
        ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card
      = ∑ l ∈ Finset.univ.filter (fun l => I p0 l),
        (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h3
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p0),
    Finset.card_univ, Fintype.card_fin] at h3
  have e : N - 1 = (q + 1) * q := by
    have : (q + 1) * q = q ^ 2 + q := by ring
    omega
  rw [e] at h3
  exact (Nat.eq_of_mul_eq_mul_right hq h3).symm

theorem lines_meet {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (l m : Fin N) (hlm : l ≠ m) : ∃ p, I p l ∧ I p m := by
  by_contra hno
  push Not at hno
  have hmpos : 0 < (Finset.univ.filter (fun p => I p m)).card := by rw [hline m]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hmpos
  have hpm : I p m := (Finset.mem_filter.mp hp).2
  have hpl : ¬ I p l := fun h => hno p h hpm
  have hex : ∀ r : Fin N, ∃ f : Fin N, r ≠ p → I r f ∧ I p f := by
    intro r
    by_cases h : r = p
    · exact ⟨r, fun h' => absurd h h'⟩
    · obtain ⟨f, hf, _⟩ := huniq r p h
      exact ⟨f, fun _ => hf⟩
  choose f hf using hex
  set P := Finset.univ.filter (fun r => I r l) with hP
  have hrp : ∀ r ∈ P, r ≠ p := by
    intro r hr h
    subst h
    exact hpl (Finset.mem_filter.mp hr).2
  have hinj : Set.InjOn f P := by
    intro r hr r' hr' hfr
    by_contra hne
    have hr1 := (Finset.mem_filter.mp hr).2
    have hr2 := (Finset.mem_filter.mp hr').2
    have a1 := hf r (hrp r hr)
    have a2 := hf r' (hrp r' hr')
    obtain ⟨g, _, hgu⟩ := huniq r r' hne
    have e1 := hgu (f r) ⟨a1.1, hfr ▸ a2.1⟩
    have e2 := hgu l ⟨hr1, hr2⟩
    exact hpl (e2 ▸ e1 ▸ a1.2)
  have hsub : P.image f ⊆ (Finset.univ.filter (fun k => I p k)).erase m := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
    have a1 := hf r (hrp r hr)
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a1.2⟩⟩
    intro h
    exact hno r (Finset.mem_filter.mp hr).2 (h ▸ a1.1)
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, hP, hline l,
    Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpm⟩),
    lines_through q I hq hN hline huniq p] at c1
  omega

end PEqualNP.Outside.L_meta_7714


theorem PEqualNP.Outside.L_meta_7714 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (0 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 : Bool) (x10 : Set (Fin x2)) (x11 x12 : Fin x2),             have x13 : Fin x2 → Fin x2 → Prop := fun (x13 x14 : Fin x2) => bif x9 then x3 x13 x14 else x3 x14 x13;             x11 ∈ x10 → x12 ∈ x10 → x11 ≠ x12 → (∃ (x17 : Fin x2), (∀ x18 ∈ x10, x13 x18 x17) ∧ x10.ncard ≤ x1 + (1 : ℕ) ∧ ∀ (x18 : Fin x2), x18 ≠ x17 → (x10 ∩ {x20 : Fin x2 | x13 x20 x18}).ncard ≤ (1 : ℕ)) ∨ ∃ x17 ∈ x10, x17 ≠ x11 ∧ x17 ≠ x12 ∧ ∀ (x18 : Fin x2), ¬(x13 x11 x18 ∧ x13 x12 x18 ∧ x13 x17 x18) := by
  intro q N I _ hq hN hcard hu x9 S a b
  have hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    rw [← hcard l, Fintype.card_subtype]
  have hq1 : 1 ≤ q := hq
  have ncard_eq : ∀ (J : Fin N → Prop) [DecidablePred J],
      {x | J x}.ncard = (Finset.univ.filter J).card := by
    intro J _
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp
  intro x13 ha hb hab
  simp only [x13] at *
  cases x9
  · -- dual: elements of S are lines, the other side points
    exact PEqualNP.Outside.L_meta_7714.core (fun x l => I l x) q S a b ha hb hab
      (PEqualNP.Outside.L_meta_7714.lines_meet q I hq1 hN hl hu a b hab)
      (by
        intro x y hxy l l' hxl hyl hxl' hyl'
        by_contra hne
        obtain ⟨g, _, hgu⟩ := hu l l' hne
        exact hxy ((hgu x ⟨hxl, hxl'⟩).trans (hgu y ⟨hyl, hyl'⟩).symm))
      (by
        intro l
        rw [ncard_eq (fun x => I l x), PEqualNP.Outside.L_meta_7714.lines_through q I hq1 hN hl hu l])
  · exact PEqualNP.Outside.L_meta_7714.core (fun x l => I x l) q S a b ha hb hab
      (hu a b hab).exists
      (by
        intro x y hxy l l' hxl hyl hxl' hyl'
        exact (hu x y hxy).unique ⟨hxl, hyl⟩ ⟨hxl', hyl'⟩)
      (by
        intro l
        rw [ncard_eq (fun x => I x l), hl l])
