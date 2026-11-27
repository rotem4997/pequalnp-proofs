import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_8746_1
    (hTests : ∃ (n : ℕ) (B : Fin n → Finset (Fin n)) (C : Circuit),
      (∀ i, i ∈ B i) ∧
      (∀ i j, i ≠ j → (B i ∩ B j).card ≤ 1) ∧ IsAO2 (n + n) C ∧
      C.size + 1 < (incidences B).card + n ∧
      (∀ l, ∀ p ∈ B l, C.eval (incidenceInput {p} {l}) = true) ∧
      (∀ X : Finset (Fin n), C.eval (incidenceInput X
        (Finset.univ.filter (fun l => Disjoint X (B l)))) = false))
    (hMono : ∀ (n : ℕ) (C : Circuit), IsAO2 (n + n) C →
      ∀ (X Y X' Y' : Finset (Fin n)), X ⊆ X' → Y ⊆ Y' →
      C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true) :
    ∃ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      let x3 : Fin x1 → Finset (Fin x1) := fun x3 =>
        {x4 : Fin x1 | x2.eval (PEqualNP.GenericRejection.incidenceInput {x4} {x3}) = Bool.true}
      (∀ (x4 : Fin x1), x4 ∈ x3 x4) ∧
      (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x3 x4 ∩ x3 x5).card ≤ (1 : ℕ)) ∧
      PEqualNP.TopForm.IsAO2 (x1 + x1) x2 ∧
      (∀ (x4 x5 : Finset (Fin x1)),
        x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true →
        (∀ x7 ∈ x4, x2.eval (PEqualNP.GenericRejection.incidenceInput (x4.erase x7) x5) = Bool.false) →
        (∀ x8 ∈ x5, x2.eval (PEqualNP.GenericRejection.incidenceInput x4 (x5.erase x8)) = Bool.false) →
        x4.card = (1 : ℕ) ∧ x5.card = (1 : ℕ)) ∧
      x2.size + (1 : ℕ) < (PEqualNP.HeptadCover.incidences x3).card + x1 := by
  classical
  have cardOne {n : ℕ} {X : Finset (Fin n)} {p : Fin n}
      (hp : p ∈ X) (hUnique : ∀ q ∈ X, q ≠ p → False) : X.card = 1 := by
    have he : X = {p} := by
      ext q
      simp only [Finset.mem_singleton]
      constructor
      · intro hq
        by_contra hne
        exact hUnique q hq hne
      · rintro rfl
        exact hp
    simp [he]
  obtain ⟨n, B, C, diag, hLinear, ao, budget, pos, neg⟩ := hTests
  have exactness (X Y : Finset (Fin n)) :
      C.eval (incidenceInput X Y) = true ↔ ∃ p ∈ X, ∃ l ∈ Y, p ∈ B l := by
    constructor
    · intro h
      by_contra hn
      have sub : Y ⊆ Finset.univ.filter (fun l => Disjoint X (B l)) := by
        intro l hl
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mpr ?_⟩
        intro p hp he
        exact hn ⟨p, hp, l, hl, he⟩
      have bad := hMono n C ao X Y X _ (by intro p hp; exact hp) sub h
      rw [neg X] at bad
      cases bad
    · rintro ⟨p, hp, l, hl, he⟩
      exact hMono n C ao {p} {l} X Y (Finset.singleton_subset_iff.mpr hp)
        (Finset.singleton_subset_iff.mpr hl) (pos l p he)
  let E : Fin n → Finset (Fin n) := fun l =>
    {p : Fin n | C.eval (incidenceInput {p} {l}) = true}
  have hE : E = B := by
    funext l
    ext p
    change p ∈ Finset.univ.filter (fun q => C.eval (incidenceInput {q} {l}) = true) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [exactness]
    simp
  have d : ∀ l, l ∈ E l := by rw [hE]; exact diag
  have lin : ∀ i j, i ≠ j → (E i ∩ E j).card ≤ 1 := by rw [hE]; exact hLinear
  have sz : C.size + 1 < (incidences E).card + n := by rw [hE]; exact budget
  refine ⟨n, C, d, lin, ao, ?_, sz⟩
  intro X Y h hX hY
  obtain ⟨p, hp, l, hl, he⟩ := (exactness X Y).mp h
  constructor
  · apply cardOne hp
    intro q hq hne
    have bad := (exactness (X.erase q) Y).mpr
      ⟨p, Finset.mem_erase.mpr ⟨Ne.symm hne, hp⟩, l, hl, he⟩
    rw [hX q hq] at bad
    cases bad
  · apply cardOne hl
    intro q hq hne
    have bad := (exactness X (Y.erase q)).mpr
      ⟨p, hp, l, Finset.mem_erase.mpr ⟨Ne.symm hne, hl⟩, he⟩
    rw [hY q hq] at bad
    cases bad
