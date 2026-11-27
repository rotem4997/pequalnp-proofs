import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18976_aux

private def badList : List ℕ :=
  [67100672, 25018369, 7962627, 24444933, 7405575, 6815755, 23330829, 5799955,
   22282261, 21757977, 19988517, 19415081, 6619269, 2179233]

private def lutR (d1 d2 : Fin 13) : ℕ :=
  match d1.val with
  | 0 => match d2.val with | 0 => 25018369 | 1 => 7962627 | 2 => 24444933 | 3 => 7962627 | 4 => 7962627 | 5 => 24444933 | 6 => 24444933 | 7 => 24444933 | 8 => 24444933 | 9 => 7962627 | 10 => 7962627 | 11 => 24444933 | _ => 7962627
  | 1 => match d2.val with | 0 => 7962627 | 1 => 7962627 | 2 => 7405575 | 3 => 6815755 | 4 => 5799955 | 5 => 23330829 | 6 => 19415081 | 7 => 22282261 | 8 => 19988517 | 9 => 6815755 | 10 => 21757977 | 11 => 23330829 | _ => 7405575
  | 2 => match d2.val with | 0 => 24444933 | 1 => 7405575 | 2 => 24444933 | 3 => 23330829 | 4 => 22282261 | 5 => 19988517 | 6 => 19988517 | 7 => 6619269 | 8 => 2179233 | 9 => 19415081 | 10 => 19415081 | 11 => 22282261 | _ => 6815755
  | 3 => match d2.val with | 0 => 7962627 | 1 => 6815755 | 2 => 23330829 | 3 => 7962627 | 4 => 21757977 | 5 => 19415081 | 6 => 7405575 | 7 => 23330829 | 8 => 22282261 | 9 => 6815755 | 10 => 7405575 | 11 => 19988517 | _ => 5799955
  | 4 => match d2.val with | 0 => 7962627 | 1 => 5799955 | 2 => 22282261 | 3 => 21757977 | 4 => 7962627 | 5 => 6815755 | 6 => 19415081 | 7 => 6815755 | 8 => 7405575 | 9 => 7405575 | 10 => 23330829 | 11 => 19988517 | _ => 23330829
  | 5 => match d2.val with | 0 => 24444933 | 1 => 23330829 | 2 => 19988517 | 3 => 19415081 | 4 => 6815755 | 5 => 24444933 | 6 => 19988517 | 7 => 2179233 | 8 => 22282261 | 9 => 7405575 | 10 => 22282261 | 11 => 6619269 | _ => 19415081
  | 6 => match d2.val with | 0 => 24444933 | 1 => 19415081 | 2 => 19988517 | 3 => 7405575 | 4 => 19415081 | 5 => 19988517 | 6 => 24444933 | 7 => 22282261 | 8 => 6619269 | 9 => 23330829 | 10 => 6815755 | 11 => 2179233 | _ => 22282261
  | 7 => match d2.val with | 0 => 24444933 | 1 => 22282261 | 2 => 6619269 | 3 => 23330829 | 4 => 6815755 | 5 => 2179233 | 6 => 22282261 | 7 => 24444933 | 8 => 19415081 | 9 => 19988517 | 10 => 7405575 | 11 => 19415081 | _ => 19988517
  | 8 => match d2.val with | 0 => 24444933 | 1 => 19988517 | 2 => 2179233 | 3 => 22282261 | 4 => 7405575 | 5 => 22282261 | 6 => 6619269 | 7 => 19415081 | 8 => 24444933 | 9 => 23330829 | 10 => 19988517 | 11 => 19415081 | _ => 6815755
  | 9 => match d2.val with | 0 => 7962627 | 1 => 6815755 | 2 => 19415081 | 3 => 6815755 | 4 => 7405575 | 5 => 7405575 | 6 => 23330829 | 7 => 19988517 | 8 => 23330829 | 9 => 7962627 | 10 => 5799955 | 11 => 22282261 | _ => 21757977
  | 10 => match d2.val with | 0 => 7962627 | 1 => 21757977 | 2 => 19415081 | 3 => 7405575 | 4 => 23330829 | 5 => 22282261 | 6 => 6815755 | 7 => 7405575 | 8 => 19988517 | 9 => 5799955 | 10 => 7962627 | 11 => 6815755 | _ => 23330829
  | 11 => match d2.val with | 0 => 24444933 | 1 => 23330829 | 2 => 22282261 | 3 => 19988517 | 4 => 19988517 | 5 => 6619269 | 6 => 2179233 | 7 => 19415081 | 8 => 19415081 | 9 => 22282261 | 10 => 6815755 | 11 => 24444933 | _ => 7405575
  | _ => match d2.val with | 0 => 7962627 | 1 => 7405575 | 2 => 6815755 | 3 => 5799955 | 4 => 23330829 | 5 => 19415081 | 6 => 22282261 | 7 => 19988517 | 8 => 6815755 | 9 => 21757977 | 10 => 23330829 | 11 => 7405575 | _ => 7962627

private def lutA (d1 d2 : Fin 13) : Fin 13 :=
  match d1.val with
  | 0 => match d2.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 9 | 4 => 3 | 5 => 3 | 6 => 9 | 7 => 9 | 8 => 3 | 9 => 3 | 10 => 9 | 11 => 1 | _ => 1
  | 1 => match d2.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 3 | 6 => 3 | 7 => 9 | 8 => 3 | 9 => 3 | 10 => 1 | 11 => 1 | _ => 1
  | 2 => match d2.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 9 | 7 => 1 | 8 => 1 | 9 => 9 | 10 => 1 | 11 => 1 | _ => 1
  | 3 => match d2.val with | 0 => 9 | 1 => 1 | 2 => 1 | 3 => 9 | 4 => 1 | 5 => 1 | 6 => 9 | 7 => 9 | 8 => 3 | 9 => 9 | 10 => 9 | 11 => 1 | _ => 1
  | 4 => match d2.val with | 0 => 3 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 3 | 5 => 3 | 6 => 9 | 7 => 9 | 8 => 3 | 9 => 3 | 10 => 9 | 11 => 9 | _ => 3
  | 5 => match d2.val with | 0 => 3 | 1 => 3 | 2 => 1 | 3 => 1 | 4 => 3 | 5 => 3 | 6 => 3 | 7 => 1 | 8 => 3 | 9 => 3 | 10 => 3 | 11 => 1 | _ => 3
  | 6 => match d2.val with | 0 => 9 | 1 => 3 | 2 => 9 | 3 => 9 | 4 => 9 | 5 => 3 | 6 => 9 | 7 => 9 | 8 => 1 | 9 => 9 | 10 => 9 | 11 => 1 | _ => 9
  | 7 => match d2.val with | 0 => 9 | 1 => 9 | 2 => 1 | 3 => 9 | 4 => 9 | 5 => 1 | 6 => 9 | 7 => 9 | 8 => 3 | 9 => 9 | 10 => 9 | 11 => 9 | _ => 3
  | 8 => match d2.val with | 0 => 3 | 1 => 3 | 2 => 1 | 3 => 3 | 4 => 3 | 5 => 3 | 6 => 1 | 7 => 3 | 8 => 3 | 9 => 3 | 10 => 1 | 11 => 1 | _ => 3
  | 9 => match d2.val with | 0 => 3 | 1 => 3 | 2 => 9 | 3 => 9 | 4 => 3 | 5 => 3 | 6 => 9 | 7 => 9 | 8 => 3 | 9 => 3 | 10 => 1 | 11 => 1 | _ => 1
  | 10 => match d2.val with | 0 => 9 | 1 => 1 | 2 => 1 | 3 => 9 | 4 => 9 | 5 => 3 | 6 => 9 | 7 => 9 | 8 => 1 | 9 => 1 | 10 => 9 | 11 => 1 | _ => 1
  | 11 => match d2.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 9 | 5 => 1 | 6 => 1 | 7 => 9 | 8 => 1 | 9 => 1 | 10 => 1 | 11 => 1 | _ => 1
  | _ => match d2.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 3 | 5 => 3 | 6 => 9 | 7 => 3 | 8 => 3 | 9 => 1 | 10 => 1 | 11 => 1 | _ => 1

private def lutB (d1 d2 : Fin 13) : Fin 13 :=
  match d1.val with
  | 0 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 2 | 8 => 2 | 9 => 0 | 10 => 1 | 11 => 2 | _ => 1
  | 1 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 4 | 8 => 2 | 9 => 0 | 10 => 3 | 11 => 2 | _ => 1
  | 2 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 5 | 9 => 0 | 10 => 3 | 11 => 2 | _ => 1
  | 3 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 2 | 8 => 4 | 9 => 0 | 10 => 1 | 11 => 2 | _ => 1
  | 4 => match d2.val with | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 1 | 6 => 3 | 7 => 3 | 8 => 2 | 9 => 1 | 10 => 3 | 11 => 5 | _ => 3
  | 5 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 2 | 9 => 0 | 10 => 0 | 11 => 2 | _ => 3
  | 6 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 3 | 5 => 0 | 6 => 0 | 7 => 2 | 8 => 7 | 9 => 0 | 10 => 1 | 11 => 7 | _ => 0
  | 7 => match d2.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 0 | 6 => 2 | 7 => 2 | 8 => 5 | 9 => 2 | 10 => 2 | 11 => 5 | _ => 5
  | 8 => match d2.val with | 0 => 2 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 2 | 5 => 2 | 6 => 7 | 7 => 5 | 8 => 2 | 9 => 2 | 10 => 5 | 11 => 5 | _ => 3
  | 9 => match d2.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 2 | 8 => 2 | 9 => 0 | 10 => 4 | 11 => 4 | _ => 4
  | 10 => match d2.val with | 0 => 1 | 1 => 3 | 2 => 3 | 3 => 1 | 4 => 3 | 5 => 0 | 6 => 1 | 7 => 2 | 8 => 5 | 9 => 4 | 10 => 1 | 11 => 3 | _ => 3
  | 11 => match d2.val with | 0 => 2 | 1 => 2 | 2 => 2 | 3 => 2 | 4 => 5 | 5 => 2 | 6 => 7 | 7 => 5 | 8 => 5 | 9 => 4 | 10 => 3 | 11 => 2 | _ => 2
  | _ => match d2.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 3 | 5 => 3 | 6 => 0 | 7 => 5 | 8 => 3 | 9 => 4 | 10 => 3 | 11 => 2 | _ => 1

private lemma orbit_empty :
    ∀ i : Fin 13, false = (67100672 : ℕ).testBit ((1 : Fin 13) * i + (0 : Fin 13)).val := by
  decide

private lemma orbit_r_mem : ∀ d1 d2 : Fin 13, lutR d1 d2 ∈ badList := by decide
private lemma orbit_a_mem : ∀ d1 d2 : Fin 13, lutA d1 d2 ∈ ([1, 3, 9] : List (Fin 13)) := by decide

private lemma orbit_bits :
    ∀ d1 d2 j : Fin 13,
      decide (j = 0 ∨ j = d1 ∨ j = d2) =
        (lutR d1 d2).testBit ((lutA d1 d2) * j + (lutB d1 d2)).val := by
  decide

private lemma card_le_three_triple {α : Type*} [DecidableEq α] (S : Finset α)
    (hne : S.Nonempty) (hcard : S.card ≤ 3) :
    ∃ x y z : α, S = {x, y, z} := by
  rcases hne with ⟨x, hx⟩
  by_cases h1 : (S.erase x).Nonempty
  · rcases h1 with ⟨y, hy'⟩
    have hy : y ∈ S := Finset.mem_of_mem_erase hy'
    by_cases h2 : ((S.erase x).erase y).Nonempty
    · rcases h2 with ⟨z, hz''⟩
      have hz' : z ∈ S.erase x := Finset.mem_of_mem_erase hz''
      have hz : z ∈ S := Finset.mem_of_mem_erase hz'
      refine ⟨x, y, z, ?_⟩
      have hsub : ({x, y, z} : Finset α) ⊆ S := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have hcard0 : (((S.erase x).erase y).erase z).card = 0 := by
        rw [Finset.card_erase_of_mem hz'', Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx]
        omega
      have hempty : ((S.erase x).erase y).erase z = ∅ := Finset.card_eq_zero.mp hcard0
      ext w
      constructor
      · intro hw
        by_contra hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hw3 : w ∈ ((S.erase x).erase y).erase z :=
          Finset.mem_erase.mpr ⟨hnot.2.2, Finset.mem_erase.mpr ⟨hnot.2.1, Finset.mem_erase.mpr ⟨hnot.1, hw⟩⟩⟩
        rw [hempty] at hw3
        exact Finset.notMem_empty w hw3
      · exact fun hw => hsub hw
    · rw [Finset.not_nonempty_iff_eq_empty] at h2
      refine ⟨x, y, y, ?_⟩
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hw
        by_contra hnot
        push Not at hnot
        have hw2 : w ∈ (S.erase x).erase y :=
          Finset.mem_erase.mpr ⟨hnot.2.1, Finset.mem_erase.mpr ⟨hnot.1, hw⟩⟩
        rw [h2] at hw2
        exact Finset.notMem_empty w hw2
      · rintro (rfl | rfl | rfl) <;> assumption
  · rw [Finset.not_nonempty_iff_eq_empty] at h1
    refine ⟨x, x, x, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      by_contra hnot
      push Not at hnot
      have hw1 : w ∈ S.erase x := Finset.mem_erase.mpr ⟨hnot.1, hw⟩
      rw [h1] at hw1
      exact Finset.notMem_empty w hw1
    · rintro (rfl | rfl | rfl) <;> exact hx

theorem orbits_main :
    ∀ S : Finset (Fin 13), S.card ≤ 3 →
      ∃ r ∈ ([67100672, 25018369, 7962627, 24444933, 7405575, 6815755, 23330829, 5799955,
              22282261, 21757977, 19988517, 19415081, 6619269, 2179233] : List ℕ),
      ∃ a ∈ ([1, 3, 9] : List (Fin 13)), ∃ b : Fin 13,
        ∀ i : Fin 13, decide (i ∈ S) = r.testBit (a * i + b).val := by
  intro S hcard
  by_cases hempty : S = ∅
  · subst hempty
    refine ⟨67100672, by decide, 1, by decide, 0, ?_⟩
    intro i
    simpa using orbit_empty i
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨x, y, z, rfl⟩ := card_le_three_triple S hne hcard
    let d1 : Fin 13 := y - x
    let d2 : Fin 13 := z - x
    refine ⟨lutR d1 d2, orbit_r_mem d1 d2, lutA d1 d2, orbit_a_mem d1 d2, lutB d1 d2 - lutA d1 d2 * x, ?_⟩
    intro i
    have hidx : lutA d1 d2 * i + (lutB d1 d2 - lutA d1 d2 * x) =
        lutA d1 d2 * (i - x) + lutB d1 d2 := by
      rw [mul_sub, add_sub_assoc', sub_add_eq_add_sub, add_comm (lutA d1 d2 * i) (lutB d1 d2), add_sub_assoc]
    rw [hidx, ← orbit_bits d1 d2 (i - x)]
    apply Bool.eq_iff_iff.mpr
    simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq, sub_eq_zero]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_left_inj.mp h))
      · exact Or.inr (Or.inr (sub_left_inj.mp h))

end PEqualNP.Outside.L_meta_18976_aux

theorem PEqualNP.Outside.L_meta_18976 : ∀ (x1 : Finset (Fin (13 : ℕ))), x1.card ≤ (3 : ℕ) → ∃ x3 ∈ [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)], ∃ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), Decidable.decide (x6 ∈ x1) = x3.testBit ↑(x4 * x6 + x5) := by
  exact PEqualNP.Outside.L_meta_18976_aux.orbits_main
