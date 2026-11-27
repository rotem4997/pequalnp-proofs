import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18860 : (∀ (x1 : Set (Set (Fin (26 : ℕ) → Bool))) (x2 : Finset (Set (Fin (26 : ℕ) → Bool))), (∀ x3 ∈ x2, x3 ∉ x1) → ∃ (x4 : List (Set (Fin (26 : ℕ) → Bool))), x4.Nodup ∧ x4.toFinset ⊆ x2 ∧ (∀ (x5 : ℕ) (x6 : Set (Fin (26 : ℕ) → Bool)), x4[x5]? = Option.some x6 → ∃ x8 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, ∃ x9 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, x6 = x8 ∩ x9 ∨ x6 = x8 ∪ x9) ∧ ∀ x5 ∈ x1 ∪ ↑x4.toFinset, ∀ x7 ∈ x1 ∪ ↑x4.toFinset, ∀ x9 ∈ x2, x9 = x5 ∩ x7 ∨ x9 = x5 ∪ x7 → x9 ∈ x1 ∪ ↑x4.toFinset) := by
  classical
  intro B S _
  let available (L : List (Set (Fin 26 → Bool))) := B ∪ (↑L.toFinset : Set (Set (Fin 26 → Bool)))
  let generated (T : Set (Set (Fin 26 → Bool))) (A : Set (Fin 26 → Bool)) :=
    ∃ U ∈ T, ∃ V ∈ T, A = U ∩ V ∨ A = U ∪ V
  let good (L : List (Set (Fin 26 → Bool))) := L.Nodup ∧ L.toFinset ⊆ S ∧
    ∀ i A, L[i]? = some A → generated (available (L.take i)) A
  let attainable (n : ℕ) := ∃ L : List (Set (Fin 26 → Bool)), good L ∧ L.length = n
  have zero : attainable 0 := by
    refine ⟨[], ⟨by simp, by simp, ?_⟩, rfl⟩
    simp
  let n := Nat.findGreatest attainable S.card
  obtain ⟨L, hL, hlen⟩ : attainable n := Nat.findGreatest_spec (m := 0) (by omega) zero
  obtain ⟨hn, hs, hg⟩ := hL
  refine ⟨L, hn, hs, hg, ?_⟩
  intro U hu V hv A ha make
  by_contra missing
  have fresh : A ∉ L := by
    intro h
    exact missing (Or.inr (List.mem_toFinset.mpr h))
  have nextNodup : (L ++ [A]).Nodup := by
    simp [List.nodup_append, hn]
    rintro a haL rfl
    exact fresh haL
  have nextSub : (L ++ [A]).toFinset ⊆ S := by
    intro T hT
    rcases List.mem_append.mp (List.mem_toFinset.mp hT) with h | h
    · exact hs (List.mem_toFinset.mpr h)
    · simpa only [List.mem_singleton.mp h] using ha
  have nextGood : good (L ++ [A]) := by
    refine ⟨nextNodup, nextSub, ?_⟩
    intro i T eq
    by_cases hi : i < L.length
    · rw [List.take_append_of_le_length hi.le]
      exact hg i T ((List.getElem?_append_left hi).symm.trans eq)
    · have bound := (List.getElem?_eq_some_iff.mp eq).1
      simp only [List.length_append, List.length_singleton] at bound
      have ix : i = L.length := by omega
      subst i
      have same : A = T := by simpa using eq
      subst T
      rw [List.take_append_length]
      exact ⟨U, hu, V, hv, make⟩
  have bound := Finset.card_le_card nextSub
  rw [List.toFinset_card_of_nodup nextNodup] at bound
  have possible : attainable (L ++ [A]).length := ⟨_, nextGood, rfl⟩
  have tooBig : (L ++ [A]).length ≤ n := Nat.le_findGreatest bound possible
  simp only [List.length_append, List.length_singleton] at tooBig
  omega
