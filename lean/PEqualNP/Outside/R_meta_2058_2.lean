import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

-- Count disjoint classes in order of the shortest available witnesses:
-- one leaf of each side, three leaves, then four leaves.
theorem PEqualNP.Outside.R_meta_2058_2
    (shadow : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      IsReadK (N + N) C 2 → ∀ p l : Fin N, I p l →
      ∃ a b : ℕ, 0 < a ∧ a ≤ 2 ∧ 0 < b ∧ b ≤ 2 ∧
        [a, b] ∈ (readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [])
    (once : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, I p l → I p l' → I p' l → I p' l' → p = p' ∨ l = l') →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        [1, 1] ∈ (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []} ≤ 8 * C.size)
    (three : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, I p l → I p l' → I p' l → I p' l' → p = p' ∨ l = l') →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        let v := (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
        [1, 1] ∉ v ∧ ([1, 2] ∈ v ∨ [2, 1] ∈ v)} ≤ 40 * C.size)
    (four : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, I p l → I p l' → I p' l → I p' l' → p = p' ∨ l = l') →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        let v := (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
        [1, 1] ∉ v ∧ [1, 2] ∉ v ∧ [2, 1] ∉ v ∧ [2, 2] ∈ v} ≤ 64 * C.size) :
∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size := by
  intro q N I inst C _ _ degrees joins binary computes read
  have square_free : ∀ p p' l l' : Fin N,
      I p l → I p l' → I p' l → I p' l' → p = p' ∨ l = l' := by
    intro p p' l l' hpl hpl' hp'l hp'l'
    by_cases he : p = p'
    · exact Or.inl he
    · obtain ⟨j, _, unique⟩ := joins p p' he
      exact Or.inr ((unique l ⟨hpl, hp'l⟩).trans (unique l' ⟨hpl', hp'l'⟩).symm)
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2
  let V (e : Fin N × Fin N) :=
    (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []
  let E2 := E.filter fun e => [1, 1] ∈ V e
  let E3 := E.filter fun e => [1, 1] ∉ V e ∧ ([1, 2] ∈ V e ∨ [2, 1] ∈ V e)
  let E4 := E.filter fun e => [1, 1] ∉ V e ∧ [1, 2] ∉ V e ∧ [2, 1] ∉ V e ∧ [2, 2] ∈ V e
  have bound2 : E2.card ≤ 8 * C.size := by
    simpa only [Fintype.card_subtype, E2, E, V, Finset.filter_filter] using
      once N I C square_free binary computes
  have bound3 : E3.card ≤ 40 * C.size := by
    simpa only [Fintype.card_subtype, E3, E, V, Finset.filter_filter] using
      three N I C square_free binary computes
  have bound4 : E4.card ≤ 64 * C.size := by
    simpa only [Fintype.card_subtype, E4, E, V, Finset.filter_filter] using
      four N I C square_free binary computes
  have cover : E ⊆ (E2 ∪ E3) ∪ E4 := by
    intro e he
    have edge := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_union, E2, E3, E4, Finset.mem_filter, he, true_and]
    by_cases h11 : [1, 1] ∈ V e
    · exact Or.inl (Or.inl h11)
    by_cases h12 : [1, 2] ∈ V e
    · exact Or.inl (Or.inr ⟨h11, Or.inl h12⟩)
    by_cases h21 : [2, 1] ∈ V e
    · exact Or.inl (Or.inr ⟨h11, Or.inr h21⟩)
    obtain ⟨a, b, apos, abnd, bpos, bbnd, hv⟩ := shadow N I C binary computes read e.1 e.2 edge
    change [a, b] ∈ V e at hv
    have acases : a = 1 ∨ a = 2 := by omega
    have bcases : b = 1 ∨ b = 2 := by omega
    rcases acases with rfl | rfl <;> rcases bcases with rfl | rfl
    · exact (h11 hv).elim
    · exact (h12 hv).elim
    · exact (h21 hv).elim
    · exact Or.inr ⟨h11, h12, h21, hv⟩
  let col (l : Fin N) := (Finset.univ.filter fun p => I p l).image fun p => (p, l)
  have cols : E = (Finset.univ : Finset (Fin N)).biUnion col := by
    ext ⟨p, l⟩
    simp [E, col]
  have disjoint_cols : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) col := by
    intro l _ l' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', _, eq⟩ := Finset.mem_image.mp he'
    exact hne (congrArg Prod.snd eq).symm
  have card_col (l : Fin N) : (col l).card = q + 1 := by
    dsimp [col]
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h), degrees]
  have card_edges : E.card = N * (q + 1) := by
    rw [cols, Finset.card_biUnion disjoint_cols]
    simp [card_col]
  have hcover := Finset.card_le_card cover
  have h23 := Finset.card_union_le E2 E3
  have h234 := Finset.card_union_le (E2 ∪ E3) E4
  omega
