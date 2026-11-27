import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_11102 :
    ¬ (∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 5 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  classical
  rintro ⟨L, hlen, allZero, covers⟩
  let cell : Fin 6 → Fin 20 × Fin 20 := ![(19, 17), (17, 15), (16, 5), (14, 0), (9, 18), (1, 13)]
  let bit (i j : Fin 20) : Bool :=
    (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val
  have zero : ∀ k : Fin 6, bit (cell k).1 (cell k).2 = false := by decide +kernel
  -- One of the two cross entries is a one, so these zeros need different rectangles.
  have cross : ∀ i j : Fin 6, i ≠ j →
      bit (cell i).1 (cell j).2 = true ∨ bit (cell j).1 (cell i).2 = true := by
    decide +kernel
  have covered : ∀ k : Fin 6, ∃ r : Fin L.length,
      (cell k).1 ∈ (L.get r).1 ∧ (cell k).2 ∈ (L.get r).2 := by
    intro k
    obtain ⟨r, hr, hrow, hcol⟩ := covers (cell k).1 (cell k).2 (zero k)
    obtain ⟨idx, rfl⟩ := List.mem_iff_get.mp hr
    exact ⟨idx, hrow, hcol⟩
  choose pick hits using covered
  have injective : Function.Injective pick := by
    intro i j he
    by_contra different
    have both : (cell j).1 ∈ (L.get (pick i)).1 ∧
        (cell j).2 ∈ (L.get (pick i)).2 := by
      simpa only [he] using hits j
    have mem := List.get_mem L (pick i)
    have first : bit (cell i).1 (cell j).2 = false :=
      allZero _ mem _ (hits i).1 _ both.2
    have second : bit (cell j).1 (cell i).2 = false :=
      allZero _ mem _ both.1 _ (hits i).2
    rcases cross i j different with h | h
    · simp [first] at h
    · simp [second] at h
  have bound := Fintype.card_le_of_injective pick injective
  simp only [Fintype.card_fin] at bound
  omega
