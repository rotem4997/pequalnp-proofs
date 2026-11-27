import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19020

private def Dlist : List (Fin 13) := [0, 1, 3, 9]
private def Dset : Finset (Fin 13) := {(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)}
private def xs : List ℕ :=
  [7405575, 23330829, 5799955, 22282261, 21757977, 19988517, 19415081, 6619269]

private def witTable : Array (ℕ × Fin 13 × Fin 13) :=
  #[(7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (5799955, 1, 0), (23330829, 3, 0), (19415081, 3, 0), (22282261, 9, 4), (19988517, 3, 2), (7405575, 1, 0), (21757977, 1, 3), (23330829, 1, 2), (7405575, 1, 1), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (23330829, 1, 0), (22282261, 1, 0), (19988517, 1, 0), (19988517, 9, 0), (6619269, 1, 0), (7405575, 1, 0), (19415081, 9, 0), (19415081, 1, 3), (22282261, 1, 2), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (23330829, 1, 0), (7405575, 1, 0), (21757977, 1, 0), (19415081, 1, 0), (7405575, 9, 0), (23330829, 9, 2), (22282261, 3, 4), (7405575, 1, 0), (7405575, 9, 1), (19988517, 1, 2), (5799955, 1, 1), (7405575, 1, 0), (5799955, 1, 0), (22282261, 1, 0), (21757977, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (19415081, 9, 3), (7405575, 1, 0), (7405575, 3, 2), (7405575, 3, 1), (23330829, 9, 3), (19988517, 9, 5), (23330829, 3, 3), (7405575, 1, 0), (23330829, 3, 0), (19988517, 1, 0), (19415081, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (19988517, 3, 0), (7405575, 1, 0), (22282261, 3, 2), (7405575, 3, 0), (22282261, 3, 0), (6619269, 1, 2), (19415081, 3, 3), (7405575, 1, 0), (19415081, 3, 0), (19988517, 9, 0), (7405575, 9, 0), (19415081, 9, 3), (19988517, 3, 0), (7405575, 1, 0), (22282261, 9, 2), (6619269, 1, 7), (23330829, 9, 0), (7405575, 1, 0), (7405575, 1, 0), (22282261, 9, 0), (7405575, 1, 0), (22282261, 9, 4), (6619269, 1, 0), (23330829, 9, 2), (7405575, 1, 0), (7405575, 1, 0), (22282261, 9, 2), (7405575, 1, 0), (19415081, 3, 5), (19988517, 9, 2), (7405575, 9, 2), (19415081, 9, 5), (19988517, 3, 5), (7405575, 1, 0), (19988517, 3, 2), (7405575, 1, 0), (22282261, 3, 4), (7405575, 3, 2), (22282261, 3, 2), (6619269, 1, 7), (19415081, 3, 5), (7405575, 1, 0), (23330829, 3, 2), (19988517, 1, 5), (19415081, 1, 5), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 0), (19415081, 9, 0), (7405575, 1, 0), (7405575, 3, 1), (7405575, 3, 0), (23330829, 9, 0), (19988517, 9, 2), (23330829, 3, 2), (7405575, 1, 0), (5799955, 1, 4), (22282261, 1, 4), (21757977, 1, 4), (7405575, 1, 0), (21757977, 1, 3), (19415081, 1, 3), (7405575, 9, 1), (23330829, 9, 3), (22282261, 3, 0), (7405575, 1, 0), (7405575, 9, 2), (19988517, 1, 5), (5799955, 1, 4), (7405575, 1, 0), (7405575, 1, 0), (23330829, 1, 3), (7405575, 1, 0), (23330829, 1, 2), (22282261, 1, 2), (19988517, 1, 2), (19988517, 9, 5), (6619269, 1, 2), (7405575, 1, 0), (19415081, 9, 5), (19415081, 1, 5), (22282261, 1, 4), (7405575, 1, 0), (7405575, 1, 0), (7405575, 1, 2), (7405575, 1, 0), (7405575, 1, 1), (7405575, 1, 0), (5799955, 1, 1), (23330829, 3, 3), (19415081, 3, 3), (22282261, 9, 0), (19988517, 3, 5), (7405575, 1, 0), (21757977, 1, 4), (23330829, 1, 3), (7405575, 1, 2), (7405575, 1, 0)]

private def inD (z : Fin 13) : Bool :=
  z == 0 || z == 1 || z == 3 || z == 9

private lemma inD_iff (z : Fin 13) : inD z = true ↔ z ∈ Dset := by
  revert z
  decide

private lemma wit_mem :
    ∀ d1 d2 : Fin 13,
      let t := witTable.getD (13 * d1.val + d2.val) (7405575, 1, 0)
      t.1 ∈ xs ∧ t.2.1 ∈ [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)] := by
  decide +kernel

private def nonCollinear3 (d1 d2 : Fin 13) : Bool :=
  d1 != 0 && d2 != 0 && d1 != d2 &&
  (List.finRange 13).all fun l => !(inD (0 - l) && inD (d1 - l) && inD (d2 - l))

private lemma wit_ok :
    ∀ d1 d2 : Fin 13, nonCollinear3 d1 d2 = true →
      let t := witTable.getD (13 * d1.val + d2.val) (7405575, 1, 0)
      t.1.testBit ↑(t.2.1 * 0 + t.2.2) = true ∧
      t.1.testBit ↑(t.2.1 * d1 + t.2.2) = true ∧
      t.1.testBit ↑(t.2.1 * d2 + t.2.2) = true ∧
      ∀ l : Fin 13, !inD (0 - l) → !inD (d1 - l) → !inD (d2 - l) →
        t.1.testBit (13 + ↑(t.2.1 * l + t.2.2)) = true := by
  decide +kernel

private lemma triple_cover (a b c : Fin 13) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnc : ∀ l : Fin 13, ¬(a - l ∈ Dset ∧ b - l ∈ Dset ∧ c - l ∈ Dset)) :
    ∃ x7 ∈ xs, ∃ x9 ∈ [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)], ∃ x10 : Fin 13,
      (∀ p ∈ ({a, b, c} : Finset (Fin 13)), x7.testBit ↑(x9 * p + x10) = true) ∧
      (∀ l : Fin 13, (∀ p ∈ ({a, b, c} : Finset (Fin 13)), p - l ∉ Dset) →
        x7.testBit (13 + ↑(x9 * l + x10)) = true) := by
  set d1 := b - a
  set d2 := c - a
  have hnc3 : nonCollinear3 d1 d2 = true := by
    simp only [nonCollinear3, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
      List.mem_finRange, true_implies, Bool.not_eq_true', Bool.and_eq_false_iff]
    refine ⟨⟨⟨sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hac.symm⟩, ?_⟩, ?_⟩
    · intro h; apply hbc; have := congrArg (· + a) h; simpa [d1, d2] using this
    · intro l
      by_contra h
      simp only [not_or, Bool.not_eq_false] at h
      obtain ⟨⟨h0, h1⟩, h2⟩ := h
      rw [inD_iff] at h0 h1 h2
      apply hnc (l + a)
      refine ⟨?_, ?_, ?_⟩
      · simpa [sub_add_eq_sub_sub] using h0
      · have : b - (l + a) = d1 - l := by dsimp only [d1]; abel
        rw [this]; exact h1
      · have : c - (l + a) = d2 - l := by dsimp only [d2]; abel
        rw [this]; exact h2
  have hmem := wit_mem d1 d2
  have hok := wit_ok d1 d2 hnc3
  refine ⟨(witTable.getD (13 * d1.val + d2.val) (7405575, 1, 0)).1, hmem.1,
          (witTable.getD (13 * d1.val + d2.val) (7405575, 1, 0)).2.1, hmem.2,
          (witTable.getD (13 * d1.val + d2.val) (7405575, 1, 0)).2.2 -
            (witTable.getD (13 * d1.val + d2.val) (7405575, 1, 0)).2.1 * a, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp
    · rw [hp]
      have : ∀ u v : Fin 13, u * a + (v - u * a) = u * 0 + v := fun u v => by rw [mul_zero, zero_add]; abel
      rw [this]; exact hok.1
    · rw [hp]
      have : ∀ u v : Fin 13, u * b + (v - u * a) = u * d1 + v := fun u v => by dsimp only [d1]; rw [mul_sub]; abel
      rw [this]; exact hok.2.1
    · rw [hp]
      have : ∀ u v : Fin 13, u * c + (v - u * a) = u * d2 + v := fun u v => by dsimp only [d2]; rw [mul_sub]; abel
      rw [this]; exact hok.2.2.1
  · intro l hl
    have : ∀ u v : Fin 13, u * l + (v - u * a) = u * (l - a) + v := fun u v => by rw [mul_sub]; abel
    rw [this]
    apply hok.2.2.2 (l - a)
    · simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, inD_iff]
      intro h; apply hl a (by simp)
      have heq : a - l = 0 - (l - a) := by abel
      rw [heq]; exact h
    · simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, inD_iff]
      intro h; apply hl b (by simp)
      have heq : b - l = d1 - (l - a) := by dsimp only [d1]; abel
      rw [heq]; exact h
    · simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, inD_iff]
      intro h; apply hl c (by simp)
      have heq : c - l = d2 - (l - a) := by dsimp only [d2]; abel
      rw [heq]; exact h

private def isArc4 (d1 d2 d3 : Fin 13) : Bool :=
  d1 != 0 && d2 != 0 && d3 != 0 && d1 != d2 && d1 != d3 && d2 != d3 &&
  (List.finRange 13).all fun l =>
    (if inD (0 - l) then 1 else 0) + (if inD (d1 - l) then 1 else 0) +
    (if inD (d2 - l) then 1 else 0) + (if inD (d3 - l) then 1 else 0) ≤ 2

private def avoids4 (d1 d2 d3 l : Fin 13) : Bool :=
  !inD (0 - l) && !inD (d1 - l) && !inD (d2 - l) && !inD (d3 - l)

private lemma arc4_avoids_prop :
    ∀ d1 d2 d3 : Fin 13, isArc4 d1 d2 d3 = true →
      let av := (List.finRange 13).filter (avoids4 d1 d2 d3)
      av.length = 3 ∧
      (∀ p : Fin 13,
        (if inD (p - av.getD 0 0) then 1 else 0) +
        (if inD (p - av.getD 1 0) then 1 else 0) +
        (if inD (p - av.getD 2 0) then 1 else 0) ≤ 2) := by
  decide +kernel

private lemma arc4_no_fifth :
    ∀ d1 d2 d3 : Fin 13, isArc4 d1 d2 d3 = true →
      ∀ q : Fin 13, q ≠ 0 → q ≠ d1 → q ≠ d2 → q ≠ d3 →
        ∃ l : Fin 13,
          (if inD (0 - l) then 1 else 0) + (if inD (d1 - l) then 1 else 0) +
          (if inD (d2 - l) then 1 else 0) + (if inD (d3 - l) then 1 else 0) +
          (if inD (q - l) then 1 else 0) ≥ 3 := by
  decide +kernel

private lemma line_through_two (a b : Fin 13) (hab : a ≠ b) :
    ∃ l : Fin 13, a - l ∈ Dset ∧ b - l ∈ Dset ∧
      ∀ l' : Fin 13, a - l' ∈ Dset → b - l' ∈ Dset → l' = l := by
  revert a b hab
  decide +kernel

private lemma line_pts_card (l : Fin 13) :
    (Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset).card = 4 := by
  revert l
  decide +kernel

private lemma dual_step (x2 x3 : Finset (Fin 13))
    (h : ∃ x7 ∈ xs, ∃ x9 ∈ [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)], ∃ x10 : Fin 13,
      (∀ p ∈ x3.image (fun z => -z), x7.testBit ↑(x9 * p + x10) = true) ∧
      (∀ l ∈ x2.image (fun z => -z), x7.testBit (13 + ↑(x9 * l + x10)) = true)) :
    ∃ (x7 : ℕ) (x8 : Bool), x7 ∈ xs ∧ ∃ x9 ∈ [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)], ∃ x10 : Fin 13,
      (∀ x11 ∈ x2, x7.testBit (if x8 = true then 13 + ↑(-(x9 * x11 + x10)) else ↑(x9 * x11 + x10)) = true) ∧
      (∀ x11 ∈ x3, x7.testBit (if x8 = true then ↑(-(x9 * x11 + x10)) else 13 + ↑(x9 * x11 + x10)) = true) := by
  obtain ⟨x7, hx7, x9, hx9, x10, h3, h2⟩ := h
  refine ⟨x7, true, hx7, x9, hx9, -x10, ?_, ?_⟩
  · intro p hp
    simp only [↓reduceIte]
    have heq : -(x9 * p + -x10) = x9 * (-p) + x10 := by rw [mul_neg]; abel
    rw [heq]
    exact h2 (-p) (Finset.mem_image_of_mem _ hp)
  · intro l hl
    simp only [↓reduceIte]
    have heq : -(x9 * l + -x10) = x9 * (-l) + x10 := by rw [mul_neg]; abel
    rw [heq]
    exact h3 (-l) (Finset.mem_image_of_mem _ hl)

private lemma arc_le_two_extend (x2 x3 : Finset (Fin 13))
    (hdisj : ∀ p ∈ x2, ∀ l ∈ x3, p - l ∉ Dset)
    (h2c : x2.card ≤ 2) (h3c : x3.card ≤ 2) :
    ∃ a b c : Fin 13, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      x2 ⊆ {a, b, c} ∧
      (∀ l : Fin 13, ¬(a - l ∈ Dset ∧ b - l ∈ Dset ∧ c - l ∈ Dset)) ∧
      (∀ p ∈ ({a, b, c} : Finset (Fin 13)), ∀ l ∈ x3, p - l ∉ Dset) := by
  have hstep1 : ∀ s : Finset (Fin 13), s.card ≤ 1 → (∀ p ∈ s, ∀ l ∈ x3, p - l ∉ Dset) →
      ∃ p : Fin 13, p ∉ s ∧ ∀ l ∈ x3, p - l ∉ Dset := by
    intro s hsc _
    let bad := s ∪ x3.biUnion (fun l => Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset)
    have hbad : bad.card < (Finset.univ : Finset (Fin 13)).card := by
      have h1 : bad.card ≤ s.card + (x3.biUnion (fun l => Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset)).card :=
        Finset.card_union_le _ _
      have h2 : (x3.biUnion (fun l => Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset)).card ≤
          ∑ l ∈ x3, (Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset).card := Finset.card_biUnion_le
      have h3 : ∑ l ∈ x3, (Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset).card = x3.card * 4 := by
        simp [line_pts_card]
      have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by simp
      omega
    obtain ⟨p, _, hpbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
    simp only [bad, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or, not_exists, not_and] at hpbad
    exact ⟨p, hpbad.1, hpbad.2⟩
  have hstep2 : ∀ a b : Fin 13, a ≠ b → (∀ l ∈ x3, a - l ∉ Dset) → (∀ l ∈ x3, b - l ∉ Dset) →
      ∃ c : Fin 13, c ≠ a ∧ c ≠ b ∧
        (∀ l : Fin 13, ¬(a - l ∈ Dset ∧ b - l ∈ Dset ∧ c - l ∈ Dset)) ∧
        (∀ l ∈ x3, c - l ∉ Dset) := by
    intro a b hab _ _
    obtain ⟨lab, hlab_a, hlab_b, hlab_uniq⟩ := line_through_two a b hab
    let bad := (Finset.univ.filter fun p : Fin 13 => p - lab ∈ Dset) ∪
               x3.biUnion (fun l => Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset)
    have hbad : bad.card < (Finset.univ : Finset (Fin 13)).card := by
      have h1 : bad.card ≤ (Finset.univ.filter fun p : Fin 13 => p - lab ∈ Dset).card +
          (x3.biUnion (fun l => Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset)).card :=
        Finset.card_union_le _ _
      have h2 : (x3.biUnion (fun l => Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset)).card ≤
          ∑ l ∈ x3, (Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset).card := Finset.card_biUnion_le
      have h3 : ∑ l ∈ x3, (Finset.univ.filter fun p : Fin 13 => p - l ∈ Dset).card = x3.card * 4 := by
        simp [line_pts_card]
      have h4 : (Finset.univ.filter fun p : Fin 13 => p - lab ∈ Dset).card = 4 := line_pts_card lab
      have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by simp
      omega
    obtain ⟨c, _, hcbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
    simp only [bad, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or, not_exists, not_and] at hcbad
    refine ⟨c, ?_, ?_, ?_, hcbad.2⟩
    · rintro rfl; exact hcbad.1 hlab_a
    · rintro rfl; exact hcbad.1 hlab_b
    · rintro l ⟨hla, hlb, hlc⟩
      have hl_eq := hlab_uniq l hla hlb
      subst hl_eq
      exact hcbad.1 hlc
  by_cases hc0 : x2.card = 0
  · have hxe : x2 = ∅ := Finset.card_eq_zero.mp hc0
    subst hxe
    obtain ⟨a, _, ha3⟩ := hstep1 ∅ (by simp) (by simp)
    obtain ⟨b, hba, hb3⟩ := hstep1 {a} (by simp) (fun p hp => by simp at hp; subst hp; exact ha3)
    have hab : a ≠ b := fun h => hba (by simp [h])
    obtain ⟨c, hca, hcb, hnc, hc3⟩ := hstep2 a b hab ha3 hb3
    refine ⟨a, b, c, hab, hca.symm, hcb.symm, Finset.empty_subset _, hnc, ?_⟩
    intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> assumption
  · by_cases hc1 : x2.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
      have ha3 : ∀ l ∈ x3, a - l ∉ Dset := hdisj a (by simp)
      obtain ⟨b, hba, hb3⟩ := hstep1 {a} (by simp) hdisj
      have hab : a ≠ b := fun h => hba (by simp [h])
      obtain ⟨c, hca, hcb, hnc, hc3⟩ := hstep2 a b hab ha3 hb3
      refine ⟨a, b, c, hab, hca.symm, hcb.symm, ?_, hnc, ?_⟩
      · intro p hp; simp at hp ⊢; exact Or.inl hp
      · intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> assumption
    · have hc2 : x2.card = 2 := by omega
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
      have ha3 : ∀ l ∈ x3, a - l ∉ Dset := hdisj a (by simp)
      have hb3 : ∀ l ∈ x3, b - l ∉ Dset := hdisj b (by simp)
      obtain ⟨c, hca, hcb, hnc, hc3⟩ := hstep2 a b hab ha3 hb3
      refine ⟨a, b, c, hab, hca.symm, hcb.symm, ?_, hnc, ?_⟩
      · intro p hp; simp at hp ⊢; rcases hp with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
      · intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> assumption

private lemma card_filter_insert_of_notMem {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (x : α) (s : Finset α) (hx : x ∉ s) :
    ((insert x s).filter P).card = (if P x then 1 else 0) + (s.filter P).card := by
  rw [Finset.filter_insert]
  split_ifs with hp
  · rw [Finset.card_insert_of_notMem (fun h => hx (Finset.mem_filter.mp h).1)]
    omega
  · omega

private lemma card_filter_singleton {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P] (x : α) :
    (({x} : Finset α).filter P).card = if P x then 1 else 0 := by
  rw [Finset.filter_singleton]
  split_ifs <;> simp

private lemma card_ge_three_solve (x2 x3 : Finset (Fin 13))
    (hdisj : ∀ p ∈ x2, ∀ l ∈ x3, p - l ∉ Dset)
    (harc2 : ∀ l : Fin 13, (x2.filter fun p => p - l ∈ Dset).card ≤ 2)
    (h3ge : 3 ≤ x2.card) :
    ∃ (x7 : ℕ) (x8 : Bool), x7 ∈ xs ∧ ∃ x9 ∈ [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)], ∃ x10 : Fin 13,
      (∀ x11 ∈ x2, x7.testBit (if x8 = true then 13 + ↑(-(x9 * x11 + x10)) else ↑(x9 * x11 + x10)) = true) ∧
      (∀ x11 ∈ x3, x7.testBit (if x8 = true then ↑(-(x9 * x11 + x10)) else 13 + ↑(x9 * x11 + x10)) = true) := by
  by_cases hc3 : x2.card = 3
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc3
    have hnc : ∀ l : Fin 13, ¬(a - l ∈ Dset ∧ b - l ∈ Dset ∧ c - l ∈ Dset) := by
      rintro l ⟨ha, hb, hc⟩
      have hsub : ({a, b, c} : Finset (Fin 13)) ⊆ ({a, b, c} : Finset (Fin 13)).filter fun p => p - l ∈ Dset := by
        intro p hp; simp only [Finset.mem_filter]; refine ⟨hp, ?_⟩
        simp at hp; rcases hp with rfl | rfl | rfl <;> assumption
      have hle := (Finset.card_le_card hsub).trans (harc2 l)
      have hcard3 : ({a, b, c} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      omega
    obtain ⟨x7, hx7, x9, hx9, x10, hp, hl⟩ := triple_cover a b c hab hac hbc hnc
    refine ⟨x7, false, hx7, x9, hx9, x10, ?_, ?_⟩
    · intro p hpm; simp only [Bool.false_eq_true, ↓reduceIte]; exact hp p hpm
    · intro l hlm; simp only [Bool.false_eq_true, ↓reduceIte]; exact hl l (fun p hpm => hdisj p hpm l hlm)
  · have hge4 : 4 ≤ x2.card := by omega
    obtain ⟨s4, hs4_sub, hs4_card⟩ := Finset.exists_subset_card_eq hge4
    obtain ⟨a, ha4⟩ := Finset.card_pos.mp (by omega : 0 < s4.card)
    have hs3_card : (s4.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha4]; omega
    obtain ⟨b, c, d, hbc, hbd, hcd, hs3_eq⟩ := Finset.card_eq_three.mp hs3_card
    have hmem3 : ∀ z, z ∈ s4.erase a ↔ z = b ∨ z = c ∨ z = d := fun z => by rw [hs3_eq]; simp
    have hb_er : b ∈ s4.erase a := (hmem3 b).mpr (Or.inl rfl)
    have hc_er : c ∈ s4.erase a := (hmem3 c).mpr (Or.inr (Or.inl rfl))
    have hd_er : d ∈ s4.erase a := (hmem3 d).mpr (Or.inr (Or.inr rfl))
    have hab : a ≠ b := (Finset.mem_erase.mp hb_er).1.symm
    have hac : a ≠ c := (Finset.mem_erase.mp hc_er).1.symm
    have had : a ≠ d := (Finset.mem_erase.mp hd_er).1.symm
    have ha2 : a ∈ x2 := hs4_sub ha4
    have hb2 : b ∈ x2 := hs4_sub (Finset.mem_of_mem_erase hb_er)
    have hc2 : c ∈ x2 := hs4_sub (Finset.mem_of_mem_erase hc_er)
    have hd2 : d ∈ x2 := hs4_sub (Finset.mem_of_mem_erase hd_er)
    set d1 := b - a; set d2 := c - a; set d3 := d - a
    have his4 : isArc4 d1 d2 d3 = true := by
      simp only [isArc4, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
        List.mem_finRange, true_implies, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨⟨sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hac.symm⟩, sub_ne_zero.mpr had.symm⟩,
        fun h => hbc (by have := congrArg (· + a) h; simpa [d1, d2] using this)⟩,
        fun h => hbd (by have := congrArg (· + a) h; simpa [d1, d3] using this)⟩,
        fun h => hcd (by have := congrArg (· + a) h; simpa [d2, d3] using this)⟩, ?_⟩
      intro l
      have hsub : ({a, b, c, d} : Finset (Fin 13)).filter (fun p => p - (l + a) ∈ Dset) ⊆
          x2.filter (fun p => p - (l + a) ∈ Dset) := by
        intro p hp; simp only [Finset.mem_filter] at hp ⊢
        refine ⟨?_, hp.2⟩
        simp at hp; rcases hp.1 with rfl | rfl | rfl | rfl <;> assumption
      have hcard_le := (Finset.card_le_card hsub).trans (harc2 (l + a))
      have hcalc : (({a, b, c, d} : Finset (Fin 13)).filter (fun p => p - (l + a) ∈ Dset)).card =
          (if inD (0 - l) then 1 else 0) + (if inD (d1 - l) then 1 else 0) +
          (if inD (d2 - l) then 1 else 0) + (if inD (d3 - l) then 1 else 0) := by
        rw [card_filter_insert_of_notMem _ a {b, c, d} (by simp [hab, hac, had]),
            card_filter_insert_of_notMem _ b {c, d} (by simp [hbc, hbd]),
            card_filter_insert_of_notMem _ c {d} (by simp [hcd]),
            card_filter_singleton]
        have h0e : (a - (l + a) ∈ Dset) ↔ inD (0 - l) = true := by rw [inD_iff, show a - (l + a) = 0 - l by abel]
        have h1e : (b - (l + a) ∈ Dset) ↔ inD (d1 - l) = true := by rw [inD_iff, show b - (l + a) = d1 - l by dsimp only [d1]; abel]
        have h2e : (c - (l + a) ∈ Dset) ↔ inD (d2 - l) = true := by rw [inD_iff, show c - (l + a) = d2 - l by dsimp only [d2]; abel]
        have h3e : (d - (l + a) ∈ Dset) ↔ inD (d3 - l) = true := by rw [inD_iff, show d - (l + a) = d3 - l by dsimp only [d3]; abel]
        simp only [h0e, h1e, h2e, h3e]
        omega
      omega
    have hx2_eq : x2 = {a, b, c, d} := by
      ext q
      constructor
      · intro hq
        by_contra hqnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqnot
        obtain ⟨hqa, hqb, hqc, hqd⟩ := hqnot
        obtain ⟨l, hlge⟩ := arc4_no_fifth d1 d2 d3 his4 (q - a)
          (sub_ne_zero.mpr hqa)
          (fun h => hqb (by have := congrArg (· + a) h; simpa [d1] using this))
          (fun h => hqc (by have := congrArg (· + a) h; simpa [d2] using this))
          (fun h => hqd (by have := congrArg (· + a) h; simpa [d3] using this))
        have hsub : ({a, b, c, d, q} : Finset (Fin 13)).filter (fun p => p - (l + a) ∈ Dset) ⊆
            x2.filter (fun p => p - (l + a) ∈ Dset) := by
          intro p hp; simp only [Finset.mem_filter] at hp ⊢
          refine ⟨?_, hp.2⟩
          simp at hp; rcases hp.1 with rfl | rfl | rfl | rfl | rfl <;> assumption
        have hcard_le := (Finset.card_le_card hsub).trans (harc2 (l + a))
        have hcalc : (({a, b, c, d, q} : Finset (Fin 13)).filter (fun p => p - (l + a) ∈ Dset)).card =
            (if inD (0 - l) then 1 else 0) + (if inD (d1 - l) then 1 else 0) +
            (if inD (d2 - l) then 1 else 0) + (if inD (d3 - l) then 1 else 0) +
            (if inD ((q - a) - l) then 1 else 0) := by
          rw [card_filter_insert_of_notMem _ a {b, c, d, q} (by simp [hab, hac, had, Ne.symm hqa]),
              card_filter_insert_of_notMem _ b {c, d, q} (by simp [hbc, hbd, Ne.symm hqb]),
              card_filter_insert_of_notMem _ c {d, q} (by simp [hcd, Ne.symm hqc]),
              card_filter_insert_of_notMem _ d {q} (by simp [Ne.symm hqd]),
              card_filter_singleton]
          have h0e : (a - (l + a) ∈ Dset) ↔ inD (0 - l) = true := by rw [inD_iff, show a - (l + a) = 0 - l by abel]
          have h1e : (b - (l + a) ∈ Dset) ↔ inD (d1 - l) = true := by rw [inD_iff, show b - (l + a) = d1 - l by dsimp only [d1]; abel]
          have h2e : (c - (l + a) ∈ Dset) ↔ inD (d2 - l) = true := by rw [inD_iff, show c - (l + a) = d2 - l by dsimp only [d2]; abel]
          have h3e : (d - (l + a) ∈ Dset) ↔ inD (d3 - l) = true := by rw [inD_iff, show d - (l + a) = d3 - l by dsimp only [d3]; abel]
          have hqe : (q - (l + a) ∈ Dset) ↔ inD ((q - a) - l) = true := by rw [inD_iff, show q - (l + a) = (q - a) - l by abel]
          simp only [h0e, h1e, h2e, h3e, hqe]
          omega
        omega
      · intro hq; simp at hq; rcases hq with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨hav_len, hav_nc⟩ := arc4_avoids_prop d1 d2 d3 his4
    set av := (List.finRange 13).filter (avoids4 d1 d2 d3)
    have hav_nodup : av.Nodup := (List.nodup_finRange 13).filter _
    rcases hav_eq : av with _ | ⟨l0, _ | ⟨l1, _ | ⟨l2, _ | _⟩⟩⟩
    · simp [hav_eq] at hav_len
    · simp [hav_eq] at hav_len
    · simp [hav_eq] at hav_len
    · rw [hav_eq] at hav_nodup hav_nc
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hav_nodup
      obtain ⟨⟨h01, h02⟩, h12, _⟩ := hav_nodup
      have hget0 : [l0, l1, l2].getD 0 0 = l0 := rfl
      have hget1 : [l0, l1, l2].getD 1 0 = l1 := rfl
      have hget2 : [l0, l1, l2].getD 2 0 = l2 := rfl
      rw [hget0, hget1, hget2] at hav_nc
      have hmem_av : ∀ l : Fin 13, avoids4 d1 d2 d3 l = true ↔ l = l0 ∨ l = l1 ∨ l = l2 := by
        intro l
        have h1 : l ∈ av ↔ avoids4 d1 d2 d3 l = true := by
          simp [av, List.mem_filter]
        rw [← h1, hav_eq]
        simp
      apply dual_step x2 x3
      have hnc' : ∀ p : Fin 13, ¬((-(l0 + a)) - p ∈ Dset ∧ (-(l1 + a)) - p ∈ Dset ∧ (-(l2 + a)) - p ∈ Dset) := by
        rintro p ⟨h0, h1, h2⟩
        have h0' : inD ((-p - a) - l0) = true := (inD_iff _).mpr (by rw [show (-p - a) - l0 = -(l0 + a) - p by abel]; exact h0)
        have h1' : inD ((-p - a) - l1) = true := (inD_iff _).mpr (by rw [show (-p - a) - l1 = -(l1 + a) - p by abel]; exact h1)
        have h2' : inD ((-p - a) - l2) = true := (inD_iff _).mpr (by rw [show (-p - a) - l2 = -(l2 + a) - p by abel]; exact h2)
        have := hav_nc (-p - a)
        simp [h0', h1', h2'] at this
      have hn01 : -(l0 + a) ≠ -(l1 + a) := fun h => h01 (by have := congrArg (fun z => -z - a) h; simpa using this)
      have hn02 : -(l0 + a) ≠ -(l2 + a) := fun h => h02 (by have := congrArg (fun z => -z - a) h; simpa using this)
      have hn12 : -(l1 + a) ≠ -(l2 + a) := fun h => h12 (by have := congrArg (fun z => -z - a) h; simpa using this)
      obtain ⟨x7, hx7, x9, hx9, x10, hp, hl⟩ := triple_cover (-(l0 + a)) (-(l1 + a)) (-(l2 + a)) hn01 hn02 hn12 hnc'
      refine ⟨x7, hx7, x9, hx9, x10, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨l, hl3, rfl⟩ := hz
        have hav_l : avoids4 d1 d2 d3 (l - a) = true := by
          simp only [avoids4, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, inD_iff]
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
          · have : 0 - (l - a) = a - l := by abel
            rw [this]; exact hdisj a ha2 l hl3
          · have : d1 - (l - a) = b - l := by dsimp only [d1]; abel
            rw [this]; exact hdisj b hb2 l hl3
          · have : d2 - (l - a) = c - l := by dsimp only [d2]; abel
            rw [this]; exact hdisj c hc2 l hl3
          · have : d3 - (l - a) = d - l := by dsimp only [d3]; abel
            rw [this]; exact hdisj d hd2 l hl3
        have hmem := (hmem_av (l - a)).mp hav_l
        apply hp (-l)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hmem with h | h | h
        · left; rw [← h]; abel
        · right; left; rw [← h]; abel
        · right; right; rw [← h]; abel
      · intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨p, hp2, rfl⟩ := hz
        apply hl (-p)
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rw [hx2_eq] at hp2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp2
        have hcheck : ∀ li : Fin 13, avoids4 d1 d2 d3 li = true → -(li + a) - (-p) ∉ Dset := by
          intro li hli
          simp only [avoids4, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, inD_iff] at hli
          rcases hp2 with hp2 | hp2 | hp2 | hp2
          · rw [hp2]; rw [show -(li + a) - -a = 0 - li by abel]; exact hli.1.1.1
          · rw [hp2]; rw [show -(li + a) - -b = d1 - li by dsimp only [d1]; abel]; exact hli.1.1.2
          · rw [hp2]; rw [show -(li + a) - -c = d2 - li by dsimp only [d2]; abel]; exact hli.1.2
          · rw [hp2]; rw [show -(li + a) - -d = d3 - li by dsimp only [d3]; abel]; exact hli.2
        rcases hu with rfl | rfl | rfl
        · exact hcheck l0 ((hmem_av l0).mpr (Or.inl rfl))
        · exact hcheck l1 ((hmem_av l1).mpr (Or.inr (Or.inl rfl)))
        · exact hcheck l2 ((hmem_av l2).mpr (Or.inr (Or.inr rfl)))
    · simp [hav_eq] at hav_len

theorem solve :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 - x6 ∉ x1) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x6 - x7 ∈ x1}.card ≤ (2 : ℕ)) → ∃ (x7 : ℕ) (x8 : Bool), x7 ∈ [(7405575 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ)] ∧ ∃ x9 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x2, x7.testBit (if x8 = Bool.true then (13 : ℕ) + ↑(-(x9 * x11 + x10)) else ↑(x9 * x11 + x10)) = Bool.true) ∧ ∀ x11 ∈ x3, x7.testBit (if x8 = Bool.true then ↑(-(x9 * x11 + x10)) else (13 : ℕ) + ↑(x9 * x11 + x10)) = Bool.true := by
  intro x1 x2 x3 hdisj harc2 harc3
  change ∀ p ∈ x2, ∀ l ∈ x3, p - l ∉ Dset at hdisj
  change ∀ l : Fin 13, (x2.filter fun p => p - l ∈ Dset).card ≤ 2 at harc2
  change ∀ p : Fin 13, (x3.filter fun l => p - l ∈ Dset).card ≤ 2 at harc3
  by_cases h2 : 3 ≤ x2.card
  · exact card_ge_three_solve x2 x3 hdisj harc2 h2
  · by_cases h3 : 3 ≤ x3.card
    · let y2 := x3.image (fun z => -z)
      let y3 := x2.image (fun z => -z)
      have hy_disj : ∀ p ∈ y2, ∀ l ∈ y3, p - l ∉ Dset := by
        intro p hp l hl
        simp only [y2, y3, Finset.mem_image] at hp hl
        obtain ⟨l0, hl0, rfl⟩ := hp
        obtain ⟨p0, hp0, rfl⟩ := hl
        have : -l0 - -p0 = p0 - l0 := by abel
        rw [this]; exact hdisj p0 hp0 l0 hl0
      have hy_arc2 : ∀ l : Fin 13, (y2.filter fun p => p - l ∈ Dset).card ≤ 2 := by
        intro l
        have hcard : (y2.filter fun p => p - l ∈ Dset).card = (x3.filter fun q => (-l) - q ∈ Dset).card := by
          apply Finset.card_bij (fun p _ => -p)
          · intro p hp
            simp only [y2, Finset.mem_filter, Finset.mem_image] at hp ⊢
            obtain ⟨⟨q, hq, rfl⟩, hmem⟩ := hp
            refine ⟨by simpa using hq, ?_⟩
            have : -l - -(-q) = -q - l := by abel
            rw [this]; exact hmem
          · intro a _ b _ h; exact neg_inj.mp h
          · intro q hq
            simp only [Finset.mem_filter] at hq
            refine ⟨-q, ?_, neg_neg q⟩
            simp only [y2, Finset.mem_filter, Finset.mem_image]
            refine ⟨⟨q, hq.1, rfl⟩, ?_⟩
            have : -q - l = -l - q := by abel
            rw [this]; exact hq.2
        rw [hcard]; exact harc3 (-l)
      have hy_card : 3 ≤ y2.card := by
        have : y2.card = x3.card := Finset.card_image_of_injective x3 neg_injective
        omega
      obtain ⟨x7, x8, hx7, x9, hx9, x10, hp, hl⟩ := card_ge_three_solve y2 y3 hy_disj hy_arc2 hy_card
      refine ⟨x7, !x8, hx7, x9, hx9, -x10, ?_, ?_⟩
      · intro p hp2
        cases x8
        · simp only [Bool.not_false, ↓reduceIte]
          have h := hl (-p) (Finset.mem_image_of_mem _ hp2)
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          have heq : -(x9 * p + -x10) = x9 * (-p) + x10 := by rw [mul_neg]; abel
          rw [heq]; exact h
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have h := hl (-p) (Finset.mem_image_of_mem _ hp2)
          simp only [↓reduceIte] at h
          have heq : x9 * p + -x10 = -(x9 * (-p) + x10) := by rw [mul_neg]; abel
          rw [heq]; exact h
      · intro l hl3
        cases x8
        · simp only [Bool.not_false, ↓reduceIte]
          have h := hp (-l) (Finset.mem_image_of_mem _ hl3)
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          have heq : -(x9 * l + -x10) = x9 * (-l) + x10 := by rw [mul_neg]; abel
          rw [heq]; exact h
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have h := hp (-l) (Finset.mem_image_of_mem _ hl3)
          simp only [↓reduceIte] at h
          have heq : x9 * l + -x10 = -(x9 * (-l) + x10) := by rw [mul_neg]; abel
          rw [heq]; exact h
    · obtain ⟨a, b, c, hab, hac, hbc, hsub, hnc, hdisj3⟩ := arc_le_two_extend x2 x3 hdisj (by omega) (by omega)
      obtain ⟨x7, hx7, x9, hx9, x10, hp, hl⟩ := triple_cover a b c hab hac hbc hnc
      refine ⟨x7, false, hx7, x9, hx9, x10, ?_, ?_⟩
      · intro p hp2; simp only [Bool.false_eq_true, ↓reduceIte]; exact hp p (hsub hp2)
      · intro l hl3; simp only [Bool.false_eq_true, ↓reduceIte]; exact hl l (fun p hp3 => hdisj3 p hp3 l hl3)

end PEqualNP.Outside.L_meta_19020

theorem PEqualNP.Outside.L_meta_19020 : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 - x6 ∉ x1) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x6 - x7 ∈ x1}.card ≤ (2 : ℕ)) → ∃ (x7 : ℕ) (x8 : Bool), x7 ∈ [(7405575 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ)] ∧ ∃ x9 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x2, x7.testBit (if x8 = Bool.true then (13 : ℕ) + ↑(-(x9 * x11 + x10)) else ↑(x9 * x11 + x10)) = Bool.true) ∧ ∀ x11 ∈ x3, x7.testBit (if x8 = Bool.true then ↑(-(x9 * x11 + x10)) else (13 : ℕ) + ↑(x9 * x11 + x10)) = Bool.true) :=
  PEqualNP.Outside.L_meta_19020.solve
