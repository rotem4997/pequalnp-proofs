import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6710_aux

open PEqualNP.HeptadCover

private def inc (p l : Fin 13) : Bool :=
  let d := (p.val + 13 - l.val) % 13
  d == 0 || d == 1 || d == 3 || d == 9

private abbrev Quad := Fin 13 × Fin 13 × Fin 13 × Fin 13

private def memQ (p : Fin 13) (q : Quad) : Bool :=
  p == q.1 || p == q.2.1 || p == q.2.2.1 || p == q.2.2.2

private def missQ (l : Fin 13) (q : Quad) : Bool :=
  !inc q.1 l && !inc q.2.1 l && !inc q.2.2.1 l && !inc q.2.2.2 l

private def isQuad4 (q : Quad) : Bool :=
  let (a, b, c, d) := q
  a != b && a != c && a != d && b != c && b != d && c != d &&
  (List.finRange 13).all fun l =>
    decide ((if inc a l then 1 else 0) + (if inc b l then 1 else 0) +
      (if inc c l then 1 else 0) + (if inc d l then 1 else 0) ≤ 2)

private def quadSet (q : Quad) : Finset (Fin 13) :=
  {q.1, q.2.1, q.2.2.1, q.2.2.2}

private def shiftQ (s : Fin 13) (q : Quad) : Quad :=
  (q.1 + s, q.2.1 + s, q.2.2.1 + s, q.2.2.2 + s)

private def cov0 : List Quad :=
  [(0,1,2,5),(0,1,4,8),(0,3,7,11),(0,2,4,9),(0,3,5,10),(0,6,7,12),(0,5,8,9),(0,7,9,10),
   (0,5,11,12),(0,2,3,6),(0,1,2,11),(0,3,10,12),(0,4,6,9),(0,1,8,10),(0,1,2,7),(0,1,4,12),
   (0,3,4,8),(0,6,7,8),(0,9,11,12),(0,1,2,6),(0,1,4,11),(0,1,8,11),(0,2,3,10),(0,2,5,6),
   (0,3,4,10)]

private def covM0 : List Quad :=
  [(2,4,5,6),(2,4,5,8),(2,4,5,12),(2,4,6,8),(2,4,6,11),(2,4,7,8),(2,4,7,11),(2,4,7,12),
   (2,4,11,12),(2,5,6,10),(2,5,6,12),(2,5,7,8),(2,5,7,10),(2,5,7,12),(2,5,8,10),(2,6,8,10),
   (2,6,8,11),(2,6,10,12),(2,6,11,12),(2,7,8,11),(2,7,10,11),(2,7,10,12),(2,8,10,11),(2,10,11,12),
   (4,5,6,10),(4,5,6,11),(4,5,8,10),(4,5,8,12),(4,5,10,11),(4,5,11,12),(4,6,7,8),(4,6,7,10),
   (4,6,7,11),(4,6,8,10),(4,7,8,12),(4,7,10,11),(4,7,10,12),(4,8,10,12),(4,10,11,12),(5,6,7,10),
   (5,6,7,11),(5,6,7,12),(5,6,11,12),(5,7,8,11),(5,7,8,12),(5,7,10,11),(5,8,10,11),(5,8,11,12),
   (6,7,8,11),(6,7,8,12),(6,7,10,12),(6,8,10,12),(6,8,11,12),(8,10,11,12)]

private lemma mem_singerLines3_iff (p l : Fin 13) :
    p ∈ singerLines3 l ↔ inc p l = true := by
  revert p l; decide

private lemma inc_add (p l s : Fin 13) : inc (p + s) (l + s) = inc p l := by
  have h : ∀ a b c : Fin 13, inc (a + c) (b + c) = inc a b := by decide
  exact h p l s

private lemma inc_sub_cancel (p l s : Fin 13) : inc (p + s) l = inc p (l - s) := by
  have h : l = (l - s) + s := (sub_add_cancel l s).symm
  conv_lhs => rw [h]
  exact inc_add p (l - s) s

private lemma isQuad4_shift (s : Fin 13) (q : Quad) (hq : isQuad4 q = true) :
    isQuad4 (shiftQ s q) = true := by
  rcases q with ⟨a, b, c, d⟩
  simp only [isQuad4, shiftQ, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, decide_eq_true_eq] at hq ⊢
  rcases hq with ⟨⟨⟨⟨⟨⟨hab, hac⟩, had⟩, hbc⟩, hbd⟩, hcd⟩, hlines⟩
  refine ⟨⟨⟨⟨⟨⟨fun h => hab (add_right_cancel h), fun h => hac (add_right_cancel h)⟩,
    fun h => had (add_right_cancel h)⟩, fun h => hbc (add_right_cancel h)⟩,
    fun h => hbd (add_right_cancel h)⟩, fun h => hcd (add_right_cancel h)⟩, ?_⟩
  intro l _
  simp only [inc_sub_cancel, decide_eq_true_eq]
  exact hlines (l - s) (List.mem_finRange _)

private lemma card_inter_le_count4 (a b c d : Fin 13) (S : Finset (Fin 13)) :
    (({a, b, c, d} : Finset (Fin 13)) ∩ S).card ≤
      (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) +
      (if c ∈ S then 1 else 0) + (if d ∈ S then 1 else 0) := by
  have hstep : ∀ (x : Fin 13) (T : Finset (Fin 13)),
      ((insert x T) ∩ S).card ≤ (if x ∈ S then 1 else 0) + (T ∩ S).card := by
    intro x T
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceIte]
      have hsub : insert x T ∩ S ⊆ insert x (T ∩ S) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_insert] at hy ⊢
        rcases hy.1 with rfl | hT
        · exact Or.inl rfl
        · exact Or.inr ⟨hT, hy.2⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le x (T ∩ S)
      omega
    · simp only [hx, ↓reduceIte, Nat.zero_add]
      have hsub : insert x T ∩ S ⊆ T ∩ S := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_insert] at hy ⊢
        rcases hy.1 with rfl | hT
        · exact (hx hy.2).elim
        · exact ⟨hT, hy.2⟩
      exact Finset.card_le_card hsub
  have h1 := hstep a {b, c, d}
  have h2 := hstep b {c, d}
  have h3 := hstep c {d}
  have h4 := hstep d ∅
  change (({d} : Finset (Fin 13)) ∩ S).card ≤ (if d ∈ S then 1 else 0) + (∅ ∩ S).card at h4
  simp only [Finset.empty_inter, Finset.card_empty, Nat.add_zero] at h4
  omega

private lemma isQuadrangle_of_isQuad4 (q : Quad) (hq : isQuad4 q = true) :
    IsQuadrangle singerLines3 (quadSet q) := by
  rcases q with ⟨a, b, c, d⟩
  simp only [isQuad4, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, decide_eq_true_eq] at hq
  rcases hq with ⟨⟨⟨⟨⟨⟨hab, hac⟩, had⟩, hbc⟩, hbd⟩, hcd⟩, hlines⟩
  refine ⟨?_, ?_⟩
  · unfold quadSet
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_insert_of_notMem (by simp [hcd]),
        Finset.card_singleton]
  · intro l
    have hle := card_inter_le_count4 a b c d (singerLines3 l)
    have hl := hlines l (List.mem_finRange l)
    have heq : ∀ x : Fin 13, (if x ∈ singerLines3 l then 1 else 0) = (if inc x l = true then 1 else 0) := by
      intro x
      by_cases hx : inc x l = true
      · simp [mem_singerLines3_iff, hx]
      · simp [mem_singerLines3_iff, hx]
    rw [heq a, heq b, heq c, heq d] at hle
    exact le_trans hle hl

private lemma mem_quadSet_of_memQ {p : Fin 13} {q : Quad} (h : memQ p q = true) :
    p ∈ quadSet q := by
  simp only [memQ, Bool.or_eq_true, beq_iff_eq] at h
  simp only [quadSet, Finset.mem_insert, Finset.mem_singleton]
  rcases h with ((rfl | rfl) | rfl) | rfl <;> simp

private lemma mem_quadSet_shift {p s : Fin 13} {q : Quad} (h : memQ p q = true) :
    p + s ∈ quadSet (shiftQ s q) := by
  simp only [memQ, Bool.or_eq_true, beq_iff_eq] at h
  simp only [quadSet, shiftQ, Finset.mem_insert, Finset.mem_singleton]
  rcases h with ((rfl | rfl) | rfl) | rfl <;> simp

private lemma mem_missLines_shift {l s : Fin 13} {q : Quad} (h : missQ l q = true) :
    l + s ∈ missLines singerLines3 (quadSet (shiftQ s q)) := by
  simp only [missQ, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
  intro p hp
  simp only [quadSet, shiftQ, Finset.mem_insert, Finset.mem_singleton] at hp
  rw [mem_singerLines3_iff]
  rcases hp with rfl | rfl | rfl | rfl <;> rw [inc_add] <;> simp [h1, h2, h3, h4]

private lemma cov0_all_quad : cov0.all isQuad4 = true := by decide

private lemma covM0_all_quad : covM0.all isQuad4 = true := by decide

private lemma cov0_case30 :
    (List.finRange 13).all (fun p1 =>
      (List.finRange 13).all (fun p2 =>
        if p1 == 0 || p2 == 0 || p1 == p2 ||
           (List.finRange 13).any (fun l => inc 0 l && inc p1 l && inc p2 l) then true
        else cov0.any fun q => memQ 0 q && memQ p1 q && memQ p2 q)) = true := by decide

private lemma cov0_case21 :
    (List.finRange 13).all (fun p1 =>
      (List.finRange 13).all (fun l0 =>
        if p1 == 0 || inc 0 l0 || inc p1 l0 then true
        else cov0.any fun q => memQ 0 q && memQ p1 q && missQ l0 q)) = true := by decide

private lemma cov0_case20 :
    (List.finRange 13).all (fun p1 =>
      if p1 == 0 then true
      else cov0.any fun q => memQ 0 q && memQ p1 q) = true := by decide

private lemma cov0_case12 :
    (List.finRange 13).all (fun l0 =>
      (List.finRange 13).all (fun l1 =>
        if inc 0 l0 || inc 0 l1 then true
        else cov0.any fun q => memQ 0 q && missQ l0 q && missQ l1 q)) = true := by decide

private lemma covM0_case02 :
    (List.finRange 13).all (fun l1 =>
      if l1 == 0 then true
      else covM0.any fun q => missQ 0 q && missQ l1 q) = true := by decide

private lemma covM0_case03 :
    (List.finRange 13).all (fun l1 =>
      (List.finRange 13).all (fun l2 =>
        if l1 == 0 || l2 == 0 || l1 == l2 ||
           (List.finRange 13).any (fun p => inc p 0 && inc p l1 && inc p l2) then true
        else covM0.any fun q => missQ 0 q && missQ l1 q && missQ l2 q)) = true := by decide

private lemma cov0_mem_quad {q : Quad} (hq : q ∈ cov0) : isQuad4 q = true :=
  List.all_eq_true.mp cov0_all_quad q hq

private lemma covM0_mem_quad {q : Quad} (hq : q ∈ covM0) : isQuad4 q = true :=
  List.all_eq_true.mp covM0_all_quad q hq

private lemma main_proof (x3 x4 : Finset (Fin 13))
    (hcard : x3.card + x4.card ≤ 3)
    (hnoninc : ¬∃ p ∈ x3, ∃ l ∈ x4, p ∈ singerLines3 l)
    (hnondeg : ¬((x4 = ∅ ∧ x3.card = 3 ∧ ∃ l : Fin 13, x3 ⊆ singerLines3 l) ∨
      x3 = ∅ ∧ x4.card = 3 ∧ ∃ p : Fin 13, ∀ l ∈ x4, p ∈ singerLines3 l)) :
    ∃ Q : Finset (Fin 13),
      IsQuadrangle singerLines3 Q ∧ x3 ⊆ Q ∧ x4 ⊆ missLines singerLines3 Q := by
  have hni : ∀ p ∈ x3, ∀ l ∈ x4, inc p l = false := by
    intro p hp l hl
    cases h : inc p l
    · rfl
    · exact (hnoninc ⟨p, hp, l, hl, (mem_singerLines3_iff p l).mpr h⟩).elim
  rcases h3 : x3.card with _ | _ | _ | _ | n
  · -- x3.card = 0
    have hx3 : x3 = ∅ := Finset.card_eq_zero.mp h3
    subst hx3
    rcases h4 : x4.card with _ | _ | _ | _ | m
    · -- (0, 0)
      have hx4 : x4 = ∅ := Finset.card_eq_zero.mp h4
      subst hx4
      have hq : (0, 1, 2, 5) ∈ cov0 := by decide
      exact ⟨quadSet (0, 1, 2, 5), isQuadrangle_of_isQuad4 _ (cov0_mem_quad hq),
        Finset.empty_subset _, Finset.empty_subset _⟩
    · -- (0, 1)
      obtain ⟨l0, rfl⟩ := Finset.card_eq_one.mp h4
      have hq : (2, 4, 5, 6) ∈ covM0 := by decide
      have hm0 : missQ 0 (2, 4, 5, 6) = true := by decide
      refine ⟨quadSet (shiftQ l0 (2, 4, 5, 6)),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift l0 _ (covM0_mem_quad hq)),
        Finset.empty_subset _, ?_⟩
      intro l hl
      simp only [Finset.mem_singleton] at hl
      rw [hl]
      simpa using mem_missLines_shift (s := l0) hm0
    · -- (0, 2)
      obtain ⟨l0, l1, hne, rfl⟩ := Finset.card_eq_two.mp h4
      have hm1 : (l1 - l0 == 0) = false := by
        simp only [beq_eq_false_iff_ne]
        intro h; exact hne (sub_eq_zero.mp h).symm
      have hstep := List.all_eq_true.mp covM0_case02 (l1 - l0) (List.mem_finRange _)
      simp only [hm1, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨q, hqmem, hm0, hm1q⟩
      refine ⟨quadSet (shiftQ l0 q),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift l0 q (covM0_mem_quad hqmem)),
        Finset.empty_subset _, ?_⟩
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with hl | hl
      · rw [hl]; simpa using mem_missLines_shift (s := l0) hm0
      · rw [hl]; simpa [sub_add_cancel] using mem_missLines_shift (s := l0) hm1q
    · -- (0, 3)
      obtain ⟨l0, l1, l2, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp h4
      have hm1 : (l1 - l0 == 0) = false := by
        simp only [beq_eq_false_iff_ne]; intro h; exact h01 (sub_eq_zero.mp h).symm
      have hm2 : (l2 - l0 == 0) = false := by
        simp only [beq_eq_false_iff_ne]; intro h; exact h02 (sub_eq_zero.mp h).symm
      have hm12 : (l1 - l0 == l2 - l0) = false := by
        simp only [beq_eq_false_iff_ne]; intro h
        exact h12 (by have := congrArg (· + l0) h; simpa using this)
      have hnc : ((List.finRange 13).any fun p => inc p 0 && inc p (l1 - l0) && inc p (l2 - l0)) = false := by
        cases hc : (List.finRange 13).any fun p => inc p 0 && inc p (l1 - l0) && inc p (l2 - l0)
        · rfl
        · exfalso
          rw [List.any_eq_true] at hc
          rcases hc with ⟨p, _, hp⟩
          simp only [Bool.and_eq_true] at hp
          rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩
          apply hnondeg
          right
          refine ⟨rfl, h4, p + l0, ?_⟩
          intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rw [mem_singerLines3_iff]
          rcases hl with hl | hl | hl
          · rw [hl]; simpa using (inc_add p 0 l0).trans hp0
          · rw [hl]; simpa [sub_add_cancel] using (inc_add p (l1 - l0) l0).trans hp1
          · rw [hl]; simpa [sub_add_cancel] using (inc_add p (l2 - l0) l0).trans hp2
      have hstep1 := List.all_eq_true.mp covM0_case03 (l1 - l0) (List.mem_finRange _)
      have hstep := List.all_eq_true.mp hstep1 (l2 - l0) (List.mem_finRange _)
      simp only [hm1, hm2, hm12, hnc, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
        List.any_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨q, hqmem, ⟨hq0, hq1⟩, hq2⟩
      refine ⟨quadSet (shiftQ l0 q),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift l0 q (covM0_mem_quad hqmem)),
        Finset.empty_subset _, ?_⟩
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with hl | hl | hl
      · rw [hl]; simpa using mem_missLines_shift (s := l0) hq0
      · rw [hl]; simpa [sub_add_cancel] using mem_missLines_shift (s := l0) hq1
      · rw [hl]; simpa [sub_add_cancel] using mem_missLines_shift (s := l0) hq2
    · omega
  · -- x3.card = 1
    obtain ⟨p0, rfl⟩ := Finset.card_eq_one.mp h3
    rcases h4 : x4.card with _ | _ | _ | m
    · -- (1, 0)
      have hx4 : x4 = ∅ := Finset.card_eq_zero.mp h4
      subst hx4
      have hq : (0, 1, 2, 5) ∈ cov0 := by decide
      have hm0 : memQ 0 (0, 1, 2, 5) = true := by decide
      refine ⟨quadSet (shiftQ p0 (0, 1, 2, 5)),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift p0 _ (cov0_mem_quad hq)), ?_, Finset.empty_subset _⟩
      intro p hp
      simp only [Finset.mem_singleton] at hp; rw [hp]
      simpa using mem_quadSet_shift (s := p0) hm0
    · -- (1, 1)
      obtain ⟨l0, rfl⟩ := Finset.card_eq_one.mp h4
      have hi0 : inc 0 (l0 - p0) = false := by
        have := hni p0 (by simp) l0 (by simp)
        simpa [← inc_sub_cancel] using this
      have hstep1 := List.all_eq_true.mp cov0_case12 (l0 - p0) (List.mem_finRange _)
      have hstep := List.all_eq_true.mp hstep1 (l0 - p0) (List.mem_finRange _)
      simp only [hi0, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        List.any_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨q, hqmem, ⟨hq0, hql0⟩, _⟩
      refine ⟨quadSet (shiftQ p0 q),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift p0 q (cov0_mem_quad hqmem)), ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_singleton] at hp; rw [hp]
        simpa using mem_quadSet_shift (s := p0) hq0
      · intro l hl
        simp only [Finset.mem_singleton] at hl; rw [hl]
        simpa [sub_add_cancel] using mem_missLines_shift (s := p0) hql0
    · -- (1, 2)
      obtain ⟨l0, l1, _, rfl⟩ := Finset.card_eq_two.mp h4
      have hi0 : inc 0 (l0 - p0) = false := by
        have := hni p0 (by simp) l0 (by simp)
        simpa [← inc_sub_cancel] using this
      have hi1 : inc 0 (l1 - p0) = false := by
        have := hni p0 (by simp) l1 (by simp)
        simpa [← inc_sub_cancel] using this
      have hstep1 := List.all_eq_true.mp cov0_case12 (l0 - p0) (List.mem_finRange _)
      have hstep := List.all_eq_true.mp hstep1 (l1 - p0) (List.mem_finRange _)
      simp only [hi0, hi1, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        List.any_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨q, hqmem, ⟨hq0, hql0⟩, hql1⟩
      refine ⟨quadSet (shiftQ p0 q),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift p0 q (cov0_mem_quad hqmem)), ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_singleton] at hp; rw [hp]
        simpa using mem_quadSet_shift (s := p0) hq0
      · intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with hl | hl
        · rw [hl]; simpa [sub_add_cancel] using mem_missLines_shift (s := p0) hql0
        · rw [hl]; simpa [sub_add_cancel] using mem_missLines_shift (s := p0) hql1
    · omega
  · -- x3.card = 2
    obtain ⟨p0, p1, hne, rfl⟩ := Finset.card_eq_two.mp h3
    have hq1ne : (p1 - p0 == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; exact hne (sub_eq_zero.mp h).symm
    rcases h4 : x4.card with _ | _ | m
    · -- (2, 0)
      have hx4 : x4 = ∅ := Finset.card_eq_zero.mp h4
      subst hx4
      have hstep := List.all_eq_true.mp cov0_case20 (p1 - p0) (List.mem_finRange _)
      simp only [hq1ne, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨q, hqmem, hq0, hq1⟩
      refine ⟨quadSet (shiftQ p0 q),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift p0 q (cov0_mem_quad hqmem)), ?_, Finset.empty_subset _⟩
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp
      · rw [hp]; simpa using mem_quadSet_shift (s := p0) hq0
      · rw [hp]; simpa [sub_add_cancel] using mem_quadSet_shift (s := p0) hq1
    · -- (2, 1)
      obtain ⟨l0, rfl⟩ := Finset.card_eq_one.mp h4
      have hi0 : inc 0 (l0 - p0) = false := by
        have := hni p0 (by simp) l0 (by simp)
        simpa [← inc_sub_cancel] using this
      have hi1 : inc (p1 - p0) (l0 - p0) = false := by
        have := hni p1 (by simp) l0 (by simp)
        simpa [← inc_sub_cancel, sub_add_cancel] using this
      have hstep1 := List.all_eq_true.mp cov0_case21 (p1 - p0) (List.mem_finRange _)
      have hstep := List.all_eq_true.mp hstep1 (l0 - p0) (List.mem_finRange _)
      simp only [hq1ne, hi0, hi1, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
        List.any_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨q, hqmem, ⟨hq0, hq1⟩, hql0⟩
      refine ⟨quadSet (shiftQ p0 q),
        isQuadrangle_of_isQuad4 _ (isQuad4_shift p0 q (cov0_mem_quad hqmem)), ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with hp | hp
        · rw [hp]; simpa using mem_quadSet_shift (s := p0) hq0
        · rw [hp]; simpa [sub_add_cancel] using mem_quadSet_shift (s := p0) hq1
      · intro l hl
        simp only [Finset.mem_singleton] at hl; rw [hl]
        simpa [sub_add_cancel] using mem_missLines_shift (s := p0) hql0
    · omega
  · -- x3.card = 3
    have hx4 : x4 = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hx4
    obtain ⟨p0, p1, p2, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp h3
    have hq1 : (p1 - p0 == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; exact h01 (sub_eq_zero.mp h).symm
    have hq2 : (p2 - p0 == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; exact h02 (sub_eq_zero.mp h).symm
    have hq12 : (p1 - p0 == p2 - p0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h
      exact h12 (by have := congrArg (· + p0) h; simpa using this)
    have hnc : ((List.finRange 13).any fun l => inc 0 l && inc (p1 - p0) l && inc (p2 - p0) l) = false := by
      cases hc : (List.finRange 13).any fun l => inc 0 l && inc (p1 - p0) l && inc (p2 - p0) l
      · rfl
      · exfalso
        rw [List.any_eq_true] at hc
        rcases hc with ⟨l, _, hl⟩
        simp only [Bool.and_eq_true] at hl
        rcases hl with ⟨⟨hl0, hl1⟩, hl2⟩
        apply hnondeg
        left
        refine ⟨rfl, h3, l + p0, ?_⟩
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rw [mem_singerLines3_iff]
        rcases hp with hp | hp | hp
        · rw [hp]; simpa using (inc_add 0 l p0).trans hl0
        · rw [hp]; simpa [sub_add_cancel] using (inc_add (p1 - p0) l p0).trans hl1
        · rw [hp]; simpa [sub_add_cancel] using (inc_add (p2 - p0) l p0).trans hl2
    have hstep1 := List.all_eq_true.mp cov0_case30 (p1 - p0) (List.mem_finRange _)
    have hstep := List.all_eq_true.mp hstep1 (p2 - p0) (List.mem_finRange _)
    simp only [hq1, hq2, hq12, hnc, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      List.any_eq_true, Bool.and_eq_true] at hstep
    rcases hstep with ⟨q, hqmem, ⟨hq0, hq1'⟩, hq2'⟩
    refine ⟨quadSet (shiftQ p0 q),
      isQuadrangle_of_isQuad4 _ (isQuad4_shift p0 q (cov0_mem_quad hqmem)), ?_, Finset.empty_subset _⟩
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp
    · rw [hp]; simpa using mem_quadSet_shift (s := p0) hq0
    · rw [hp]; simpa [sub_add_cancel] using mem_quadSet_shift (s := p0) hq1'
    · rw [hp]; simpa [sub_add_cancel] using mem_quadSet_shift (s := p0) hq2'
  · omega

end PEqualNP.Outside.L_meta_6710_aux

theorem PEqualNP.Outside.L_meta_6710 :
    have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x1 x2 : Finset (Fin (13 : ℕ))) => ∃ x3 ∈ x1, ∃ x4 ∈ x2, x3 ∈ PEqualNP.HeptadCover.singerLines3 x4;
    have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (x3 = ∅ ∧ x2.card = (3 : ℕ) ∧ ∃ (x4 : Fin (13 : ℕ)), x2 ⊆ PEqualNP.HeptadCover.singerLines3 x4) ∨ x2 = ∅ ∧ x3.card = (3 : ℕ) ∧ ∃ (x4 : Fin (13 : ℕ)), ∀ x5 ∈ x3, x4 ∈ PEqualNP.HeptadCover.singerLines3 x5;
    ∀ (x3 x4 : Finset (Fin (13 : ℕ))), x3.card + x4.card ≤ (3 : ℕ) → ¬x1 x3 x4 → ¬x2 x3 x4 → ∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 ∧ x3 ⊆ x8 ∧ x4 ⊆ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8 := by
  intro x1 x2 x3 x4 hcard hni hnd
  exact PEqualNP.Outside.L_meta_6710_aux.main_proof x3 x4 hcard hni hnd
