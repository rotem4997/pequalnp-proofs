import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4695

-- A graph whose cycles all have length at least five has no four-cycle.
lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

-- The edges covered by a family of stars (center, leaf set).
def edgesOf {V : Type*} [DecidableEq V] (F : Finset (V × Finset V)) : Finset (Sym2 V) :=
  F.biUnion fun p => p.2.image fun s => s(p.1, s)

-- Stars whose leaf sets are built by an OR list: edges at most list length plus stars.
lemma key {V : Type*} [DecidableEq V] (L : List (Finset V))
    (hL : ∀ (x9 : List (Finset V)) (x10 : Finset V) (x11 : List (Finset V)),
      L = x9 ++ x10 :: x11 → ∃ (x13 x14 : Finset V), x10 = x13 ∪ x14 ∧
        (x13.card ≤ 1 ∨ x13 ∈ x11) ∧ (x14.card ≤ 1 ∨ x14 ∈ x11))
    (F : Finset (V × Finset V)) (h1 : ∀ p ∈ F, p.2.card ≤ 1 ∨ p.2 ∈ L)
    (hQ : ∀ p ∈ F, ∀ q ∈ F, p.1 ≠ q.1 → (p.2 ∩ q.2).card ≤ 1) :
    (edgesOf F).card ≤ L.length + F.card := by
  induction L generalizing F with
  | nil =>
    simp only [List.not_mem_nil, or_false] at h1
    unfold edgesOf
    calc _ ≤ ∑ p ∈ F, (p.2.image fun s => s(p.1, s)).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ F, 1 := Finset.sum_le_sum fun p hp => (Finset.card_image_le).trans (h1 p hp)
      _ = _ := by simp
  | cons T L' ih =>
    have hL' : ∀ (x9 : List (Finset V)) (x10 : Finset V) (x11 : List (Finset V)),
        L' = x9 ++ x10 :: x11 → ∃ (x13 x14 : Finset V), x10 = x13 ∪ x14 ∧
          (x13.card ≤ 1 ∨ x13 ∈ x11) ∧ (x14.card ≤ 1 ∨ x14 ∈ x11) :=
      fun x9 x10 x11 h => hL (T :: x9) x10 x11 (by rw [h]; rfl)
    obtain ⟨A, B, hT, hA, hB⟩ := hL [] T L' rfl
    by_cases hTc : T.card ≤ 1
    · have h1' : ∀ p ∈ F, p.2.card ≤ 1 ∨ p.2 ∈ L' := by
        intro p hp
        rcases h1 p hp with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inl (h ▸ hTc)
          · exact Or.inr h
      have := ih hL' F h1' hQ
      simp only [List.length_cons]
      omega
    · push Not at hTc
      set K := F.filter (fun p => p.2 = T) with hK
      set F' := F.filter (fun p => ¬ p.2 = T) ∪
        (K.image (fun p => (p.1, A)) ∪ K.image (fun p => (p.1, B))) with hF'
      have hKc : K.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro p hp q hq
        simp only [hK, Finset.mem_filter] at hp hq
        by_contra hpq
        have : p.1 = q.1 := by
          by_contra h
          have := hQ p hp.1 q hq.1 h
          rw [hp.2, hq.2, Finset.inter_self] at this
          omega
        exact hpq (Prod.ext this (hp.2.trans hq.2.symm))
      have hdom : ∀ p' ∈ F', ∃ p ∈ F, p.1 = p'.1 ∧ p'.2 ⊆ p.2 := by
        intro p' hp'
        simp only [hF', hK, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hp'
        rcases hp' with h | ⟨p, ⟨hp, hpT⟩, rfl⟩ | ⟨p, ⟨hp, hpT⟩, rfl⟩
        · exact ⟨p', h.1, rfl, Finset.Subset.refl _⟩
        · exact ⟨p, hp, rfl, by rw [hpT, hT]; exact Finset.subset_union_left⟩
        · exact ⟨p, hp, rfl, by rw [hpT, hT]; exact Finset.subset_union_right⟩
      have h1' : ∀ p ∈ F', p.2.card ≤ 1 ∨ p.2 ∈ L' := by
        intro p' hp'
        simp only [hF', hK, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hp'
        rcases hp' with h | ⟨p, ⟨hp, hpT⟩, rfl⟩ | ⟨p, ⟨hp, hpT⟩, rfl⟩
        · rcases h1 p' h.1 with h' | h'
          · exact Or.inl h'
          · rcases List.mem_cons.mp h' with h' | h'
            · exact absurd h' h.2
            · exact Or.inr h'
        · exact hA
        · exact hB
      have hQ' : ∀ p ∈ F', ∀ q ∈ F', p.1 ≠ q.1 → (p.2 ∩ q.2).card ≤ 1 := by
        intro p hp q hq hne
        obtain ⟨p0, hp0, e1, s1⟩ := hdom p hp
        obtain ⟨q0, hq0, e2, s2⟩ := hdom q hq
        exact (Finset.card_le_card (Finset.inter_subset_inter s1 s2)).trans
          (hQ p0 hp0 q0 hq0 (by rw [e1, e2]; exact hne))
      have hsub : edgesOf F ⊆ edgesOf F' := by
        intro e he
        simp only [edgesOf, Finset.mem_biUnion, Finset.mem_image] at he ⊢
        obtain ⟨p, hp, s, hs, rfl⟩ := he
        by_cases hpT : p.2 = T
        · have hs' : s ∈ A ∪ B := hT ▸ hpT ▸ hs
          have hpK : p ∈ K := by simp only [hK, Finset.mem_filter]; exact ⟨hp, hpT⟩
          rcases Finset.mem_union.mp hs' with hsA | hsB
          · refine ⟨(p.1, A), ?_, s, hsA, rfl⟩
            simp only [hF', Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨p, hpK, rfl⟩)
          · refine ⟨(p.1, B), ?_, s, hsB, rfl⟩
            simp only [hF', Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨p, hpK, rfl⟩)
        · refine ⟨p, ?_, s, hs, rfl⟩
          simp only [hF', Finset.mem_union, Finset.mem_filter]
          exact Or.inl ⟨hp, hpT⟩
      have hcard : F'.card ≤ F.card + 1 := by
        have c1 := Finset.card_union_le (F.filter (fun p => ¬ p.2 = T))
          (K.image (fun p => (p.1, A)) ∪ K.image (fun p => (p.1, B)))
        have c2 := Finset.card_union_le (K.image (fun p => (p.1, A)))
          (K.image (fun p => (p.1, B)))
        have c3 : (K.image (fun p => (p.1, A))).card ≤ K.card := Finset.card_image_le
        have c4 : (K.image (fun p => (p.1, B))).card ≤ K.card := Finset.card_image_le
        have c5 := Finset.card_filter_add_card_filter_not (s := F) (fun p => p.2 = T)
        rw [← hK] at c5
        rw [hF']
        omega
      have e1 := ih hL' F' h1' hQ'
      have e2 := Finset.card_le_card hsub
      simp only [List.length_cons]
      omega

end PEqualNP.Outside.L_meta_4695

theorem PEqualNP.Outside.L_meta_4695 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : List (Finset (Fin x1))) (x6 : ℕ) (x7 x8 : Fin x6 → Finset (Fin x1)), (∀ (x9 : List (Finset (Fin x1))) (x10 : Finset (Fin x1)) (x11 : List (Finset (Fin x1))), x5 = x9 ++ x10 :: x11 → ∃ (x13 : Finset (Fin x1)) (x14 : Finset (Fin x1)), x10 = x13 ∪ x14 ∧ (x13.card ≤ (1 : ℕ) ∨ x13 ∈ x11) ∧ (x14.card ≤ (1 : ℕ) ∨ x14 ∈ x11)) → (∀ (x10 : Fin x6), ((x7 x10).card ≤ (1 : ℕ) ∨ x7 x10 ∈ x5) ∧ ((x8 x10).card ≤ (1 : ℕ) ∨ x8 x10 ∈ x5)) → (∀ (x11 : Fin x1 → Bool), (∃ (x12 : Fin x6), (∃ x13 ∈ x7 x12, x11 x13 = Bool.true) ∧ ∃ x13 ∈ x8 x12, x11 x13 = Bool.true) ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∃ (x12 : Finset (Fin x1)), (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → x13 ∈ x12 ∨ x14 ∈ x12) ∧ x2.edgeSet.ncard + x12.card ≤ x5.length + (2 : ℕ) * x6 := by
  intro n G _ hg L m X Y hL hXY hf
  have hadj : ∀ i, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b := by
    intro i a ha b hb
    obtain ⟨u, w, huw, hu, hw⟩ := (hf (fun v => decide (v = a ∨ v = b))).mp
      ⟨i, ⟨a, ha, by simp⟩, b, hb, by simp⟩
    simp only [decide_eq_true_eq] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact (G.ne_of_adj huw rfl).elim
    · exact huw
    · exact huw.symm
    · exact (G.ne_of_adj huw rfl).elim
  have hcov : ∀ u v, G.Adj u v → ∃ i, ∃ a ∈ X i, ∃ b ∈ Y i, s(a, b) = s(u, v) := by
    intro u v huv
    obtain ⟨i, ⟨a, ha, hau⟩, b, hb, hbv⟩ := (hf (fun x => decide (x = u ∨ x = v))).mpr
      ⟨u, v, huv, by simp, by simp⟩
    simp only [decide_eq_true_eq] at hau hbv
    have hab := hadj i a ha b hb
    refine ⟨i, a, ha, b, hb, ?_⟩
    rcases hau with rfl | rfl <;> rcases hbv with rfl | rfl
    · exact (G.ne_of_adj hab rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (G.ne_of_adj hab rfl).elim
  have hstar : ∀ i, (X i).card ≤ 1 ∨ (Y i).card ≤ 1 := by
    intro i
    by_contra h
    push Not at h
    obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.mp h.1
    obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp h.2
    exact PEqualNP.Outside.L_meta_4695.no4 G hg a b a' b' (hadj i a ha b hb)
      (hadj i a' ha' b hb).symm (hadj i a' ha' b' hb') (hadj i a ha b' hb').symm haa hbb
  let g : Fin m → Finset (Fin n × Finset (Fin n)) := fun i =>
    if (X i).card ≤ 1 then (X i) ×ˢ {Y i} else (Y i) ×ˢ {X i}
  let F := Finset.univ.biUnion g
  have hmemF : ∀ p ∈ F, ∃ i, (p ∈ (X i) ×ˢ {Y i} ∧ (X i).card ≤ 1) ∨
      (p ∈ (Y i) ×ˢ {X i} ∧ ¬ (X i).card ≤ 1) := by
    intro p hp
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hp
    refine ⟨i, ?_⟩
    by_cases hc : (X i).card ≤ 1
    · simp only [g, hc, ite_true] at hi
      exact Or.inl ⟨hi, hc⟩
    · simp only [g, hc, ite_false] at hi
      exact Or.inr ⟨hi, hc⟩
  have hFcard : F.card ≤ m := by
    calc F.card ≤ ∑ i, (g i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, 1 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hc : (X i).card ≤ 1
        · simp only [g, hc, ite_true, Finset.card_product, Finset.card_singleton, mul_one]
        · simp only [g, hc, ite_false, Finset.card_product, Finset.card_singleton, mul_one]
          exact (hstar i).resolve_left hc
      _ = m := by simp
  have hstarF : ∀ p ∈ F, ∀ s ∈ p.2, G.Adj p.1 s := by
    intro p hp s hs
    obtain ⟨i, ⟨hi, -⟩ | ⟨hi, -⟩⟩ := hmemF p hp
    · rw [Finset.mem_product, Finset.mem_singleton] at hi
      rw [hi.2] at hs
      exact hadj i p.1 hi.1 s hs
    · rw [Finset.mem_product, Finset.mem_singleton] at hi
      rw [hi.2] at hs
      exact (hadj i s hs p.1 hi.1).symm
  have h1 : ∀ p ∈ F, p.2.card ≤ 1 ∨ p.2 ∈ L := by
    intro p hp
    obtain ⟨i, ⟨hi, -⟩ | ⟨hi, -⟩⟩ := hmemF p hp
    · rw [Finset.mem_product, Finset.mem_singleton] at hi
      rw [hi.2]
      exact (hXY i).2
    · rw [Finset.mem_product, Finset.mem_singleton] at hi
      rw [hi.2]
      exact (hXY i).1
  have hQ : ∀ p ∈ F, ∀ q ∈ F, p.1 ≠ q.1 → (p.2 ∩ q.2).card ≤ 1 := by
    intro p hp q hq hne
    by_contra h
    push Not at h
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp h
    rw [Finset.mem_inter] at hs ht
    exact PEqualNP.Outside.L_meta_4695.no4 G hg p.1 s q.1 t (hstarF p hp s hs.1)
      (hstarF q hq s hs.2).symm (hstarF q hq t ht.2) (hstarF p hp t ht.1).symm hne hst
  have hkey := PEqualNP.Outside.L_meta_4695.key L hL F h1 hQ
  have hE : G.edgeSet ⊆ ↑(PEqualNP.Outside.L_meta_4695.edgesOf F) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨i, a, ha, b, hb, hab⟩ := hcov u v he
      rw [Finset.mem_coe, ← hab]
      simp only [PEqualNP.Outside.L_meta_4695.edgesOf, Finset.mem_biUnion, Finset.mem_image]
      by_cases hc : (X i).card ≤ 1
      · refine ⟨(a, Y i), ?_, b, hb, rfl⟩
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
        simp only [g, hc, ite_true, Finset.mem_product, Finset.mem_singleton]
        exact ⟨ha, trivial⟩
      · refine ⟨(b, X i), ?_, a, ha, Sym2.eq_swap⟩
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
        simp only [g, hc, ite_false, Finset.mem_product, Finset.mem_singleton]
        exact ⟨hb, trivial⟩
  refine ⟨F.image Prod.fst, ?_, ?_⟩
  · intro u v huv
    have hm := hE (show s(u, v) ∈ G.edgeSet from huv)
    rw [Finset.mem_coe] at hm
    simp only [PEqualNP.Outside.L_meta_4695.edgesOf, Finset.mem_biUnion,
      Finset.mem_image] at hm
    obtain ⟨p, hp, s, -, hps⟩ := hm
    rcases Sym2.eq_iff.mp hps with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨p, hp, h⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨p, hp, h⟩)
  · have c1 : G.edgeSet.ncard ≤ (PEqualNP.Outside.L_meta_4695.edgesOf F).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hE (Finset.finite_toSet _)
    have c2 : (F.image Prod.fst).card ≤ F.card := Finset.card_image_le
    omega
