import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5873_42
    (hSmall :
      let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let U := Ustar G C
      4 ≤ B → U.card ≤ B → B < 2 * U.card →
      B - U.card ≤ 3 → (U.card = 4 → B - U.card ≤ 2) →
      ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover ↑(K ∪ X) ∧
        X.card ≤ B - U.card)
    (hMid :
      let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let U := Ustar G C
      4 ≤ B → U.card ≤ B → B < 2 * U.card →
      8 ≤ U.card → 4 ≤ B - U.card → B - U.card ≤ 6 →
      (U.card ≤ 11 → B - U.card = 4) → (U.card ≤ 15 → B - U.card ≤ 5) →
      ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover ↑(K ∪ X) ∧
        X.card ≤ B - U.card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           (4 : ℕ) ≤ x7 → x8.card ≤ x7 → x7 < (2 : ℕ) * x8.card → ∃ (x12 : Finset (Fin (11 : ℕ))) (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x12 ∧ x1.IsVertexCover ↑(x12 ∪ x13) ∧ x13.card ≤ x7 - x8.card) := by
  intro G C hSize hLeast hTop hJunk B U hB4 hUB hB2U
  let H := G.deleteEdges ↑U
  let q := B - U.card
  have hMinEx : ∃ K : Finset (Fin 11), IsMinCover H K := by
    classical
    let cov (k : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover ↑K ∧ K.card = k
    have ex : ∃ k, cov k := ⟨11, Finset.univ, by simp, by simp⟩
    obtain ⟨K, hK, hKc⟩ := Nat.find_spec ex
    exact ⟨K, hK, fun T hT => hKc.trans_le (Nat.find_min' ex ⟨T, hT, rfl⟩)⟩
  obtain ⟨K, hKmin⟩ := hMinEx
  let edgesL : List (Fin 11 × Fin 11) :=
    [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
     (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let vcs7 : List ℕ :=
    [501, 861, 981, 1451, 1465, 1507, 1521, 1658, 1722, 1778, 1870,
     1884, 1898, 1912, 1934, 1948, 1962, 1976, 1990, 2004, 2018, 2032]
  let setOfMask : ℕ → Finset (Fin 11) := fun m =>
    Finset.univ.filter fun v : Fin 11 => m.testBit v.val
  let covMask : ℕ → ℕ := fun m =>
    edgesL.countP fun e => m.testBit e.1.val || m.testBit e.2.val
  let diffMask : ℕ → ℕ → ℕ := fun t m =>
    (List.finRange 11).countP fun v => t.testBit v.val && !m.testBit v.val
  have hVcsCover : ∀ t ∈ vcs7, ∀ i j : Fin 11, G.Adj i j →
      t.testBit i.val = true ∨ t.testBit j.val = true := by
    decide +kernel
  have hVcs7Card : (setOfMask 501).card = 7 := by
    decide +kernel
  have hDiffBound : ∀ m : Fin 2048,
      (1 ≤ covMask m.val → vcs7.any (fun t => decide (diffMask t m.val ≤ 6)) = true) ∧
      (5 ≤ covMask m.val → vcs7.any (fun t => decide (diffMask t m.val ≤ 5)) = true) ∧
      (9 ≤ covMask m.val → vcs7.any (fun t => decide (diffMask t m.val ≤ 4)) = true) ∧
      (12 ≤ covMask m.val → vcs7.any (fun t => decide (diffMask t m.val ≤ 3)) = true) := by
    decide +kernel
  have hEdgesAdj : ∀ e ∈ edgesL, G.Adj e.1 e.2 := by
    decide +kernel
  have hEdgesNodup : (edgesL.map fun e => s(e.1, e.2)).Nodup := by
    decide +kernel
  have hFoldBit : ∀ (L : List (Fin 11)) (acc : ℕ) (w : Fin 11),
      (L.foldl (fun a v => if v ∈ K then a ||| 2 ^ v.val else a) acc).testBit w.val =
      (acc.testBit w.val || decide (w ∈ L ∧ w ∈ K)) := by
    intro L
    induction L with
    | nil => intro acc w; simp
    | cons a rest ih =>
      intro acc w
      rw [List.foldl_cons, ih]
      by_cases haK : a ∈ K
      · simp only [haK, ↓reduceIte, Nat.testBit_or, Nat.testBit_two_pow]
        by_cases hwa : w = a
        · subst hwa; simp [haK]
        · have hne : a.val ≠ w.val := fun h => hwa (Fin.ext h.symm)
          simp [hne, hwa]
      · simp only [haK, ↓reduceIte]
        by_cases hwa : w = a
        · subst hwa; simp [haK]
        · simp [hwa]
  have hFoldLt : ∀ (L : List (Fin 11)) (acc : ℕ), acc < 2048 →
      L.foldl (fun a v => if v ∈ K then a ||| 2 ^ v.val else a) acc < 2048 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons a rest ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih
      by_cases haK : a ∈ K
      · simp only [haK, ↓reduceIte]
        have h2 : 2 ^ a.val < 2 ^ 11 := Nat.pow_lt_pow_right (by decide) a.isLt
        exact Nat.or_lt_two_pow hacc h2
      · simp only [haK, ↓reduceIte]; exact hacc
  let mVal : ℕ := (List.finRange 11).foldl (fun a v => if v ∈ K then a ||| 2 ^ v.val else a) 0
  have hmLt : mVal < 2048 := hFoldLt (List.finRange 11) 0 (by decide)
  let m : Fin 2048 := ⟨mVal, hmLt⟩
  have hmBit : ∀ v : Fin 11, m.val.testBit v.val = decide (v ∈ K) := by
    intro v
    have h := hFoldBit (List.finRange 11) 0 v
    simpa [m, mVal, List.mem_finRange] using h
  have hFromVcs : ∀ t ∈ vcs7, diffMask t m.val ≤ q →
      ∃ K' X : Finset (Fin 11), IsMinCover H K' ∧ G.IsVertexCover ↑(K' ∪ X) ∧ X.card ≤ q := by
    intro t ht hdiff
    let T := setOfMask t
    refine ⟨K, T \ K, hKmin, ?_, ?_⟩
    · intro i j hij
      rcases hVcsCover t ht i j hij with hi | hj
      · have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        by_cases hiK : i ∈ K
        · exact Or.inl (Finset.mem_union_left _ hiK)
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hiT, hiK⟩))
      · have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        by_cases hjK : j ∈ K
        · exact Or.inr (Finset.mem_union_left _ hjK)
        · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hjT, hjK⟩))
    · have hcard : (T \ K).card = diffMask t m.val := by
        have hfilt : T \ K = Finset.univ.filter fun v : Fin 11 =>
            t.testBit v.val && !m.val.testBit v.val := by
          ext v
          simp only [T, setOfMask, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.and_eq_true, Bool.not_eq_true', hmBit v, decide_eq_false_iff_not]
        rw [hfilt]
        have hlist : (Finset.univ.filter fun v : Fin 11 =>
            t.testBit v.val && !m.val.testBit v.val) =
            ((List.finRange 11).filter fun v : Fin 11 =>
              t.testBit v.val && !m.val.testBit v.val).toFinset := by
          ext v; simp
        rw [hlist, List.toFinset_card_of_nodup ((List.nodup_finRange 11).filter _),
          ← List.countP_eq_length_filter]
      omega
  have hCovGe : 16 - U.card ≤ covMask m.val := by
    have hSub : edgesL.countP (fun e => decide (s(e.1, e.2) ∉ U)) ≤ covMask m.val := by
      apply List.countP_mono_left
      intro e he hnotU
      have hnotU' : s(e.1, e.2) ∉ U := of_decide_eq_true hnotU
      have hadjH : H.Adj e.1 e.2 := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hEdgesAdj e he, hnotU'⟩
      rcases hKmin.1 hadjH with h1 | h2
      · rw [hmBit e.1, decide_eq_true (Finset.mem_coe.mp h1)]; simp
      · rw [hmBit e.2, decide_eq_true (Finset.mem_coe.mp h2)]; simp
    have hSplit : edgesL.countP (fun e => decide (s(e.1, e.2) ∈ U)) +
        edgesL.countP (fun e => decide (s(e.1, e.2) ∉ U)) = 16 := by
      have hlen : edgesL.length = 16 := rfl
      have h := List.length_eq_countP_add_countP (l := edgesL)
        (p := fun e : Fin 11 × Fin 11 => decide (s(e.1, e.2) ∈ U))
      have hneg : edgesL.countP (fun a => decide (¬decide (s(a.1, a.2) ∈ U) = true)) =
          edgesL.countP (fun e => decide (s(e.1, e.2) ∉ U)) := by
        congr 1
      omega
    have hInLe : edgesL.countP (fun e => decide (s(e.1, e.2) ∈ U)) ≤ U.card := by
      rw [List.countP_eq_length_filter]
      have hmap : ((edgesL.filter fun e => decide (s(e.1, e.2) ∈ U)).map fun e => s(e.1, e.2)).length =
          (edgesL.filter fun e => decide (s(e.1, e.2) ∈ U)).length := List.length_map _
      rw [← hmap]
      have hnd : ((edgesL.filter fun e => decide (s(e.1, e.2) ∈ U)).map fun e => s(e.1, e.2)).Nodup := by
        have hsubL : ((edgesL.filter fun e => decide (s(e.1, e.2) ∈ U)).map fun e => s(e.1, e.2)).Sublist
            (edgesL.map fun e => s(e.1, e.2)) := (List.filter_sublist).map _
        exact hEdgesNodup.sublist hsubL
      rw [← List.toFinset_card_of_nodup hnd]
      apply Finset.card_le_card
      intro x hx
      rw [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact of_decide_eq_true (List.mem_filter.mp he).2
    omega
  by_cases h7 : 7 ≤ q
  · refine ⟨K, setOfMask 501 \ K, hKmin, ?_, ?_⟩
    · intro i j hij
      rcases hVcsCover 501 (by simp [vcs7]) i j hij with hi | hj
      · have hiT : i ∈ setOfMask 501 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        by_cases hiK : i ∈ K
        · exact Or.inl (Finset.mem_union_left _ hiK)
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hiT, hiK⟩))
      · have hjT : j ∈ setOfMask 501 := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        by_cases hjK : j ∈ K
        · exact Or.inr (Finset.mem_union_left _ hjK)
        · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hjT, hjK⟩))
    · have hle : (setOfMask 501 \ K).card ≤ (setOfMask 501).card := Finset.card_le_card Finset.sdiff_subset
      omega
  · by_cases h6 : U.card ≤ 15 ∧ 6 ≤ q
    · obtain ⟨t, ht, hdt⟩ := List.any_eq_true.mp ((hDiffBound m).1 (by omega))
      exact hFromVcs t ht (by have := of_decide_eq_true hdt; omega)
    · by_cases h5 : U.card ≤ 11 ∧ 5 ≤ q
      · obtain ⟨t, ht, hdt⟩ := List.any_eq_true.mp ((hDiffBound m).2.1 (by omega))
        exact hFromVcs t ht (by have := of_decide_eq_true hdt; omega)
      · by_cases h4 : U.card ≤ 7 ∧ 4 ≤ q
        · obtain ⟨t, ht, hdt⟩ := List.any_eq_true.mp ((hDiffBound m).2.2.1 (by omega))
          exact hFromVcs t ht (by have := of_decide_eq_true hdt; omega)
        · by_cases h3 : U.card = 4 ∧ q = 3
          · obtain ⟨t, ht, hdt⟩ := List.any_eq_true.mp ((hDiffBound m).2.2.2 (by omega))
            exact hFromVcs t ht (by have := of_decide_eq_true hdt; omega)
          · by_cases hq3 : q ≤ 3
            · exact hSmall C hSize hLeast hTop hJunk hB4 hUB hB2U hq3
                (by intro hu4; change q ≤ 2; change U.card = 4 at hu4; omega)
            · exact hMid C hSize hLeast hTop hJunk hB4 hUB hB2U
                (by change 8 ≤ U.card; omega)
                (by change 4 ≤ q; omega)
                (by change q ≤ 6; omega)
                (by intro h11; change q = 4; change U.card ≤ 11 at h11; omega)
                (by intro h15; change q ≤ 5; change U.card ≤ 15 at h15; omega)
