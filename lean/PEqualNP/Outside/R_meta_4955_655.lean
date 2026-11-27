import PEqualNP.Defs

/-
  Cut through the positive/negative rectangle game. Alice holds a flag, Bob a
  quadrangle support. A leaf exhibits a point or line on Alice's support but
  absent from Bob's. Two marked quadrangles preserve the strict witnesses at
  the final meet: each is an extra Alice input at one of the two roots and
  a Bob input at the other.

  A palette is an UNORDERED set of non-leaf rectangles. Quantifying over
  lower sets expresses least closure under horizontal/vertical forks and
  free restriction, so a cycle is not a derivation. Inclusion-minimality
  removes every dispensable rectangle, even after sharing between roots.
-/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_4955_655
    (decode :
      have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ));
      let S := PEqualNP.HeptadCover.singerLines3
      let flag := fun e : Fin 13 × Fin 13 => ({Sum.inl e.1, Sum.inr e.2} : Finset (Fin 13 ⊕ Fin 13))
      let E := flag '' (↑((PEqualNP.HeptadCover.incidences S).erase (0,0)) : Set (Fin 13 × Fin 13))
      let N := PEqualNP.HeptadCover.supp S '' (↑(PEqualNP.HeptadCover.quadrangles S) : Set (Finset (Fin 13)))
      ∃ row : Finset (Fin 13 ⊕ Fin 13) → Fin 285,
        (∀ x ∈ E, (row x).val < 51) ∧ (∀ y ∈ N, 51 ≤ (row y).val) ∧
        (∀ j : Fin 285, 51 ≤ j.val → ∃ y ∈ N, row y = j) ∧
        ∀ s ∈ x2, ∃ i : Fin 13 ⊕ Fin 13, ∀ x ∈ E ∪ N, row x ∈ s ↔ i ∈ x)
    (lower :
      let S := PEqualNP.HeptadCover.singerLines3
      let flag := fun e : Fin 13 × Fin 13 => ({Sum.inl e.1, Sum.inr e.2} : Finset (Fin 13 ⊕ Fin 13))
      let E := flag '' (↑((PEqualNP.HeptadCover.incidences S).erase (0,0)) : Set (Fin 13 × Fin 13))
      let N := PEqualNP.HeptadCover.supp S '' (↑(PEqualNP.HeptadCover.quadrangles S) : Set (Finset (Fin 13)))
      let U := Finset (Fin 13 ⊕ Fin 13)
      let R := Set U × Set U
      let leaf : R → Prop := fun r => r.1 = ∅ ∨ r.2 = ∅ ∨
        ∃ i, (∀ x ∈ r.1, i ∈ x) ∧ (∀ y ∈ r.2, i ∉ y)
      let joinable : R → R → R → Prop := fun r u v =>
        r ≤ (u.1 ∪ v.1, u.2 ∩ v.2) ∨ r ≤ (u.1 ∩ v.1, u.2 ∪ v.2)
      let reach : Finset R → Prop := fun G =>
        ∃ H ⊆ N, ∃ l ∈ H, ∃ r ∈ N \ H, (∀ t ∈ G, t.1 ⊆ insert l (insert r E)) ∧ ∀ D : LowerSet R,
          (∀ t, leaf t → t ∈ D) →
          (∀ t ∈ G, ∀ u ∈ D, ∀ v ∈ D, ¬ t ≤ u → ¬ t ≤ v → joinable t u v → t ∈ D) →
          (insert r E, H) ∈ D ∧ (insert l E, N \ H) ∈ D
      ∀ G : Finset R,
        (∀ r ∈ G, ¬leaf r ∧ (∀ x ∈ r.1, x ∉ r.2) ∧ r.2 ⊆ N) →
        reach G → (∀ W ⊂ G, ¬reach W) →
        (∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ E ⊆ a.1 ∧ E ⊆ b.1 ∧ N ⊆ a.2 ∪ b.2) →
        62 ≤ G.card)
    : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  classical
  intro x1 x2 gates cost legal a ha b hb hab hba cut
  let S := PEqualNP.HeptadCover.singerLines3
  let flag := fun e : Fin 13 × Fin 13 => ({Sum.inl e.1, Sum.inr e.2} : Finset (Fin 13 ⊕ Fin 13))
  let E := flag '' (↑((PEqualNP.HeptadCover.incidences S).erase (0,0)) : Set (Fin 13 × Fin 13))
  let N := PEqualNP.HeptadCover.supp S '' (↑(PEqualNP.HeptadCover.quadrangles S) : Set (Finset (Fin 13)))
  let U := Finset (Fin 13 ⊕ Fin 13)
  let R := Set U × Set U
  let leaf : R → Prop := fun r => r.1 = ∅ ∨ r.2 = ∅ ∨
    ∃ i, (∀ x ∈ r.1, i ∈ x) ∧ (∀ y ∈ r.2, i ∉ y)
  let joinable : R → R → R → Prop := fun r u v =>
    r ≤ (u.1 ∪ v.1, u.2 ∩ v.2) ∨ r ≤ (u.1 ∩ v.1, u.2 ∪ v.2)
  let reach : Finset R → Prop := fun G =>
    ∃ H ⊆ N, ∃ l ∈ H, ∃ r ∈ N \ H, (∀ t ∈ G, t.1 ⊆ insert l (insert r E)) ∧ ∀ D : LowerSet R,
      (∀ t, leaf t → t ∈ D) →
      (∀ t ∈ G, ∀ u ∈ D, ∀ v ∈ D, ¬ t ≤ u → ¬ t ≤ v → joinable t u v → t ∈ D) →
      (insert r E, H) ∈ D ∧ (insert l E, N \ H) ∈ D
  obtain ⟨row, pos, neg, onto, columns⟩ := decode
  change ∀ x ∈ E, (row x).val < 51 at pos
  change ∀ y ∈ N, 51 ≤ (row y).val at neg
  change ∀ j : Fin 285, 51 ≤ j.val → ∃ y ∈ N, row y = j at onto
  have classify (j : Fin 285) : j ∈ a ∩ b ↔ j.val < 51 := by
    rw [cut]
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  have mk : 
      ∀ (E N : Set (Finset (Fin 13 ⊕ Fin 13))),
      let U := Finset (Fin 13 ⊕ Fin 13)
      let R := Set U × Set U
      let leaf : R → Prop := fun r => r.1 = ∅ ∨ r.2 = ∅ ∨
        ∃ i, (∀ x ∈ r.1, i ∈ x) ∧ (∀ y ∈ r.2, i ∉ y)
      let joinable : R → R → R → Prop := fun r u v =>
        r ≤ (u.1 ∪ v.1, u.2 ∩ v.2) ∨ r ≤ (u.1 ∩ v.1, u.2 ∪ v.2)
      let reach : Finset R → Prop := fun G =>
        ∃ H ⊆ N, ∃ l ∈ H, ∃ r ∈ N \ H, (∀ t ∈ G, t.1 ⊆ insert l (insert r E)) ∧ ∀ D : LowerSet R,
          (∀ t, leaf t → t ∈ D) →
          (∀ t ∈ G, ∀ u ∈ D, ∀ v ∈ D, ¬ t ≤ u → ¬ t ≤ v → joinable t u v → t ∈ D) →
          (insert r E, H) ∈ D ∧ (insert l E, N \ H) ∈ D
      ∀ (row : U → Fin 285) (inputs gates : List (Finset (Fin 285))),
        (∀ s ∈ inputs, ∃ i : Fin 13 ⊕ Fin 13, ∀ x ∈ E ∪ N, row x ∈ s ↔ i ∈ x) →
        (∀ j : Fin gates.length, ∃ u ∈ inputs ++ gates.take j.val, ∃ v ∈ inputs ++ gates.take j.val,
          gates.get j = u ∩ v ∨ gates.get j = u ∪ v) →
        ∀ a ∈ inputs ++ gates, ∀ b ∈ inputs ++ gates,
        (∀ x ∈ E, row x ∈ a ∩ b) →
        (∀ y ∈ N, row y ∉ a ∩ b) →
        (∃ l ∈ N, row l ∈ b ∧ row l ∉ a) →
        (∃ r ∈ N, row r ∈ a ∧ row r ∉ b) →
        ∃ G : Finset R, G.card ≤ gates.length ∧
          (∀ r ∈ G, ¬leaf r ∧ Disjoint r.1 r.2 ∧ r.2 ⊆ N) ∧ reach G := by
    classical
    intro E N U R leaf joinable reach row inputs gates hin hgate a ha b hb hpos hneg hleft hright
    obtain ⟨l, hl, hlb, hla⟩ := hleft
    obtain ⟨r, hr, hra, hrb⟩ := hright
    let A : Set U := insert l (insert r E)
    have hA : A ⊆ E ∪ N := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact Or.inr hl
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact Or.inr hr
      · exact Or.inl hx
    let rect : Finset (Fin 285) → R := fun s =>
      ({x | x ∈ A ∧ row x ∈ s}, {y | y ∈ N ∧ row y ∉ s})
    let G := (gates.map rect).toFinset.filter (fun t => ¬ leaf t)
    have gateRect : ∀ t ∈ G, ∃ s ∈ gates, rect s = t := by
      intro t ht
      exact List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp ht).1)
    refine ⟨G, ?_, ?_, ?_⟩
    · exact (Finset.card_filter_le _ _).trans (by simpa using (gates.map rect).toFinset_card_le)
    · intro t ht
      have hn := (Finset.mem_filter.mp ht).2
      obtain ⟨s, hs, rfl⟩ := gateRect t ht
      exact ⟨hn, Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2), fun _ hy => hy.1⟩
    let H : Set U := {y | y ∈ N ∧ row y ∉ a}
    refine ⟨H, fun _ hy => hy.1, l, ⟨hl, hla⟩, r, ⟨hr, fun hy => hy.2 hra⟩, ?_, ?_⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := gateRect t ht
      exact fun _ hx => hx.1
    intro D base split
    have inputWin : ∀ s ∈ inputs, rect s ∈ D := by
      intro s hs
      obtain ⟨i, hi⟩ := hin s hs
      exact base _ (Or.inr (Or.inr ⟨i, fun x hx => (hi x (hA hx.1)).mp hx.2,
        fun y hy hiy => hy.2 ((hi y (Or.inr hy.1)).mpr hiy)⟩))
    have gateWin : ∀ n, ∀ hn : n < gates.length, rect (gates.get ⟨n, hn⟩) ∈ D := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro hn
        let j : Fin gates.length := ⟨n, hn⟩
        obtain ⟨u, hu, v, hv, hcomb⟩ := hgate j
        have earlier : ∀ s ∈ inputs ++ gates.take n, rect s ∈ D := by
          intro s hs
          rcases List.mem_append.mp hs with hs | hs
          · exact inputWin s hs
          · obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.mp hs
            exact ih m (lt_min_iff.mp hm).1 (lt_min_iff.mp hm).2
        have branch : joinable (rect (gates.get j)) (rect u) (rect v) := by
          change rect (gates.get j) ≤ ((rect u).1 ∪ (rect v).1, (rect u).2 ∩ (rect v).2) ∨
            rect (gates.get j) ≤ ((rect u).1 ∩ (rect v).1, (rect u).2 ∪ (rect v).2)
          rcases hcomb with h | h
          · rw [h]
            right
            refine ⟨?_, ?_⟩
            · intro x hx
              obtain ⟨hdom, hs⟩ := hx
              obtain ⟨hsu, hsv⟩ := Finset.mem_inter.mp hs
              exact ⟨⟨hdom, hsu⟩, ⟨hdom, hsv⟩⟩
            · intro y hy
              obtain ⟨hdom, hs⟩ := hy
              by_cases hyu : row y ∈ u
              · exact Or.inr ⟨hdom, fun hyv => hs (Finset.mem_inter.mpr ⟨hyu, hyv⟩)⟩
              · exact Or.inl ⟨hdom, hyu⟩
          · rw [h]
            left
            refine ⟨?_, ?_⟩
            · intro x hx
              obtain ⟨hdom, hs⟩ := hx
              exact (Finset.mem_union.mp hs).imp (fun hsu => ⟨hdom, hsu⟩) (fun hsv => ⟨hdom, hsv⟩)
            · intro y hy
              obtain ⟨hdom, hs⟩ := hy
              exact ⟨⟨hdom, fun hsu => hs (Finset.mem_union.mpr (Or.inl hsu))⟩,
                ⟨hdom, fun hsv => hs (Finset.mem_union.mpr (Or.inr hsv))⟩⟩
        change rect (gates.get j) ∈ D
        by_cases hleaf : leaf (rect (gates.get j))
        · exact base _ hleaf
        · have ku := earlier u hu
          have kv := earlier v hv
          by_cases hru : rect (gates.get j) ≤ rect u
          · exact D.lower' hru ku
          by_cases hrv : rect (gates.get j) ≤ rect v
          · exact D.lower' hrv kv
          have hG : rect (gates.get j) ∈ G := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
            (List.mem_map.mpr ⟨_, gates.get_mem j, rfl⟩), hleaf⟩
          exact split _ hG _ ku _ kv hru hrv branch
    have allWin : ∀ s ∈ inputs ++ gates, rect s ∈ D := by
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact inputWin s hs
      · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hs
        exact gateWin j.val j.isLt
    constructor
    · apply D.lower' _ (allWin a ha)
      refine ⟨fun x hx => ⟨Set.mem_insert_of_mem _ hx, ?_⟩, fun _ hy => hy⟩
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hra
      · exact (Finset.mem_inter.mp (hpos x hx)).1
    · apply D.lower' _ (allWin b hb)
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact ⟨Set.mem_insert _ _, hlb⟩
        · exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx),
            (Finset.mem_inter.mp (hpos x hx)).2⟩
      · intro y hy
        refine ⟨hy.1, fun hyb => ?_⟩
        have hya : row y ∈ a := by
          by_contra h
          exact hy.2 ⟨hy.1, h⟩
        exact hneg y hy.1 (Finset.mem_inter.mpr ⟨hya, hyb⟩)
  have weak (j : Fin gates.length) : ∃ u ∈ x2 ++ gates.take j.val, ∃ v ∈ x2 ++ gates.take j.val,
      gates.get j = u ∩ v ∨ gates.get j = u ∪ v := by
    obtain ⟨u, hu, v, hv, _, _, _, hop⟩ := legal j
    exact ⟨u, hu, v, hv, hop⟩
  obtain ⟨p, pap, pnb⟩ := Finset.not_subset.mp hab
  obtain ⟨q, qb, qna⟩ := Finset.not_subset.mp hba
  have hp : ¬ p ∈ a ∩ b := fun h => pnb (Finset.mem_inter.mp h).2
  have hq : ¬ q ∈ a ∩ b := fun h => qna (Finset.mem_inter.mp h).1
  obtain ⟨r, hr, eqr⟩ := onto p (Nat.le_of_not_gt (fun h => hp ((classify p).mpr h)))
  obtain ⟨l, hl, eql⟩ := onto q (Nat.le_of_not_gt (fun h => hq ((classify q).mpr h)))
  obtain ⟨G, budget, proper, derivable⟩ := mk E N row x2 gates columns weak a ha b hb
    (fun x hx => (classify _).mpr (pos x hx))
    (fun y hy h => (Nat.not_lt_of_ge (neg y hy)) ((classify _).mp h))
    ⟨l, hl, eql.symm ▸ qb, eql.symm ▸ qna⟩ ⟨r, hr, eqr.symm ▸ pap, eqr.symm ▸ pnb⟩
  have prune : 
      ∀ (X : Type) (G : Finset X) (good : Finset X → Prop), good G →
        ∃ V ⊆ G, good V ∧ ∀ W ⊂ V, ¬good W := by
    classical
    intro X G good
    induction G using Finset.strongInductionOn
    rename_i G ih
    intro hG
    by_cases h : ∃ W ⊂ G, good W
    · obtain ⟨W, hWG, hW⟩ := h
      obtain ⟨V, hVW, hV, hmin⟩ := ih W hWG hW
      exact ⟨V, hVW.trans (Finset.ssubset_iff_subset_ne.mp hWG).1, hV, hmin⟩
    · exact ⟨G, fun _ hx => hx, hG, fun W hWG hW => h ⟨W, hWG, hW⟩⟩
  obtain ⟨V, hVG, hV, minimal⟩ := prune R G reach derivable
  have factors : 
      ∀ (V : Finset R), (∀ r ∈ V, Disjoint r.1 r.2) → reach V →
        ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧ E ⊆ a.1 ∧ E ⊆ b.1 ∧ N ⊆ a.2 ∪ b.2 := by
    intro V clean hV
    obtain ⟨H, hn, l, hl, r, hr, _, force⟩ := hV
    have e₁ : flag (1,1) ∈ E :=
      ⟨(1,1), by decide, rfl⟩
    have e₂ : flag (2,2) ∈ E :=
      ⟨(2,2), by decide, rfl⟩
    have apart : Disjoint (flag (1,1)) (flag (2,2)) := by decide
    have nonleaf (t : R) (ht : E ⊆ t.1) (hb : t.2.Nonempty) : ¬ leaf t := by
      rintro (h | h | ⟨i, hi, _⟩)
      · have h' := ht e₁
        rw [h] at h'
        exact h'
      · rw [h] at hb
        exact Set.not_nonempty_empty hb
      · exact Finset.disjoint_left.mp apart (hi _ (ht e₁)) (hi _ (ht e₂))
    have contains (z : R) (hE : E ⊆ z.1) (hz : z.2.Nonempty)
        (which : z = (insert r E, H) ∨ z = (insert l E, N \ H)) :
        ∃ t ∈ V, z ≤ t := by
      by_contra bad
      let D : LowerSet R := ⟨{t | ¬ z ≤ t}, by
        intro u v h hv hu
        exact hv (hu.trans h)⟩
      have base (t : R) (h : leaf t) : t ∈ D := by
        intro hzt
        exact nonleaf t (hE.trans hzt.1) (hz.mono hzt.2) h
      have closed (t : R) (ht : t ∈ V) : t ∈ D := fun h => bad ⟨t, ht, h⟩
      obtain ⟨dx, dy⟩ := force D base (fun t ht _ _ _ _ _ _ _ => closed t ht)
      rcases which with rfl | rfl
      · exact dx le_rfl
      · exact dy le_rfl
    obtain ⟨a, ha, xa⟩ := contains (insert r E, H) (Set.subset_insert _ _) ⟨l,hl⟩ (Or.inl rfl)
    obtain ⟨b, hb, yb⟩ := contains (insert l E, N \ H) (Set.subset_insert _ _) ⟨r,hr⟩ (Or.inr rfl)
    refine ⟨a, ha, b, hb, ?_, (Set.subset_insert _ _).trans xa.1, (Set.subset_insert _ _).trans yb.1, ?_⟩
    · intro hab
      subst b
      exact Set.disjoint_left.mp (clean a ha) (yb.1 (Set.mem_insert l E)) (xa.2 hl)
    · intro q hq
      by_cases h : q ∈ H
      · exact Or.inl (xa.2 h)
      · exact Or.inr (yb.2 ⟨hq,h⟩)
  have lb := lower V (fun t ht => ⟨(proper t (hVG ht)).1,
    fun _ hx => Set.disjoint_left.mp (proper t (hVG ht)).2.1 hx, (proper t (hVG ht)).2.2⟩) hV minimal
    (factors V (fun t ht => (proper t (hVG ht)).2.1) hV)
  have upper := (Finset.card_le_card hVG).trans (budget.trans cost)
  exact (by decide : ¬ 62 ≤ 61) (lb.trans upper)
