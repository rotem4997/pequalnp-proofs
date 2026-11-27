import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_17121_2
    (h0 : let gate := fun (w : Finset (BitVec 32)) (z : BitVec 32) => (∃ u ∈ w, ∃ v ∈ w, z = u &&& v ∨ z = u ||| v) ∧ ∀ u ∈ w, (u ^^^ 16383) &&& (z ^^^ 16383) ≠ u ^^^ 16383
      let ok := fun (w : Finset (BitVec 32)) (s : List (BitVec 32)) => ∀ l z r, s = l ++ z :: r → gate (w ∪ l.toFinset) z
      let sep := fun (w : Finset (BitVec 32)) => ∀ i j : Fin 32, i.val < 14 → 14 ≤ j.val → ∃ u ∈ w, u.getLsbD i.val = true ∧ u.getLsbD j.val = false
      let a := ([0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752] : List (BitVec 32)).toFinset
      ∀ p : List (BitVec 32), p.length ≤ 12 → ok a p → ∀ f ⊆ a ∪ p.toFinset, f.card ≤ 7 → sep f → ∀ t : List (BitVec 32), t.length ≤ 6 → ok f t → (16383 : BitVec 32) ∉ f ∪ t.toFinset)
    (h1 : let gate := fun (w : Finset (BitVec 32)) (z : BitVec 32) => (∃ u ∈ w, ∃ v ∈ w, z = u &&& v ∨ z = u ||| v) ∧ ∀ u ∈ w, (u ^^^ 16383) &&& (z ^^^ 16383) ≠ u ^^^ 16383
      let ok := fun (w : Finset (BitVec 32)) (s : List (BitVec 32)) => ∀ l z r, s = l ++ z :: r → gate (w ∪ l.toFinset) z
      let sep := fun (w : Finset (BitVec 32)) => ∀ i j : Fin 32, i.val < 14 → 14 ≤ j.val → ∃ u ∈ w, u.getLsbD i.val = true ∧ u.getLsbD j.val = false
      let a := ([8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578] : List (BitVec 32)).toFinset
      ∀ p : List (BitVec 32), p.length ≤ 12 → ok a p → ∀ f ⊆ a ∪ p.toFinset, f.card ≤ 7 → sep f → ∀ t : List (BitVec 32), t.length ≤ 6 → ok f t → (16383 : BitVec 32) ∉ f ∪ t.toFinset)
    (h2 : let gate := fun (w : Finset (BitVec 32)) (z : BitVec 32) => (∃ u ∈ w, ∃ v ∈ w, z = u &&& v ∨ z = u ||| v) ∧ ∀ u ∈ w, (u ^^^ 16383) &&& (z ^^^ 16383) ≠ u ^^^ 16383
      let ok := fun (w : Finset (BitVec 32)) (s : List (BitVec 32)) => ∀ l z r, s = l ++ z :: r → gate (w ∪ l.toFinset) z
      let sep := fun (w : Finset (BitVec 32)) => ∀ i j : Fin 32, i.val < 14 → 14 ≤ j.val → ∃ u ∈ w, u.getLsbD i.val = true ∧ u.getLsbD j.val = false
      let a := ([8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962] : List (BitVec 32)).toFinset
      ∀ p : List (BitVec 32), p.length ≤ 12 → ok a p → ∀ f ⊆ a ∪ p.toFinset, f.card ≤ 7 → sep f → ∀ t : List (BitVec 32), t.length ≤ 6 → ok f t → (16383 : BitVec 32) ∉ f ∪ t.toFinset)
    (h3 : let gate := fun (w : Finset (BitVec 32)) (z : BitVec 32) => (∃ u ∈ w, ∃ v ∈ w, z = u &&& v ∨ z = u ||| v) ∧ ∀ u ∈ w, (u ^^^ 16383) &&& (z ^^^ 16383) ≠ u ^^^ 16383
      let ok := fun (w : Finset (BitVec 32)) (s : List (BitVec 32)) => ∀ l z r, s = l ++ z :: r → gate (w ∪ l.toFinset) z
      let sep := fun (w : Finset (BitVec 32)) => ∀ i j : Fin 32, i.val < 14 → 14 ≤ j.val → ∃ u ∈ w, u.getLsbD i.val = true ∧ u.getLsbD j.val = false
      let a := ([16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258] : List (BitVec 32)).toFinset
      ∀ p : List (BitVec 32), p.length ≤ 12 → ok a p → ∀ f ⊆ a ∪ p.toFinset, f.card ≤ 7 → sep f → ∀ t : List (BitVec 32), t.length ≤ 6 → ok f t → (16383 : BitVec 32) ∉ f ∪ t.toFinset)
    : (∀ x1 ∈ [[(0 : BitVec (32 : ℕ)), (2592243715 : BitVec (32 : ℕ)), (133562380 : BitVec (32 : ℕ)), (2844803120 : BitVec (32 : ℕ)), (84754625 : BitVec (32 : ℕ)), (403292932 : BitVec (32 : ℕ)), (102861840 : BitVec (32 : ℕ)), (1347294240 : BitVec (32 : ℕ)), (1617961282 : BitVec (32 : ℕ)), (2273325568 : BitVec (32 : ℕ)), (4160751752 : BitVec (32 : ℕ))], [(8372227 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (32849932 : BitVec (32 : ℕ)), (714129456 : BitVec (32 : ℕ)), (26198208 : BitVec (32 : ℕ)), (101352196 : BitVec (32 : ℕ)), (19074064 : BitVec (32 : ℕ)), (340530208 : BitVec (32 : ℕ)), (410001728 : BitVec (32 : ℕ)), (562049537 : BitVec (32 : ℕ)), (1040189578 : BitVec (32 : ℕ))], [(8372227 : BitVec (32 : ℕ)), (1292189708 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (1418772528 : BitVec (32 : ℕ)), (42631364 : BitVec (32 : ℕ)), (202359552 : BitVec (32 : ℕ)), (52628496 : BitVec (32 : ℕ)), (676074528 : BitVec (32 : ℕ)), (812654920 : BitVec (32 : ℕ)), (1132474881 : BitVec (32 : ℕ)), (2080376962 : BitVec (32 : ℕ))], [(16760835 : BitVec (32 : ℕ)), (353714188 : BitVec (32 : ℕ)), (63750192 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (36339908 : BitVec (32 : ℕ)), (70451984 : BitVec (32 : ℕ)), (54774784 : BitVec (32 : ℕ)), (213652480 : BitVec (32 : ℕ)), (146809160 : BitVec (32 : ℕ)), (318779905 : BitVec (32 : ℕ)), (469764258 : BitVec (32 : ℕ))]],   ∀ (x3 : List (BitVec (32 : ℕ))),     x3.length ≤ (18 : ℕ) →       (∀ (x5 : Fin x3.length),           have x6 : List (BitVec (32 : ℕ)) := x1 ++ List.take (↑x5) x3;           (∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) ∧ ∀ x7 ∈ x6, (x7 ^^^ (16383 : BitVec (32 : ℕ))) &&& (x3.get x5 ^^^ (16383 : BitVec (32 : ℕ))) ≠ x7 ^^^ (16383 : BitVec (32 : ℕ))) →         (16383 : BitVec (32 : ℕ)) ∉ x1 ++ x3) := by
  let gate := fun (w : Finset (BitVec 32)) (z : BitVec 32) => (∃ u ∈ w, ∃ v ∈ w, z = u &&& v ∨ z = u ||| v) ∧ ∀ u ∈ w, (u ^^^ 16383) &&& (z ^^^ 16383) ≠ u ^^^ 16383
  let ok := fun (w : Finset (BitVec 32)) (s : List (BitVec 32)) => ∀ l z r, s = l ++ z :: r → gate (w ∪ l.toFinset) z
  let sep := fun (w : Finset (BitVec 32)) => ∀ i j : Fin 32, i.val < 14 → 14 ≤ j.val → ∃ u ∈ w, u.getLsbD i.val = true ∧ u.getLsbD j.val = false
  have pref {w} {s t : List (BitVec 32)} (h : ok w (s ++ t)) : ok w s := by
    intro l z r he
    exact h l z (r ++ t) (by simp [he])
  have snoc {w} {s : List (BitVec 32)} {z} (hs : ok w s) (hz : gate (w ∪ s.toFinset) z) : ok w (s ++ [z]) := by
    intro l v r he
    cases r using List.reverseRecOn with
    | nil =>
      obtain ⟨rfl, heq⟩ := List.append_inj' he (by simp)
      cases heq
      exact hz
    | append_singleton r x =>
      have h : s ++ [z] = (l ++ v :: r) ++ [x] := by simpa using he
      have hh : s = l ++ v :: r := List.append_inj_left' h (by simp)
      exact hs l v r hh
  have slice (w : Finset (BitVec 32)) (s : List (BitVec 32)) (d : Finset (BitVec 32))
      (hs : ok w s) (hd : d ⊆ w ∪ s.toFinset) : ∃ f ⊆ w, ∃ t : List (BitVec 32),
      f.card ≤ d.card + t.length ∧ t.length ≤ s.length ∧ ok f t ∧ d ⊆ f ∪ t.toFinset ∧ t.toFinset ⊆ s.toFinset := by
    induction s using List.reverseRecOn generalizing d with
    | nil => exact ⟨d, by simpa using hd, [], by simp, by simp, by intro l z r h; simp at h, by simp, by simp⟩
    | append_singleton s z ih =>
      by_cases hz : z ∈ d
      · obtain ⟨⟨u, hu, v, hv, hg⟩, hdom⟩ := hs s z [] rfl
        let e := insert u (insert v (d.erase z))
        have he : e ⊆ w ∪ s.toFinset := by
          intro x hx
          simp only [e, Finset.mem_insert, Finset.mem_erase] at hx
          rcases hx with rfl | rfl | ⟨hne, hx⟩
          · exact hu
          · exact hv
          · simpa [hne] using hd hx
        obtain ⟨f, hf, t, hc, ht, hot, hed, hsub⟩ := ih e (pref hs) he
        have hgate : gate (f ∪ t.toFinset) z := ⟨⟨u, hed (by simp [e]), v, hed (by simp [e]), hg⟩, fun k hk => hdom k (Finset.union_subset_union hf hsub hk)⟩
        refine ⟨f, hf, t ++ [z], ?_, by simpa using ht, snoc hot hgate, ?_, by simpa only [List.toFinset_append] using Finset.union_subset_union hsub (Finset.Subset.refl [z].toFinset)⟩
        · have hcard := Finset.card_insert_le u (insert v (d.erase z))
          have hcard' := Finset.card_insert_le v (d.erase z)
          have hcard'' := Finset.card_erase_add_one hz
          dsimp [e] at hc
          simp only [List.length_append, List.length_singleton]; omega
        · intro x hx
          by_cases hxz : x = z
          · simp [hxz]
          · have h := hed (show x ∈ e by simp [e, hxz, hx])
            simpa [hxz] using h
      · have hd' : d ⊆ w ∪ s.toFinset := by
          intro x hx
          have hne : x ≠ z := fun h => hz (h ▸ hx)
          simpa [hne] using hd hx
        obtain ⟨f, hf, t, hc, ht, hot, hed, hsub⟩ := ih d (pref hs) hd'
        exact ⟨f, hf, t, hc, by simp; omega, hot, hed, by rw [List.toFinset_append]; exact hsub.trans Finset.subset_union_left⟩
  have separate (f : Finset (BitVec 32)) (t : List (BitVec 32)) (ht : ok f t)
      (hm : (16383 : BitVec 32) ∈ f ∪ t.toFinset) : sep f := by
    intro i j hi hj
    by_contra! bad
    have prop : ∀ x ∈ f ∪ t.toFinset, x.getLsbD i.val = true → x.getLsbD j.val = true := by
      clear hm
      induction t using List.reverseRecOn with
      | nil => simpa using bad
      | append_singleton l z ih =>
        have hold := ih (pref ht)
        obtain ⟨u, hu, v, hv, huv⟩ := (ht l z [] rfl).1
        intro x hx
        by_cases he : x = z
        · subst x
          have pu := hold u hu
          have pv := hold v hv
          rcases huv with rfl | rfl <;> simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
        · exact hold x (by simpa [he] using hx)
    have bits : ∀ k : Fin 32, (16383 : BitVec 32).getLsbD k.val = decide (k.val < 14) := by decide
    have hp := prop 16383 hm
    rw [bits i, bits j] at hp
    simp [hi, Nat.not_lt.mpr hj] at hp
  intro a ha s hs hsok hm
  have hall : ok a.toFinset s := by
    intro l z r he
    subst s
    have hh := hsok ⟨l.length, by simp⟩
    simpa [gate, List.get_eq_getElem, List.getElem_append_right] using hh
  let p := s.take 12
  let q := s.drop 12
  have hpq : p ++ q = s := List.take_append_drop ..
  have hpre : ok a.toFinset p := pref (hpq.symm ▸ hall)
  have htail : ok (a.toFinset ∪ p.toFinset) q := by
    intro l z r he
    have hh := hall (p ++ l) z r (by rw [← hpq, he, List.append_assoc])
    simpa [Finset.union_assoc] using hh
  have hneed : {(16383 : BitVec 32)} ⊆ (a.toFinset ∪ p.toFinset) ∪ q.toFinset := by
    simpa [← hpq, or_assoc] using hm
  obtain ⟨f, hf, t, hc, ht, hok, hlast, _⟩ := slice _ q _ htail hneed
  have ht6 : t.length ≤ 6 := by simp [q] at ht; omega
  have hf7 : f.card ≤ 7 := by simp at hc; omega
  have hm' : (16383 : BitVec 32) ∈ f ∪ t.toFinset := hlast (by simp)
  have hsep := separate _ _ hok hm'
  have hp12 : p.length ≤ 12 := by simp [p]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h0 p hp12 hpre f hf hf7 hsep t ht6 hok hm'
  · exact h1 p hp12 hpre f hf hf7 hsep t ht6 hok hm'
  · exact h2 p hp12 hpre f hf hf7 hsep t ht6 hok hm'
  · exact h3 p hp12 hpre f hf hf7 hsep t ht6 hok hm'
