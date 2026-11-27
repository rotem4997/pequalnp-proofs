import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4387_1
    (hlastAnd : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))];
      ∀ (x2 : List (BitVec (58 : ℕ))),
        x2.length ≤ (24 : ℕ) →
        (∀ (x4 : Fin x2.length),
          have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take x4.val x2;
          x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, x6 ≠ x7 ∧ (x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7)) →
        ¬∃ x6 ∈ x1 ++ x2, ∃ x7 ∈ x1 ++ x2, x6 ≠ x7 ∧ x6 &&& x7 = (2097151 : BitVec (58 : ℕ)))
    (hlastOr : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))];
      ∀ (x2 : List (BitVec (58 : ℕ))),
        x2.length ≤ (24 : ℕ) →
        (∀ (x4 : Fin x2.length),
          have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take x4.val x2;
          x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, x6 ≠ x7 ∧ (x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7)) →
        ¬∃ x6 ∈ x1 ++ x2, ∃ x7 ∈ x1 ++ x2, x6 ≠ x7 ∧ x6 ||| x7 = (2097151 : BitVec (58 : ℕ))) :
    have x1 : List (BitVec (58 : ℕ)) := [(0 : BitVec (58 : ℕ)), BitVec.allOnes (58 : ℕ), (95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ)), (95274182876594239 : BitVec (58 : ℕ))]; ∀ (x2 : List (BitVec (58 : ℕ))),   x2.length ≤ (25 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List (BitVec (58 : ℕ)) := x1 ++ List.take (↑x4) x2;         ∃ x6 ∈ x5, ∃ x7 ∈ x5, x2.get x4 = x6 &&& x7 ∨ x2.get x4 = x6 ||| x7) →       (2097151 : BitVec (58 : ℕ)) ∉ x1 ++ x2 := by
  classical
  dsimp only
  let x1' : List (BitVec 58) :=
    [(95229015649943559 : BitVec 58), (63038587666488 : BitVec 58),
     (256462815680 : BitVec 58), (4292497062759936 : BitVec 58),
     (8521481482240 : BitVec 58), (14003410187812864 : BitVec 58),
     (55389823207997440 : BitVec 58), (189297016294081033 : BitVec 58),
     (155696362464477250 : BitVec 58), (218994303132270608 : BitVec 58),
     (183565875465490436 : BitVec 58), (229736628138025984 : BitVec 58),
     (270286071508633728 : BitVec 58), (288160007407550752 : BitVec 58),
     (95274182876594239 : BitVec 58)]
  let x1 : List (BitVec 58) := (0 : BitVec 58) :: BitVec.allOnes 58 :: x1'
  let Good : List (BitVec 58) → Prop := fun l =>
    (∀ i : Fin l.length,
      ∃ a ∈ x1 ++ l.take i.val, ∃ b ∈ x1 ++ l.take i.val,
        l.get i = a &&& b ∨ l.get i = a ||| b) ∧
    (2097151 : BitVec 58) ∈ x1 ++ l
  intro x2 hlen2 hvalid hmem2
  have hex : ∃ k : ℕ, ∃ l : List (BitVec 58), l.length = k ∧ Good l :=
    ⟨x2.length, x2, rfl, hvalid, hmem2⟩
  rcases Nat.find_spec hex with ⟨l, hllen, hlvalid, hlmem⟩
  have hle25 : l.length ≤ 25 := by
    have hmin : l.length ≤ x2.length := by
      rw [hllen]
      exact Nat.find_min' hex ⟨x2, rfl, hvalid, hmem2⟩
    omega
  have hlmin : ∀ l' : List (BitVec 58), Good l' → l.length ≤ l'.length := by
    intro l' h'
    rw [hllen]
    exact Nat.find_min' hex ⟨l', rfl, h'⟩
  have hnotx1 : (2097151 : BitVec 58) ∉ x1 := by decide
  have hlmem_l : (2097151 : BitVec 58) ∈ l := by
    rcases List.mem_append.mp hlmem with h | h
    · exact absurd h hnotx1
    · exact h
  have hpos : 0 < l.length := List.length_pos_of_mem hlmem_l
  have hnodup : ∀ i : Fin l.length, l.get i ∉ x1 ++ l.take i.val := by
    intro i hdup
    let l' : List (BitVec 58) := l.take i.val ++ l.drop (i.val + 1)
    have hl'len : l'.length = l.length - 1 := by
      simp only [l', List.length_append, List.length_take, List.length_drop]
      omega
    have hsplit_l : l = l.take i.val ++ [l.get i] ++ l.drop (i.val + 1) := by
      have h1 : l.drop i.val = l.get i :: l.drop (i.val + 1) := by
        rw [List.get_eq_getElem]
        exact List.drop_eq_getElem_cons i.isLt
      calc l = l.take i.val ++ l.drop i.val := (List.take_append_drop i.val l).symm
        _ = l.take i.val ++ (l.get i :: l.drop (i.val + 1)) := by rw [h1]
        _ = l.take i.val ++ [l.get i] ++ l.drop (i.val + 1) := by simp [List.append_assoc]
    have hgood' : Good l' := by
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hj : j.val < i.val
        · have hj_l : j.val < l.length := by omega
          have hget : l'.get j = l.get ⟨j.val, hj_l⟩ := by
            rw [List.get_eq_getElem, List.get_eq_getElem]
            have hlt_take : j.val < (l.take i.val).length := by rw [List.length_take]; omega
            simp only [l', List.getElem_append_left hlt_take, List.getElem_take]
          have htake : l'.take j.val = l.take j.val := by
            have hle_take : j.val ≤ (l.take i.val).length := by rw [List.length_take]; omega
            simp only [l', List.take_append_of_le_length hle_take, List.take_take, Nat.min_eq_left (by omega : j.val ≤ i.val)]
          rw [hget, htake]
          exact hlvalid ⟨j.val, hj_l⟩
        · have hj_l : j.val + 1 < l.length := by omega
          have hget : l'.get j = l.get ⟨j.val + 1, hj_l⟩ := by
            rw [List.get_eq_getElem, List.get_eq_getElem]
            have hlen_take : (l.take i.val).length = i.val := List.length_take_of_le (by omega)
            have hge_take : (l.take i.val).length ≤ j.val := by omega
            simp only [l', List.getElem_append_right hge_take, hlen_take, List.getElem_drop]
            congr 1; omega
          have hsub : ∀ u, u ∈ x1 ++ l.take (j.val + 1) → u ∈ x1 ++ l'.take j.val := by
            intro u hu
            have hlt_take : (l.take i.val).length = i.val := List.length_take_of_le (by omega)
            have htake' : l'.take j.val = l.take i.val ++ (l.drop (i.val + 1)).take (j.val - i.val) := by
              simp only [l', List.take_append, hlt_take,
                List.take_of_length_le (by rw [hlt_take]; omega : (l.take i.val).length ≤ j.val)]
            have htake_orig : l.take (j.val + 1) =
                l.take i.val ++ [l.get i] ++ (l.drop (i.val + 1)).take (j.val - i.val) := by
              conv_lhs => rw [hsplit_l]
              have hlen_p : (l.take i.val ++ [l.get i]).length = i.val + 1 := by
                simp only [List.length_append, hlt_take, List.length_cons, List.length_nil]
              rw [List.take_append, hlen_p, List.take_of_length_le (by rw [hlen_p]; omega)]
              congr 2; omega
            rw [htake_orig] at hu
            rw [htake']
            rcases List.mem_append.mp hu with hx | hrest
            · exact List.mem_append.mpr (Or.inl hx)
            · rcases List.mem_append.mp hrest with hpre | htail
              · rcases List.mem_append.mp hpre with hpre1 | hmid
                · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hpre1)))
                · have hueq : u = l.get i := List.mem_singleton.mp hmid
                  rw [hueq]
                  rcases List.mem_append.mp hdup with hx | hpre1
                  · exact List.mem_append.mpr (Or.inl hx)
                  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hpre1)))
              · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr htail)))
          rcases hlvalid ⟨j.val + 1, hj_l⟩ with ⟨a, ha, b, hb, hab⟩
          rw [hget]
          exact ⟨a, hsub a ha, b, hsub b hb, hab⟩
      · have hmem_split : (2097151 : BitVec 58) ∈ l.take i.val ++ [l.get i] ++ l.drop (i.val + 1) := by
          rw [← hsplit_l]; exact hlmem_l
        rcases List.mem_append.mp hmem_split with hpre | hdrop
        · rcases List.mem_append.mp hpre with htake | hmid
          · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl htake)))
          · have heq : (2097151 : BitVec 58) = l.get i := List.mem_singleton.mp hmid
            rw [heq]
            rcases List.mem_append.mp hdup with hx | htake
            · exact List.mem_append.mpr (Or.inl hx)
            · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl htake)))
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hdrop)))
    have hle := hlmin l' hgood'
    omega
  have hclean : ∀ i : Fin l.length,
      l.get i ∉ x1' ++ l.take i.val ∧
      ∃ a ∈ x1' ++ l.take i.val, ∃ b ∈ x1' ++ l.take i.val,
        a ≠ b ∧ (l.get i = a &&& b ∨ l.get i = a ||| b) := by
    intro i
    have hnd := hnodup i
    have hnd' : l.get i ∉ x1' ++ l.take i.val := by
      intro hmem
      apply hnd
      rcases List.mem_append.mp hmem with h1 | h2
      · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)))
      · exact List.mem_append.mpr (Or.inr h2)
    refine ⟨hnd', ?_⟩
    rcases hlvalid i with ⟨a, ha, b, hb, hab⟩
    have h0_mem : (0 : BitVec 58) ∈ x1 ++ l.take i.val :=
      List.mem_append.mpr (Or.inl (List.mem_cons_self ..))
    have h1_mem : BitVec.allOnes 58 ∈ x1 ++ l.take i.val :=
      List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rcases hab with h | h
      · rw [show (0 : BitVec 58) &&& b = 0 by simp] at h; rw [h] at hnd; exact hnd h0_mem
      · rw [show (0 : BitVec 58) ||| b = b by simp] at h; rw [h] at hnd; exact hnd hb
    have ha1 : a ≠ BitVec.allOnes 58 := by
      rintro rfl
      rcases hab with h | h <;> simp only [BitVec.allOnes_and, BitVec.allOnes_or] at h <;> rw [h] at hnd <;> exact hnd (by assumption)
    have hb0 : b ≠ 0 := by
      rintro rfl
      rcases hab with h | h
      · rw [show a &&& (0 : BitVec 58) = 0 by simp] at h; rw [h] at hnd; exact hnd h0_mem
      · rw [show a ||| (0 : BitVec 58) = a by simp] at h; rw [h] at hnd; exact hnd ha
    have hb1 : b ≠ BitVec.allOnes 58 := by
      rintro rfl
      rcases hab with h | h <;> simp only [BitVec.and_allOnes, BitVec.or_allOnes] at h <;> rw [h] at hnd <;> exact hnd (by assumption)
    have hne_ab : a ≠ b := by
      rintro rfl
      rcases hab with h | h <;> simp only [BitVec.and_self, BitVec.or_self] at h <;> rw [h] at hnd <;> exact hnd ha
    have hstrip : ∀ u, u ∈ x1 ++ l.take i.val → u ≠ 0 → u ≠ BitVec.allOnes 58 → u ∈ x1' ++ l.take i.val := by
      intro u hu hu0 hu1
      rcases List.mem_append.mp hu with hx | ht
      · simp only [x1, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx'
        · exact absurd rfl hu0
        · exact absurd rfl hu1
        · exact List.mem_append.mpr (Or.inl hx')
      · exact List.mem_append.mpr (Or.inr ht)
    exact ⟨a, hstrip a ha ha0 ha1, b, hstrip b hb hb0 hb1, hne_ab, hab⟩
  have hlast : l.get ⟨l.length - 1, by omega⟩ = (2097151 : BitVec 58) := by
    rcases List.mem_iff_get.mp hlmem_l with ⟨i, hi⟩
    have hieq : i.val = l.length - 1 := by
      by_contra hneq
      have hlt : i.val + 1 < l.length := by omega
      let l' : List (BitVec 58) := l.take (i.val + 1)
      have hl'len : l'.length = i.val + 1 := List.length_take_of_le (by omega)
      have hgood' : Good l' := by
        refine ⟨?_, ?_⟩
        · intro j
          have hj_l : j.val < l.length := by omega
          have hget : l'.get j = l.get ⟨j.val, hj_l⟩ := by
            rw [List.get_eq_getElem, List.get_eq_getElem]
            exact List.getElem_take
          have htake : l'.take j.val = l.take j.val := by
            simp only [l', List.take_take, Nat.min_eq_left (by omega : j.val ≤ i.val + 1)]
          rw [hget, htake]
          exact hlvalid ⟨j.val, hj_l⟩
        · apply List.mem_append.mpr; right
          rw [← hi]
          have hget : l'.get ⟨i.val, by omega⟩ = l.get i := by
            rw [List.get_eq_getElem, List.get_eq_getElem]
            exact List.getElem_take
          rw [← hget]
          exact List.get_mem l' ⟨i.val, by omega⟩
      have hle := hlmin l' hgood'
      omega
    have hfin : i = ⟨l.length - 1, by omega⟩ := Fin.ext hieq
    rw [← hfin]
    exact hi
  let init : List (BitVec 58) := l.take (l.length - 1)
  have hinit_len : init.length ≤ 24 := by
    rw [List.length_take_of_le (by omega)]
    omega
  have hinit_valid : ∀ j : Fin init.length,
      have x5 : List (BitVec 58) := x1' ++ List.take j.val init;
      init.get j ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, x6 ≠ x7 ∧ (init.get j = x6 &&& x7 ∨ init.get j = x6 ||| x7) := by
    intro j
    dsimp only
    have hilen : init.length = l.length - 1 := List.length_take_of_le (by omega)
    have hj_lt : j.val < l.length - 1 := by
      have := j.isLt
      omega
    have hj_l : j.val < l.length := by omega
    have hget : init.get j = l.get ⟨j.val, hj_l⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      exact List.getElem_take
    have htake : List.take j.val init = l.take j.val := by
      simp only [init, List.take_take, Nat.min_eq_left (by omega : j.val ≤ l.length - 1)]
    rw [hget, htake]
    exact hclean ⟨j.val, hj_l⟩
  rcases (hclean ⟨l.length - 1, by omega⟩).2 with ⟨a, ha, b, hb, hne, hab⟩
  rw [hlast] at hab
  rcases hab with hand | hor
  · exact hlastAnd init hinit_len hinit_valid ⟨a, ha, b, hb, hne, hand.symm⟩
  · exact hlastOr init hinit_len hinit_valid ⟨a, ha, b, hb, hne, hor.symm⟩
