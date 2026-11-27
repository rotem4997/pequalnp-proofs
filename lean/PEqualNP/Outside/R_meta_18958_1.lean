import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18958_1
    (hTopInter : let B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let T : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}; ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 61 → L.Nodup → (∀ s ∈ L, s ∉ B) → T ∉ L → (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s → ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) → ∀ a ∈ L, ∀ u ∈ L, ∀ v ∈ L, u ≠ v → T ⊆ a → a ≠ T → T ⊆ u → u ≠ T → T ⊆ v → v ≠ T → u ∩ v ∉ B → u ∩ v ∉ L → u ∩ v ≠ T → a ∩ (u ∩ v) ≠ T)
    (hTopUnion : let B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let V : Set (Set (Fin 26 → Bool)) := Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let T : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}; ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 61 → L.Nodup → (∀ s ∈ L, s ∉ B) → T ∉ L → (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s → ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) → ∀ a ∈ L, ∀ u, (u ∈ V ∨ u ∈ L) → ∀ v, (v ∈ V ∨ v ∈ L) → u ≠ v → T ⊆ a → a ≠ T → T ⊆ u ∪ v → u ∪ v ∉ B → u ∪ v ∉ L → u ∪ v ≠ T → a ∩ (u ∪ v) ≠ T) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → x2 ∉ x3 → (∀ (x8 : ℕ) (x9 : Set (Fin (26 : ℕ) → Bool)), x3[x8]? = Option.some x9 → ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x8 x3) ∧ ∃ (x12 : Set (Fin (26 : ℕ) → Bool)), (x12 ∈ x1 ∨ x12 ∈ List.take x8 x3) ∧ (x9 = x11 ∩ x12 ∨ x9 = x11 ∪ x12)) → ∀ x9 ∈ x3, ∀ x11 ∈ x3, x9 ≠ x11 → x2 ⊆ x9 → x9 ≠ x2 → x2 ⊆ x11 → x11 ≠ x2 → x9 ∩ x11 ≠ x2) := by
  intro x1 x2 x3 hlen hnd hnotB hnotT hstep x9 hx9 x11 hx11 h911 h9sub h9ne h11sub h11ne hInt
  let y0 : Fin 26 → Bool := fun z => decide (z.val = 0 ∨ z.val = 13)
  let y1 : Fin 26 → Bool := fun z => decide (z.val = 1 ∨ z.val = 15)
  have hy0 : y0 ∈ x2 := by
    dsimp only [x2, y0]
    exact ⟨(0 : Fin 13), (0 : Fin 13), by decide, by decide, by decide⟩
  have hy1 : y1 ∈ x2 := by
    dsimp only [x2, y1]
    exact ⟨(1 : Fin 13), (2 : Fin 13), by decide, by decide, by decide⟩
  have hDisjY : ∀ i : Fin 26, y0 i = true → y1 i = true → False := by
    dsimp only [y0, y1]
    decide
  have hT_not_sub_var : ∀ i : Fin 26, ¬ (x2 ⊆ {z : Fin 26 → Bool | z i = true}) := by
    intro i hsub
    exact hDisjY i (hsub hy0) (hsub hy1)
  have hWlog : ∀ i j (hi : i < x3.length) (hj : j < x3.length),
      i < j → x2 ⊆ x3[i]'hi → x3[i]'hi ≠ x2 → x2 ⊆ x3[j]'hj → x3[j]'hj ≠ x2 →
      x3[i]'hi ∩ x3[j]'hj ≠ x2 := by
    intro i j hi hj hij hisub hine hjsub hjne
    let L : List (Set (Fin 26 → Bool)) := x3.take j
    have hL_len_eq : L.length = j := by
      simp only [L, List.length_take]
      omega
    have hL_len : L.length ≤ 61 := by omega
    have hL_nd : L.Nodup := hnd.sublist (List.take_sublist j x3)
    have hL_notB : ∀ s ∈ L, s ∉ x1 := fun s hs => hnotB s (List.mem_of_mem_take hs)
    have hT_notL : x2 ∉ L := fun hm => hnotT (List.mem_of_mem_take hm)
    have hL_step : ∀ (m : ℕ) (s : Set (Fin 26 → Bool)), L[m]? = some s →
        ∃ a, (a ∈ x1 ∨ a ∈ L.take m) ∧ ∃ b, (b ∈ x1 ∨ b ∈ L.take m) ∧ (s = a ∩ b ∨ s = a ∪ b) := by
      intro m s hm_eq
      have hm_lt : m < L.length := by
        by_contra hge
        have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
        rw [hm_eq] at hnone
        simp at hnone
      have hm_x3 : x3[m]? = some s := by
        have hcat := List.take_append_drop j x3
        rw [← hcat, List.getElem?_append_left (by rw [List.length_take]; omega)]
        simpa [L] using hm_eq
      have htk : L.take m = x3.take m := by
        simp only [L, List.take_take]
        congr 1
        omega
      rw [htk]
      exact hstep m s hm_x3
    have haL : x3[i]'hi ∈ L := by
      refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
      have hcat := List.take_append_drop j x3
      have hxi : x3[i]? = some (x3[i]'hi) := List.getElem?_eq_getElem hi
      conv at hxi => lhs; rw [← hcat, List.getElem?_append_left (by rw [List.length_take]; omega)]
      exact hxi
    have hxj_notB : x3[j]'hj ∉ x1 := hnotB (x3[j]'hj) (List.getElem_mem hj)
    have hxj_notL : x3[j]'hj ∉ L := by
      intro hxL
      obtain ⟨m, hm_eq⟩ := List.mem_iff_getElem?.mp hxL
      have hm_lt : m < L.length := by
        by_contra hge
        have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
        rw [hm_eq] at hnone
        simp at hnone
      have hm_lt3 : m < x3.length := by omega
      have hm_x3 : x3[m]? = some (x3[j]'hj) := by
        have hcat := List.take_append_drop j x3
        conv_lhs => rw [← hcat, List.getElem?_append_left (by rw [List.length_take]; omega)]
        exact hm_eq
      have hxm : x3[m]'hm_lt3 = x3[j]'hj := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem hm_lt3, hm_x3]
      have heq := (List.Nodup.getElem_inj_iff hnd).mp hxm
      omega
    have hxj_step : ∃ u, (u ∈ x1 ∨ u ∈ L) ∧ ∃ v, (v ∈ x1 ∨ v ∈ L) ∧ (x3[j]'hj = u ∩ v ∨ x3[j]'hj = u ∪ v) := by
      change ∃ u, (u ∈ x1 ∨ u ∈ x3.take j) ∧ ∃ v, (v ∈ x1 ∨ v ∈ x3.take j) ∧ _
      exact hstep j (x3[j]'hj) (List.getElem?_eq_getElem hj)
    obtain ⟨u, hu, v, hv, hop⟩ := hxj_step
    have huv : u ≠ v := by
      rintro rfl
      rcases hop with hEq | hEq
      · rw [Set.inter_self] at hEq
        rcases hu with huB | huL
        · exact hxj_notB (hEq ▸ huB)
        · exact hxj_notL (hEq ▸ huL)
      · rw [Set.union_self] at hEq
        rcases hu with huB | huL
        · exact hxj_notB (hEq ▸ huB)
        · exact hxj_notL (hEq ▸ huL)
    have hu_ne_j : u ≠ x3[j]'hj := by
      rintro rfl
      rcases hu with huB | huL
      · exact hxj_notB huB
      · exact hxj_notL huL
    have hv_ne_j : v ≠ x3[j]'hj := by
      rintro rfl
      rcases hv with hvB | hvL
      · exact hxj_notB hvB
      · exact hxj_notL hvL
    rcases hop with hEq | hEq
    · have hTu : x2 ⊆ u := Set.Subset.trans hjsub (by rw [hEq]; exact Set.inter_subset_left)
      have hTv : x2 ⊆ v := Set.Subset.trans hjsub (by rw [hEq]; exact Set.inter_subset_right)
      have huL : u ∈ L := by
        rcases hu with huB | huL
        · exfalso
          simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at huB
          rcases huB with (hu0 | huU) | ⟨r, hur⟩
          · rw [hu0] at hEq
            have hc : y0 ∈ (∅ ∩ v : Set (Fin 26 → Bool)) := hEq ▸ (hjsub hy0)
            simp at hc
          · rw [huU, Set.univ_inter] at hEq
            exact hv_ne_j hEq.symm
          · rw [← hur] at hTu
            exact hT_not_sub_var r hTu
        · exact huL
      have hvL : v ∈ L := by
        rcases hv with hvB | hvL
        · exfalso
          simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hvB
          rcases hvB with (hv0 | hvU) | ⟨r, hvr⟩
          · rw [hv0] at hEq
            have hc : y0 ∈ (u ∩ ∅ : Set (Fin 26 → Bool)) := hEq ▸ (hjsub hy0)
            simp at hc
          · rw [hvU, Set.inter_univ] at hEq
            exact hu_ne_j hEq.symm
          · rw [← hvr] at hTv
            exact hT_not_sub_var r hTv
        · exact hvL
      have huT : u ≠ x2 := fun heq => hT_notL (heq ▸ huL)
      have hvT : v ≠ x2 := fun heq => hT_notL (heq ▸ hvL)
      rw [hEq]
      exact hTopInter L hL_len hL_nd hL_notB hT_notL hL_step (x3[i]'hi) haL u huL v hvL huv
        hisub hine hTu huT hTv hvT
        (by rw [← hEq]; exact hxj_notB) (by rw [← hEq]; exact hxj_notL) (by rw [← hEq]; exact hjne)
    · have huV : u ∈ Set.range (fun r : Fin 26 => {z : Fin 26 → Bool | z r = true}) ∨ u ∈ L := by
        rcases hu with huB | huL
        · left
          simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at huB
          rcases huB with (hu0 | huU) | ⟨r, hur⟩
          · rw [hu0, Set.empty_union] at hEq
            exact absurd hEq.symm hv_ne_j
          · rw [huU, Set.univ_union] at hEq
            exact absurd (by rw [hEq]; dsimp only [x1]; simp) hxj_notB
          · exact ⟨r, hur⟩
        · exact Or.inr huL
      have hvV : v ∈ Set.range (fun r : Fin 26 => {z : Fin 26 → Bool | z r = true}) ∨ v ∈ L := by
        rcases hv with hvB | hvL
        · left
          simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hvB
          rcases hvB with (hv0 | hvU) | ⟨r, hvr⟩
          · rw [hv0, Set.union_empty] at hEq
            exact absurd hEq.symm hu_ne_j
          · rw [hvU, Set.union_univ] at hEq
            exact absurd (by rw [hEq]; dsimp only [x1]; simp) hxj_notB
          · exact ⟨r, hvr⟩
        · exact Or.inr hvL
      rw [hEq]
      exact hTopUnion L hL_len hL_nd hL_notB hT_notL hL_step (x3[i]'hi) haL u huV v hvV huv
        hisub hine
        (by rw [← hEq]; exact hjsub) (by rw [← hEq]; exact hxj_notB)
        (by rw [← hEq]; exact hxj_notL) (by rw [← hEq]; exact hjne)
  obtain ⟨i1, hi1_eq⟩ := List.mem_iff_getElem?.mp hx9
  obtain ⟨i2, hi2_eq⟩ := List.mem_iff_getElem?.mp hx11
  have hi1_lt : i1 < x3.length := by
    by_contra hge
    have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
    rw [hi1_eq] at hnone
    simp at hnone
  have hi2_lt : i2 < x3.length := by
    by_contra hge
    have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
    rw [hi2_eq] at hnone
    simp at hnone
  have hx1_val : x3[i1]'hi1_lt = x9 := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hi1_lt, hi1_eq]
  have hx2_val : x3[i2]'hi2_lt = x11 := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hi2_lt, hi2_eq]
  have hi_ne : i1 ≠ i2 := by
    intro heq
    subst heq
    exact h911 (hx1_val.symm.trans hx2_val)
  rcases Nat.lt_or_gt_of_ne hi_ne with h12 | h21
  · have := hWlog i1 i2 hi1_lt hi2_lt h12
      (by rw [hx1_val]; exact h9sub) (by rw [hx1_val]; exact h9ne)
      (by rw [hx2_val]; exact h11sub) (by rw [hx2_val]; exact h11ne)
    rw [hx1_val, hx2_val] at this
    exact this hInt
  · have := hWlog i2 i1 hi2_lt hi1_lt h21
      (by rw [hx2_val]; exact h11sub) (by rw [hx2_val]; exact h11ne)
      (by rw [hx1_val]; exact h9sub) (by rw [hx1_val]; exact h9ne)
    rw [hx2_val, hx1_val, Set.inter_comm] at this
    exact this hInt
