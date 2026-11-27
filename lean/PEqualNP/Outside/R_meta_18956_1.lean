import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18956_1
    (hInter : let B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let T : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}; ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 61 → L.Nodup → (∀ s ∈ L, s ∉ B) → T ∉ L → (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s → ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) → ∀ a ∈ L, ∀ b ∈ L, a ≠ b → T ⊆ a → a ≠ T → T ⊆ b → b ≠ T → a ∩ b ≠ T)
    (hUnion : let B : Set (Set (Fin 26 → Bool)) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let V : Set (Set (Fin 26 → Bool)) := Set.range fun i : Fin 26 => {x : Fin 26 → Bool | x i = true}; let T : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}; ∀ L : List (Set (Fin 26 → Bool)), L.length ≤ 61 → L.Nodup → (∀ s ∈ L, s ∉ B) → T ∉ L → (∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s → ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) → ∀ a, (a ∈ V ∨ a ∈ L) → ∀ b, (b ∈ V ∨ b ∈ L) → a ≠ b → a ⊆ T → a ≠ T → b ⊆ T → b ≠ T → a ∪ b ≠ T) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → (∀ (x7 : ℕ) (x8 : Set (Fin (26 : ℕ) → Bool)), x3[x7]? = Option.some x8 → ∃ (x10 : Set (Fin (26 : ℕ) → Bool)), (x10 ∈ x1 ∨ x10 ∈ List.take x7 x3) ∧ ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x7 x3) ∧ (x8 = x10 ∩ x11 ∨ x8 = x10 ∪ x11)) → x2 ∉ x3) := by
  intro x1 x2 x3 hlen hnd hnotB hstep hmem
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
  have hT_not_B : x2 ∉ x1 := by
    intro hm
    simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hm
    rcases hm with (h0 | hu) | ⟨i, hi⟩
    · have hc : y0 ∈ (∅ : Set (Fin 26 → Bool)) := h0 ▸ hy0
      simp at hc
    · let yz : Fin 26 → Bool := fun _ => false
      have hc : yz ∈ x2 := hu ▸ Set.mem_univ yz
      dsimp only [x2] at hc
      rcases hc with ⟨_, _, _, h1, _⟩
      simp [yz] at h1
    · exact hT_not_sub_var i (by rw [← hi])
  obtain ⟨m, hm_eq⟩ := List.mem_iff_getElem?.mp hmem
  have hm_lt : m < x3.length := by
    by_contra hge
    have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
    rw [hm_eq] at hnone
    simp at hnone
  let L : List (Set (Fin 26 → Bool)) := x3.take m
  have hL_len_eq : L.length = m := by
    simp only [L, List.length_take]
    omega
  have hL_len : L.length ≤ 61 := by omega
  have hL_nd : L.Nodup := hnd.sublist (List.take_sublist m x3)
  have hL_notB : ∀ s ∈ L, s ∉ x1 := fun s hs => hnotB s (List.mem_of_mem_take hs)
  have hT_notL : x2 ∉ L := by
    intro hxL
    obtain ⟨j, hj_eq⟩ := List.mem_iff_getElem?.mp hxL
    have hj_lt : j < L.length := by
      by_contra hge
      have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hj_eq] at hnone
      simp at hnone
    have hj_m : j < m := by omega
    have hj_lt3 : j < x3.length := by omega
    have hj_x3 : x3[j]? = some x2 := by
      have hcat := List.take_append_drop m x3
      rw [← hcat, List.getElem?_append_left (by rw [List.length_take]; omega)]
      simpa [L] using hj_eq
    have hxj : x3[j]'hj_lt3 = x2 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem hj_lt3, hj_x3]
    have hxm : x3[m]'hm_lt = x2 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem hm_lt, hm_eq]
    have heq := (List.Nodup.getElem_inj_iff hnd).mp (hxj.trans hxm.symm)
    omega
  have hL_step : ∀ (i : ℕ) (s : Set (Fin 26 → Bool)), L[i]? = some s →
      ∃ a, (a ∈ x1 ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ x1 ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b) := by
    intro i s hi_eq
    have hi_lt : i < L.length := by
      by_contra hge
      have hnone := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hi_eq] at hnone
      simp at hnone
    have hi_x3 : x3[i]? = some s := by
      have hcat := List.take_append_drop m x3
      rw [← hcat, List.getElem?_append_left (by rw [List.length_take]; omega)]
      simpa [L] using hi_eq
    have htk : L.take i = x3.take i := by
      simp only [L, List.take_take]
      congr 1
      omega
    rw [htk]
    exact hstep i s hi_x3
  obtain ⟨a, ha, b, hb, hop⟩ := hstep m x2 hm_eq
  have ha_ne_T : a ≠ x2 := by
    rintro rfl
    rcases ha with haB | haL
    · exact hT_not_B haB
    · exact hT_notL haL
  have hb_ne_T : b ≠ x2 := by
    rintro rfl
    rcases hb with hbB | hbL
    · exact hT_not_B hbB
    · exact hT_notL hbL
  rcases hop with hInt | hUni
  · have hab : a ≠ b := by
      rintro rfl
      rw [Set.inter_self] at hInt
      exact ha_ne_T hInt.symm
    have hTa : x2 ⊆ a := by rw [hInt]; exact Set.inter_subset_left
    have hTb : x2 ⊆ b := by rw [hInt]; exact Set.inter_subset_right
    have haL : a ∈ L := by
      rcases ha with haB | haL
      · exfalso
        simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at haB
        rcases haB with (ha0 | haU) | ⟨i, hai⟩
        · rw [ha0] at hInt
          have hc : y0 ∈ (∅ ∩ b : Set (Fin 26 → Bool)) := hInt ▸ hy0
          simp at hc
        · rw [haU, Set.univ_inter] at hInt
          exact hb_ne_T hInt.symm
        · rw [← hai] at hTa
          exact hT_not_sub_var i hTa
      · exact haL
    have hbL : b ∈ L := by
      rcases hb with hbB | hbL
      · exfalso
        simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hbB
        rcases hbB with (hb0 | hbU) | ⟨i, hbi⟩
        · rw [hb0] at hInt
          have hc : y0 ∈ (a ∩ ∅ : Set (Fin 26 → Bool)) := hInt ▸ hy0
          simp at hc
        · rw [hbU, Set.inter_univ] at hInt
          exact ha_ne_T hInt.symm
        · rw [← hbi] at hTb
          exact hT_not_sub_var i hTb
      · exact hbL
    exact hInter L hL_len hL_nd hL_notB hT_notL hL_step a haL b hbL hab hTa ha_ne_T hTb hb_ne_T hInt.symm
  · have hab : a ≠ b := by
      rintro rfl
      rw [Set.union_self] at hUni
      exact ha_ne_T hUni.symm
    have haTsub : a ⊆ x2 := by rw [hUni]; exact Set.subset_union_left
    have hbTsub : b ⊆ x2 := by rw [hUni]; exact Set.subset_union_right
    have haV : a ∈ Set.range (fun i : Fin 26 => {z : Fin 26 → Bool | z i = true}) ∨ a ∈ L := by
      rcases ha with haB | haL
      · left
        simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at haB
        rcases haB with (ha0 | haU) | ⟨i, hai⟩
        · rw [ha0, Set.empty_union] at hUni
          exact absurd hUni.symm hb_ne_T
        · rw [haU, Set.univ_union] at hUni
          exact absurd (by rw [hUni]; dsimp only [x1]; simp) hT_not_B
        · exact ⟨i, hai⟩
      · exact Or.inr haL
    have hbV : b ∈ Set.range (fun i : Fin 26 => {z : Fin 26 → Bool | z i = true}) ∨ b ∈ L := by
      rcases hb with hbB | hbL
      · left
        simp only [x1, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hbB
        rcases hbB with (hb0 | hbU) | ⟨i, hbi⟩
        · rw [hb0, Set.union_empty] at hUni
          exact absurd hUni.symm ha_ne_T
        · rw [hbU, Set.union_univ] at hUni
          exact absurd (by rw [hUni]; dsimp only [x1]; simp) hT_not_B
        · exact ⟨i, hbi⟩
      · exact Or.inr hbL
    exact hUnion L hL_len hL_nd hL_notB hT_notL hL_step a haV b hbV hab haTsub ha_ne_T hbTsub hb_ne_T hUni.symm
