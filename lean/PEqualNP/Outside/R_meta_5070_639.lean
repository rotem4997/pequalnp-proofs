import Mathlib

-- Keep only the first nonempty occurrence of each set value.
-- A retained gate combines incomparable values and preserves the earlier operands.
-- Follow each uncovered pair to a sound intersection with two unsound operands.
-- A pure rectangle at that gate would also cover the original pair.
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_5070_639
    (normalize :
      ∀ (X : Type) (m s o : ℕ) (W : ℕ → Set X),
          o < m + s → W o ≠ ∅ →
          (∀ i < s, ∃ a b, max a b < m + i ∧
            W (m + i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
          ∃ T : List ℕ, T.length ≤ s ∧ (∀ i ∈ T, m ≤ i ∧ i < m + s) ∧ W o ∈ ((List.range m ++ T).map W) ∧
            ∀ j : Fin T.length,
              let pool := List.range m ++ T.take j.val
              let z := W (T.get j)
              (∀ w ∈ pool, w < T.get j) ∧ z ≠ ∅ ∧ z ∉ pool.map W ∧
              ∃ a ∈ pool.map W, ∃ b ∈ pool.map W, ¬ a ⊆ b ∧ ¬ b ⊆ a ∧ (z = a ∪ b ∨ z = a ∩ b))
    (frontier :
          ∀ (X : Type) (src T : List (Set X)) (out : Set X),
            let prev := fun i => src ++ T.take i
            out ∈ src ++ T →
            (∀ a ∈ src, ¬ a ⊆ out) →
            (∀ i : Fin T.length, ∃ a ∈ prev i.val, ∃ b ∈ prev i.val,
              T.get i = a ∪ b ∨ T.get i = a ∩ b) →
            ∀ x ∈ out, ∃ i : Fin T.length, T.get i ⊆ out ∧ x ∈ T.get i ∧
              ∃ a ∈ prev i.val, ∃ b ∈ prev i.val,
                ¬ a ⊆ out ∧ ¬ b ⊆ out ∧ T.get i = a ∩ b)
    (density :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        let x6 : Type := Set (x5 × x5);
        have x7 : Fin x2 → Fin x2 → Bool := fun (x7 x8 : Fin x2) => Decidable.decide (x8 = x7);
        have x8 : List x6 := (List.ofFn fun (x8 : Fin x2) => {x9 : (Fin x2 → Bool) × (Fin x2 → Bool) | x9.1 x8 = Bool.true}) ++ List.ofFn fun (x8 : Fin x2) => {x9 : (Fin x2 → Bool) × (Fin x2 → Bool) | x9.2 x8 = Bool.true};
        (200 : ℕ) ≤ x1 →
          x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
            (∀ (x11 : Fin x2), Fintype.card { x12 : Fin x2 // x3 x12 x11 } = x1 + (1 : ℕ)) →
              (∀ (x12 x13 : Fin x2), x12 ≠ x13 → ∃! x15 : Fin x2, x3 x12 x15 ∧ x3 x13 x15) →
                ∀ (x13 : x6) (x14 : List x6) (x15 : Set (Fin x2 × Fin x2)),
                  have x16 : ℕ → List x6 := fun (x16 : ℕ) => x8 ++ List.take x16 x14;
                  x13 ∈ x8 ++ x14 →
                    (∀ (x18 : Fin x14.length),
                        have x19 : x6 := x14.get x18;
                        x19 ≠ ∅ ∧ x19 ∉ x16 ↑x18 ∧ ∃ x20 ∈ x16 ↑x18, ∃ x21 ∈ x16 ↑x18, ¬x20 ⊆ x21 ∧ ¬x21 ⊆ x20 ∧ (x19 = x20 ∪ x21 ∨ x19 = x20 ∩ x21)) →
                      (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x13) →
                        x15 ⊆ {x20 : Fin x2 × Fin x2 | x3 x20.1 x20.2} →
                          (96 : ℕ) * x14.length + x2 < x15.ncard →
                            (24 : ℕ) * (x2 * x1) + (25 : ℕ) * x2 < (25 : ℕ) * x15.ncard →
                              (∀ x23 ∈ x15,
                                  ∃ (x25 : Fin x14.length),
                                    have x26 : x6 := x14.get x25;
                                    have x27 : List x6 := x16 ↑x25;
                                    x26 ⊆ x13 ∧ (x7 x23.1, x7 x23.2) ∈ x26 ∧ (∃ x28 ∈ x27, ∃ x29 ∈ x27, ¬x28 ⊆ x13 ∧ ¬x29 ⊆ x13 ∧ x26 = x28 ∩ x29) ∧ ¬∃ (x28 : Set x5) (x29 : Set x5), x28 ×ˢ Set.univ ∈ x27 ∧ Set.univ ×ˢ x29 ∈ x27 ∧ x26 = x28 ×ˢ x29) →
                                False)
    :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);
        have x7 : ℕ := x2 + x2;
        (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) → (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) → ∀ (x12 x13 : ℕ) (x14 : ℕ → Set (x5 × x5)) (x15 : Set (Fin x2 × Fin x2)), x13 < x7 + x12 → x7 ≤ x12 + (1 : ℕ) → (∀ (x18 : Fin x2), x14 ↑x18 = {x19 : x5 × x5 | x19.1 x18 = Bool.true} ∧ x14 (x2 + ↑x18) = {x19 : x5 × x5 | x19.2 x18 = Bool.true}) → (∀ x19 < x12, ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x7 + x19 ∧ x14 (x7 + x19) ∈ [x14 x21 ∪ x14 x22, x14 x21, ∅, x14 x21 ∩ x14 x22]) → (∀ (x20 x21 : Fin x2), x3 x20 x21 → (x6 x20, x6 x21) ∈ x14 x13) → (∀ (x21 : x5), Fintype.card { x22 : Fin x2 // x21 x22 = Bool.true } ≤ x1 → (fun (x23 : Fin x2) => Decidable.decide ¬∃ (x24 : Fin x2), x3 x23 x24 ∧ x21 x24 = Bool.true, x21) ∉ x14 x13) → x15 ⊆ {x22 : Fin x2 × Fin x2 | x3 x22.1 x22.2} → (96 : ℕ) * x12 + x2 < x15.ncard → (24 : ℕ) * (x2 * x1) + (25 : ℕ) * x2 < (25 : ℕ) * x15.ncard → (∀ x25 < x12, x14 (x7 + x25) ⊆ x14 x13 → ∀ (x28 x29 : ℕ), Max.max x28 x29 < x7 + x25 → x14 (x7 + x25) = x14 x28 ∩ x14 x29 → ∀ (x32 x33 : Set x5), x14 x28 = x32 ×ˢ Set.univ → x14 x29 = Set.univ ×ˢ x33 → ∀ x36 ∈ x15, (x6 x36.1, x6 x36.2) ∉ x14 (x7 + x25)) → False := by
  intro q n I inst B bit m hq hn hdegree hunique
  intro s o W E hout _ hinputs hstep accept reject hE hbudget hdense uncovered
  have nonempty : W o ≠ ∅ := by
    have hnpos : 0 < n := by omega
    let l : Fin n := ⟨0, hnpos⟩
    have hpos : 0 < Fintype.card {p // I p l} := by rw [hdegree l]; omega
    obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
    intro h
    have hx := accept p l hp
    rw [h] at hx
    exact hx
  obtain ⟨T, len, bounds, outMem, shape⟩ :=
    normalize (B × B) m s o W hout nonempty hstep
  let src : List (Set (B × B)) :=
    (List.ofFn fun p : Fin n => {z | z.1 p = true}) ++
      List.ofFn (fun l : Fin n => {z | z.2 l = true})
  have srcEq : src = (List.range m).map W := by
    have leftLen : (List.ofFn fun p : Fin n => {z : B × B | z.1 p = true}).length = n :=
      List.length_ofFn
    apply List.ext_getElem
    · simp [src, m]
    · intro j hs hr
      rw [List.getElem_map, List.getElem_range]
      by_cases left : j < n
      · change ((List.ofFn fun p : Fin n => {z : B × B | z.1 p = true}) ++
          List.ofFn (fun l : Fin n => {z : B × B | z.2 l = true}))[j] = W j
        rw [List.getElem_append_left (by simpa only [leftLen] using left), List.getElem_ofFn]
        exact (hinputs ⟨j, left⟩).1.symm
      · have inside : j < m := by simpa using hr
        let l : Fin n := ⟨j - n, by dsimp [m] at inside; omega⟩
        have eq : n + l.val = j := by dsimp [l]; omega
        change ((List.ofFn fun p : Fin n => {z : B × B | z.1 p = true}) ++
          List.ofFn (fun l : Fin n => {z : B × B | z.2 l = true}))[j] = W j
        rw [List.getElem_append_right (by rw [leftLen]; omega), List.getElem_ofFn]
        have source : W j = {z : B × B | z.2 l = true} := (congrArg W eq).symm.trans (hinputs l).2
        rw [source]
        have id :
            (⟨j - (List.ofFn fun p : Fin n => {z : B × B | z.1 p = true}).length, by
              rw [leftLen]; exact l.isLt⟩ : Fin n) = l := by
          apply Fin.ext
          simp [leftLen, l]
        exact congrArg (fun t : Fin n => {z : B × B | z.2 t = true}) id
  have listLen : (T.map W).length = T.length := List.length_map W
  let U := T.map W
  let prev (i : ℕ) := src ++ U.take i
  have outU : W o ∈ src ++ U := by
    change W o ∈ src ++ T.map W
    rw [srcEq, ← List.map_append]
    exact outMem
  have newStep (i : Fin U.length) :
      let z := U.get i
      let R := prev i.val
      z ≠ ∅ ∧ z ∉ R ∧ ∃ a ∈ R, ∃ b ∈ R,
        ¬ a ⊆ b ∧ ¬ b ⊆ a ∧ (z = a ∪ b ∨ z = a ∩ b) := by
    let j : Fin T.length := ⟨i.val, listLen ▸ i.isLt⟩
    have poolEq : prev i.val = (List.range m ++ T.take j.val).map W := by
      change src ++ (T.map W).take i.val = _
      rw [srcEq, List.map_append, ← List.map_take]
    have valueEq : U.get i = W (T.get j) := List.getElem_map W
    dsimp only
    rw [valueEq, poolEq]
    exact (shape j).2
  have newBudget : 96 * U.length + n < E.ncard := by
    change 96 * (T.map W).length + n < E.ncard
    rw [listLen]
    omega
  have raw (z : Set (B × B)) (hz : z ∈ src) : ¬ z ⊆ W o := by
    intro sub
    rcases List.mem_append.mp hz with left | right
    · obtain ⟨p, id⟩ := List.mem_ofFn.mp left
      let zero : B := fun _ => false
      have cardZero : Fintype.card {l : Fin n // zero l = true} ≤ q := by simp [zero]
      apply reject zero cardZero
      apply sub
      change _ ∈ z
      rw [← id]
      change decide (¬ ∃ l, I p l ∧ zero l = true) = true
      simp [zero]
    · obtain ⟨l, id⟩ := List.mem_ofFn.mp right
      have cardBit : Fintype.card {k : Fin n // bit l k = true} ≤ q := by
        rw [Fintype.card_of_subtype ({l} : Finset (Fin n)) (by intro k; simp [bit])]
        simpa using show 1 ≤ q by omega
      apply reject (bit l) cardBit
      apply sub
      rw [← id]
      exact decide_eq_true rfl
  have generated (i : Fin U.length) : ∃ a ∈ prev i.val, ∃ b ∈ prev i.val,
      U.get i = a ∪ b ∨ U.get i = a ∩ b := by
    obtain ⟨a, ha, b, hb, _, _, law⟩ := (newStep i).2.2
    exact ⟨a, ha, b, hb, law⟩
  apply density q n I hq hn hdegree hunique (W o) U E outU newStep
    reject hE newBudget hdense
  intro e he
  have seen := accept e.1 e.2 (hE he)
  obtain ⟨i, sub, hit, witness⟩ :=
    frontier (B × B) src U (W o) outU raw generated (bit e.1,bit e.2) seen
  refine ⟨i, sub, hit, witness, ?_⟩
  rintro ⟨P, L, hp, hl, product⟩
  have separated : (P ×ˢ Set.univ) ∩ (Set.univ ×ˢ L) = P ×ˢ L := by
    ext a
    simp
  have meet : U.get i = (P ×ˢ Set.univ) ∩ (Set.univ ×ˢ L) := product.trans separated.symm
  apply (show (bit e.1,bit e.2) ∉ U.get i from ?_) hit
  let j : Fin T.length := ⟨i.val, listLen ▸ i.isLt⟩
  have poolEq : src ++ (T.map W).take i.val =
      (List.range m ++ T.take j.val).map W := by
    rw [srcEq, List.map_append, ← List.map_take]
  have valueEq : (T.map W).get i = W (T.get j) := List.getElem_map W
  change P ×ˢ Set.univ ∈ src ++ (T.map W).take i.val at hp
  change Set.univ ×ˢ L ∈ src ++ (T.map W).take i.val at hl
  rw [poolEq] at hp hl
  obtain ⟨a, ha, ea⟩ := List.mem_map.mp hp
  obtain ⟨b, hb, eb⟩ := List.mem_map.mp hl
  obtain ⟨lower, upper⟩ := bounds _ (List.get_mem T j)
  let k := T.get j - m
  have index : m + k = T.get j := Nat.add_sub_of_le lower
  have kbound : k < s := by omega
  have before : max a b < m + k := by
    rw [index]
    exact max_lt_iff.mpr ⟨(shape j).1 a ha, (shape j).1 b hb⟩
  change (T.map W).get i ⊆ W o at sub
  change (T.map W).get i = (P ×ˢ Set.univ) ∩ (Set.univ ×ˢ L) at meet
  change (bit e.1,bit e.2) ∉ (T.map W).get i
  rw [valueEq] at sub meet ⊢
  have meetOld : W (m + k) = W a ∩ W b := by rw [index, meet, ea, eb]
  rw [← index] at sub ⊢
  exact uncovered k kbound sub a b before meetOld P L ea eb e he
