import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3077_7
    (h1 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) → (↑x2 : ℕ) ≤ List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑x2 ↑x2 →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))))
    (h2 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x2 = (9 : ℕ) → (↑x1 : ℕ) ≤ List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑x1 ↑x1 →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ)))) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b c L hL hab ha hb hcov
  -- the symmetry (1 5)(2 8)(6 7) of the graph fixes 0 and 4, hence the wire x0 OR x4
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b0 && b5 || (b5 && b8 || (b8 && b3 || (b3 && b4 || (b4 && b0 || (b0 && b1 ||
        (b5 && b7 || (b8 && b6 || (b3 && b2 || (b1 && b6 || (b7 && b2 || (b2 && b1 ||
          false)))))))))))) =
      (b0 && b1 || (b1 && b2 || (b2 && b3 || (b3 && b4 || (b4 && b0 || (b0 && b5 ||
        (b1 && b6 || (b2 && b7 || (b3 && b8 || (b5 && b7 || (b6 && b8 || (b8 && b5 ||
          false)))))))))))) := by
    decide
  have hlt : ∀ j : ℕ, j < 9 → List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j < 9 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 9 ≤ j → List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hinv : ∀ j : ℕ, List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ)
      (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) = j := by
    intro j
    by_cases hj : j < 9
    · interval_cases j <;> decide
    · rw [hge j (by omega), hge j (by omega)]
  have hr : ∀ v : Fin 26,
      ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) : ℕ) =
        List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v := by
    intro v
    rw [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    by_cases h : (v : ℕ) < 9
    · have := hlt v h
      omega
    · rw [hge v (by omega)]
      exact v.2
  have hne : ∀ v : Fin 26, (v : ℕ) ≠ 25 → List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v ≠ 25 := by
    intro v hv
    by_cases h : (v : ℕ) < 9
    · have := hlt v h
      omega
    · rw [hge v (by omega)]
      exact hv
  have hX : ∀ (W W' : List Bool),
      (∀ j : ℕ, W'.getD (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) false = W.getD j false) →
      ∀ v : Fin 26,
      (if ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) : ℕ) = 25 then true
        else W'.getD ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) : ℕ)
          false) =
      (if (v : ℕ) = 25 then true else W.getD (v : ℕ) false) := by
    intro W W' hW v
    rw [hr v]
    by_cases h25 : (v : ℕ) = 25
    · rw [if_pos h25, h25, hge 25 (by omega), if_pos rfl]
    · rw [if_neg h25, if_neg (hne v h25)]
      exact hW v
  have happ : ∀ (W W' : List Bool) (u : Bool), W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) false = W.getD j false) →
      ∀ j : ℕ, (W' ++ [u]).getD (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) false =
        (W ++ [u]).getD j false := by
    intro W W' u hl h9 hW j
    by_cases hj : j < W.length
    · have hj' : List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j < W'.length := by
        by_cases h : j < 9
        · have := hlt j h
          omega
        · rw [hge j (by omega)]
          omega
      have hWj := hW j
      generalize List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j = r at hj' hWj ⊢
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hj', List.getElem?_append_left hj]
      simpa only [List.getD_eq_getElem?_getD] using hWj
    · rw [hge j (by omega)]
      by_cases hj2 : j = W.length
      · subst hj2
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
          List.getElem?_append_right (le_refl _), ← hl,
          List.getElem?_append_right (le_refl _)]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hpre : ∀ (gs : List (Fin 3 × Fin 26 × Fin 26)) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) false = W.getD j false) →
      ∀ j : ℕ,
        (List.foldl (fun (w : List Bool) (t : Fin 3 × Fin 26 × Fin 26) => w ++
            [if (t.1 : ℕ) = 0 then
              (if (t.2.1 : ℕ) = 25 then true else w.getD (t.2.1 : ℕ) false) &&
                (if (t.2.2 : ℕ) = 25 then true else w.getD (t.2.2 : ℕ) false)
            else if (t.1 : ℕ) = 1 then
              (if (t.2.1 : ℕ) = 25 then true else w.getD (t.2.1 : ℕ) false) ||
                (if (t.2.2 : ℕ) = 25 then true else w.getD (t.2.2 : ℕ) false)
            else !(if (t.2.1 : ℕ) = 25 then true else w.getD (t.2.1 : ℕ) false)]) W'
          (gs.map fun t : Fin 3 × Fin 26 × Fin 26 =>
            (t.1, (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.1 ↑t.2.1) : Fin 26),
              (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.2 ↑t.2.2) : Fin 26)))).getD
            (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) false =
        (List.foldl (fun (w : List Bool) (t : Fin 3 × Fin 26 × Fin 26) => w ++
            [if (t.1 : ℕ) = 0 then
              (if (t.2.1 : ℕ) = 25 then true else w.getD (t.2.1 : ℕ) false) &&
                (if (t.2.2 : ℕ) = 25 then true else w.getD (t.2.2 : ℕ) false)
            else if (t.1 : ℕ) = 1 then
              (if (t.2.1 : ℕ) = 25 then true else w.getD (t.2.1 : ℕ) false) ||
                (if (t.2.2 : ℕ) = 25 then true else w.getD (t.2.2 : ℕ) false)
            else !(if (t.2.1 : ℕ) = 25 then true else w.getD (t.2.1 : ℕ) false)]) W gs).getD
          j false := by
    intro gs
    induction gs with
    | nil =>
      intro W W' _ _ hW j
      exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      have h1' := hX W W' hW g.2.1
      have h2' := hX W W' hW g.2.2
      simp only [List.map_cons, List.foldl_cons]
      rw [h1', h2']
      apply ih
      · simp [hl]
      · simp
        omega
      · exact happ W W' _ hl h9 hW
  have hwit : ∀ m : ℕ, ∃ n < 512, ∀ i : Fin 9,
      n.testBit ↑i = m.testBit (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑i ↑i) := by
    intro m
    have hd : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : Bool,
        c0.toNat + 2 * c1.toNat + 4 * c2.toNat + 8 * c3.toNat + 16 * c4.toNat + 32 * c5.toNat +
          64 * c6.toNat + 128 * c7.toNat + 256 * c8.toNat < 512 ∧
        ∀ i : Fin 9, (c0.toNat + 2 * c1.toNat + 4 * c2.toNat + 8 * c3.toNat + 16 * c4.toNat +
          32 * c5.toNat + 64 * c6.toNat + 128 * c7.toNat + 256 * c8.toNat).testBit ↑i =
            [c0, c1, c2, c3, c4, c5, c6, c7, c8].getD ↑i false := by
      decide
    obtain ⟨hd1, hd2⟩ := hd (m.testBit 0) (m.testBit 5) (m.testBit 8) (m.testBit 3) (m.testBit 4)
      (m.testBit 1) (m.testBit 7) (m.testBit 6) (m.testBit 2)
    refine ⟨_, hd1, ?_⟩
    intro i
    rw [hd2 i]
    fin_cases i <;> rfl
  have h9le : ∀ v : Fin 26, (v : ℕ) = 9 → (v : ℕ) ≤ List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v := by
    intro v hv
    rw [hv]
    decide
  have h9r : ∀ v : Fin 26, (v : ℕ) = 9 →
      ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) : ℕ) = 9 := by
    intro v hv
    rw [hr, hv]
    rfl
  have hcan : ∀ v : Fin 26, ¬ ((v : ℕ) ≤ List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) →
      ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) : ℕ) ≤
        List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ)
          ↑(Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26)
          ↑(Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) := by
    intro v hv
    rw [hr, hinv]
    omega
  have h25 : ∀ v : Fin 26, (v : ℕ) ≠ 25 →
      ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑v ↑v) : Fin 26) : ℕ) ≠ 25 := by
    intro v hv
    rw [hr]
    exact hne v hv
  by_cases hc : (a : ℕ) ≤ List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑a ↑a ∧
      (b : ℕ) ≤ List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑b ↑b
  · rcases hab with h | h
    · exact h1 a b c L hL h hc.2 ha hb hcov
    · exact h2 a b c L hL h hc.1 ha hb hcov
  · have hL' : (L.map fun t : Fin 3 × Fin 26 × Fin 26 =>
        (t.1, (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.1 ↑t.2.1) : Fin 26),
          (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.2 ↑t.2.2) : Fin 26))).length ≤
        13 := by
      rw [List.length_map]
      exact hL
    have hcov' : ∀ k < 9, ∃ t ∈ (L.map fun t : Fin 3 × Fin 26 × Fin 26 =>
        (t.1, (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.1 ↑t.2.1) : Fin 26),
          (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.2 ↑t.2.2) : Fin 26))),
        (t.2.1 : ℕ) = k ∨ (t.2.2 : ℕ) = k := by
      intro k hk
      obtain ⟨t, ht, h⟩ := hcov (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) k k) (hlt k hk)
      refine ⟨_, List.mem_map_of_mem ht, ?_⟩
      show ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.1 ↑t.2.1) : Fin 26) : ℕ) = k ∨
        ((Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑t.2.2 ↑t.2.2) : Fin 26) : ℕ) = k
      rw [hr, hr]
      rcases h with h | h
      · left
        rw [h, hinv]
      · right
        rw [h, hinv]
    have Hex := hab.elim
      (fun h => h1 _ _ (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑c ↑c)) _ hL' (h9r a h) (hcan b (fun hbb => hc ⟨h9le a h, hbb⟩))
        (h25 a ha) (h25 b hb) hcov')
      (fun h => h2 _ _ (Fin.ofNat 26 (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) ↑c ↑c)) _ hL' (h9r b h) (hcan a (fun haa => hc ⟨haa, h9le b h⟩))
        (h25 a ha) (h25 b hb) hcov')
    obtain ⟨m, hm, hP⟩ := Hex
    obtain ⟨n, hn, hbits⟩ := hwit m
    refine ⟨n, hn, ?_⟩
    have e0 : n.testBit 0 = m.testBit 0 := hbits 0
    have e1 : n.testBit 1 = m.testBit 5 := hbits 1
    have e2 : n.testBit 2 = m.testBit 8 := hbits 2
    have e3 : n.testBit 3 = m.testBit 3 := hbits 3
    have e4 : n.testBit 4 = m.testBit 4 := hbits 4
    have e5 : n.testBit 5 = m.testBit 1 := hbits 5
    have e6 : n.testBit 6 = m.testBit 7 := hbits 6
    have e7 : n.testBit 7 = m.testBit 6 := hbits 7
    have e8 : n.testBit 8 = m.testBit 2 := hbits 8
    have hinit : ∀ j : ℕ,
        (List.ofFn (fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 4]).getD
          (List.getD ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ) j j) false =
        (List.ofFn (fun i : Fin 9 => n.testBit ↑i) ++ [n.testBit 0 || n.testBit 4]).getD j false := by
      intro j
      by_cases hj : j < 10
      · interval_cases j
        · exact e0.symm
        · exact e1.symm
        · exact e2.symm
        · exact e3.symm
        · exact e4.symm
        · exact e5.symm
        · exact e6.symm
        · exact e7.symm
        · exact e8.symm
        · show (m.testBit 0 || m.testBit 4) = (n.testBit 0 || n.testBit 4)
          rw [e0, e4]
      · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have e := hpre (((1 : Fin 3), a, b) :: L)
      (List.ofFn (fun i : Fin 9 => n.testBit ↑i) ++ [n.testBit 0 || n.testBit 4])
      (List.ofFn (fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 4])
      (by simp) (by simp) hinit ↑c
    rw [← hr c] at e
    have hedge : (n.testBit 0 && n.testBit 1 || (n.testBit 1 && n.testBit 2 ||
        (n.testBit 2 && n.testBit 3 || (n.testBit 3 && n.testBit 4 || (n.testBit 4 && n.testBit 0 ||
        (n.testBit 0 && n.testBit 5 || (n.testBit 1 && n.testBit 6 || (n.testBit 2 && n.testBit 7 ||
        (n.testBit 3 && n.testBit 8 || (n.testBit 5 && n.testBit 7 || (n.testBit 6 && n.testBit 8 ||
        (n.testBit 8 && n.testBit 5 || false)))))))))))) =
        (m.testBit 0 && m.testBit 1 || (m.testBit 1 && m.testBit 2 ||
        (m.testBit 2 && m.testBit 3 || (m.testBit 3 && m.testBit 4 || (m.testBit 4 && m.testBit 0 ||
        (m.testBit 0 && m.testBit 5 || (m.testBit 1 && m.testBit 6 || (m.testBit 2 && m.testBit 7 ||
        (m.testBit 3 && m.testBit 8 || (m.testBit 5 && m.testBit 7 || (m.testBit 6 && m.testBit 8 ||
        (m.testBit 8 && m.testBit 5 || false)))))))))))) := by
      rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]
      exact hF0 _ _ _ _ _ _ _ _ _
    intro x11 x12 x13 hcon
    apply hP
    exact e.trans (hcon.trans hedge)
