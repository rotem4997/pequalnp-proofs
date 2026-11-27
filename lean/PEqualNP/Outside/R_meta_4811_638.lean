import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4811_638
    (positive :
      let T := Fin 21
      let S : T → Finset T := fun l => Finset.univ.filter fun p =>
        (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let F : (Fin 42 → Bool) → Prop := fun x =>
        ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧
          (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x p = true ∧ x l = true
      ∀ x, F x →
        (∀ y, (∀ j, y j = true → x j = true) → F y → y = x) →
        ∃ p l : T, p ∈ S l ∧ List.ofFn x = PEqualNP.GenericRejection.incidenceInput {p} {l})
    (negative :
      let T := Fin 21
      let S : T → Finset T := fun l => Finset.univ.filter fun p =>
        (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let F : (Fin 42 → Bool) → Prop := fun x =>
        ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧
          (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x p = true ∧ x l = true
      ∀ x, ¬ F x →
        (∀ y, (∀ j, x j = true → y j = true) → ¬ F y → y = x) →
        ∃ X : Finset T,
          let Y := PEqualNP.HeptadCover.missLines S X
          PEqualNP.GenericRejection.zeroSet S Y = X ∧
          List.ofFn x = PEqualNP.GenericRejection.incidenceInput X Y)
    (candidate :
      let T := Fin 21
      let S : T → Finset T := fun l => Finset.univ.filter fun p =>
        (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let P := Fin 42
      let Q := Fin 43
      let E := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (i : P) (a b : Q) (xs : List Bool) =>
        let ys := xs ++ [xs.getD 0 false || xs.getD i.val false]
        C.eval (ys ++ [ys.getD a.val false || ys.getD b.val false])
      (∃ (i : P) (a b : Q) (C : PEqualNP.CircuitLowerBounds.Circuit),
        i ∈ ([1, 21, 22] : List P) ∧ a < b ∧ (a, b) ≠ (0, i.castSucc) ∧
        (b = Fin.last 42 → a ≠ 0 ∧ a ≠ i.castSucc) ∧
        (∀ j : P, List.count j.val [0, i.val, a.val, b.val] = 1 →
          ∃ g ∈ C.gates, j.val ∈ g.inputs) ∧
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 44 C ∧
        C.size ≤ 122 ∧
        (∀ p l : T, p ∈ S l → E C i a b (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true) ∧
        ∀ X : Finset T,
          let Y := PEqualNP.HeptadCover.missLines S X
          PEqualNP.GenericRejection.zeroSet S Y = X →
          E C i a b (PEqualNP.GenericRejection.incidenceInput X Y) = false)) :
    have x1 : (Fin (42 : ℕ) → Bool) → Prop := fun (x1 : Fin (42 : ℕ) → Bool) => ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (42 : ℕ)), (↑x2 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3 ∧ (↑x3 + (21 : ℕ) - ↑x2) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : Fin (43 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (x2 = (1 : Fin (42 : ℕ)) ∨ x2 = (21 : Fin (42 : ℕ)) ∨ x2 = (22 : Fin (42 : ℕ))) ∧     x3 < x4 ∧       (x3, x4) ≠ ((0 : Fin (43 : ℕ)), x2.castSucc) ∧         (x4 = Fin.last (42 : ℕ) → x3 ≠ (0 : Fin (43 : ℕ)) ∧ x3 ≠ x2.castSucc) ∧           (∀ (x6 : Fin (42 : ℕ)), List.count ↑x6 [(0 : ℕ), ↑x2, ↑x3, ↑x4] = (1 : ℕ) → ∃ x8 ∈ x5.gates, ↑x6 ∈ x8.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x5 ∧                 x5.size ≤ (122 : ℕ) ∧                   ∀ (x6 : Fin (42 : ℕ) → Bool),                     ((x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x7 x8 = Bool.true → x6 x8 = Bool.true) → x1 x7 → x7 = x6) ∨ ¬x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x6 x8 = Bool.true → x7 x8 = Bool.true) → ¬x1 x7 → x7 = x6) →                       have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 (0 : Fin (42 : ℕ)) || x6 x2) x6 x8;                       x5.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x3 || x8 x4) x8 x9) = Bool.true ↔ x1 x6 := by
  rcases candidate with ⟨i, a, b, C, hi, hab, hpair, hlast, hread, hmono, hback, hsize, hp, hn⟩
  have hi' : i = (1 : Fin 42) ∨ i = 21 ∨ i = 22 := by simpa using hi
  refine ⟨i, a, b, C, hi', hab, hpair, hlast, hread, hmono, hback, hsize, ?_⟩
  have snoc {n : ℕ} (x : Fin n → Bool) (b : Bool) :
      List.ofFn (Fin.lastCases b x) = List.ofFn x ++ [b] := by
    simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append] using
      (List.ofFn_succ' (Fin.lastCases b x))
  have read {n : ℕ} (x : Fin n → Bool) (j : Fin n) : (List.ofFn x).getD j.val false = x j := by
    have hj : j.val < (List.ofFn x).length := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem_ofFn]
    rfl
  intro x h
  let y : Fin 43 → Bool := Fin.lastCases (x 0 || x i) x
  change C.eval (List.ofFn (Fin.lastCases (y a || y b) y)) = true ↔ _
  rw [snoc, ← read y a, ← read y b]
  have hy : List.ofFn y = List.ofFn x ++
      [(List.ofFn x).getD 0 false || (List.ofFn x).getD i.val false] := by
    rw [read x i]
    have hzero := read x (0 : Fin 42)
    change (List.ofFn x).getD 0 false = x 0 at hzero
    rw [hzero]
    exact snoc x (x 0 || x i)
  rw [hy]
  rcases h with ⟨hpos, hmin⟩ | ⟨hneg, hmax⟩
  · obtain ⟨p, l, hpl, hx⟩ := positive x hpos hmin
    refine iff_of_true ?_ hpos
    rw [hx]
    exact hp p l hpl
  · obtain ⟨X, hclosed, hx⟩ := negative x hneg hmax
    refine iff_of_false ?_ hneg
    rw [hx]
    have hfalse := hn X hclosed
    exact fun he => Bool.noConfusion (he.symm.trans hfalse)
