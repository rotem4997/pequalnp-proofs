import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A permutation transports the first fourteen wires and fixes the extra feature wire.
-- The two subproblems give the remaining circuit the value of its first AND or OR for free.
-- Its two operands are equal, on the same side, incident, or on opposite sides and nonincident.
-- The empty and one-operand cases are included because fan-in is an upper bound.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_1985_84
    (andBound : ∀ (T : Circuit) (ks : List ℕ), Monotone2 T → ReadsBack 15 T →
      ks ∈ [[], [0], [0,0], [0,1], [0,7], [0,9]] →
      let pos : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let neg : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      (∀ r ∈ pos ++ neg, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
        [GateOp.and.eval (ks.map fun k => r.testBit k)]) = decide (r ∈ pos)) → 26 ≤ T.size)
    (orBound : ∀ (T : Circuit) (ks : List ℕ), Monotone2 T → ReadsBack 15 T →
      ks ∈ [[], [0], [0,0], [0,1], [0,7], [0,9]] →
      let pos : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let neg : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      (∀ r ∈ pos ++ neg, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
        [GateOp.or.eval (ks.map fun k => r.testBit k)]) = decide (r ∈ pos)) → 26 ≤ T.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let A (u v : Fin 14) := (u.val, v.val) ∈ edges ∨ (v.val, u.val) ∈ edges
  let Good (p : Fin 14 → Fin 14) :=
    (∀ i, ∃ j, p j = i) ∧ ∀ u v, A u v ↔ A (p u) (p v)
  let F (x : Fin 14 → Bool) := ∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
  let pos : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
  let neg : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
  let canon : List (List ℕ) := [[], [0], [0,0], [0,1], [0,7], [0,9]]
  let tab₁ : List (List (Fin 14)) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8],
    [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8],
    [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12],
    [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8],
    [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12],
    [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12],
    [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6],
    [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6],
    [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3],
    [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6],
    [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3],
    [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3],
    [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0]]
  let tab₂ : List (List (Fin 14)) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13],
    [0, 3, 2, 1, 5, 4, 6, 7, 8, 11, 10, 9, 13, 12],
    [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13],
    [0, 2, 5, 6, 3, 1, 4, 8, 10, 13, 7, 11, 9, 12],
    [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13],
    [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12],
    [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13],
    [0, 1, 5, 3, 6, 2, 4, 7, 10, 13, 8, 11, 12, 9]]
  let α (a i : Fin 14) := (tab₁.getD a.val []).getD i.val 0
  let β (a i : Fin 14) := (tab₂.getD a.val []).getD i.val 0
  have one : ∀ a, α a a = 0 ∧ Good (α a) := by decide
  have two : ∀ a, β a 0 = 0 ∧ β a a ∈ ([0,1,7,9] : List (Fin 14)) ∧ Good (β a) := by decide
  have pair (a b : Fin 14) : ∃ p, Good p ∧ p a = 0 ∧ p b ∈ ([0,1,7,9] : List (Fin 14)) := by
    obtain ⟨ha, hα⟩ := one a
    obtain ⟨hz, hb, hβ⟩ := two (α a b)
    refine ⟨fun i => β (α a b) (α a i), ⟨?_, ?_⟩, ?_, hb⟩
    · intro i
      obtain ⟨j, hj⟩ := hβ.1 i
      obtain ⟨k, hk⟩ := hα.1 j
      exact ⟨k, (congrArg (β (α a b)) hk).trans hj⟩
    · intro u v
      exact (hα.2 u v).trans (hβ.2 _ _)
    · simpa only [ha] using hz
  let ren (p : Fin 14 → Fin 14) (k : ℕ) := (p (Fin.ofNat 14 k)).val
  have orbit (ks : List ℕ) (hl : ks.length ≤ 2) :
      ∃ p, Good p ∧ ks.map (ren p) ∈ canon := by
    rcases ks with _ | ⟨k, ks⟩
    · exact ⟨α 0, (one 0).2, by simp [canon]⟩
    rcases ks with _ | ⟨l, rest⟩
    · obtain ⟨p, hp, hk, _⟩ := pair (Fin.ofNat 14 k) 0
      exact ⟨p, hp, by simp only [List.map_cons, List.map_nil, ren, hk]; decide⟩
    cases rest with
    | cons r rs => simp at hl
    | nil =>
      obtain ⟨p, hp, hk, hmem⟩ := pair (Fin.ofNat 14 k) (Fin.ofNat 14 l)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      refine ⟨p, hp, ?_⟩
      rcases hmem with h | h | h | h <;> simp only [List.map_cons, List.map_nil, ren, hk, h] <;> decide
  have asAdj (x : Fin 14 → Bool) : F x ↔ ∃ u v : Fin 14, A u v ∧ x u = true ∧ x v = true := by
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨u, v, Or.inl huv, hu, hv⟩
    · rintro ⟨u, v, huv | hvu, hu, hv⟩
      · exact ⟨u, v, huv, hu, hv⟩
      · exact ⟨v, u, hvu, hv, hu⟩
  have invariant (p : Fin 14 → Fin 14) (hp : Good p) (x : Fin 14 → Bool) :
      F (fun i => x (p i)) ↔ F x := by
    rw [asAdj, asAdj]
    constructor
    · rintro ⟨u, v, h, hu, hv⟩
      exact ⟨p u, p v, (hp.2 u v).mp h, hu, hv⟩
    · rintro ⟨u, v, h, hu, hv⟩
      obtain ⟨a, rfl⟩ := hp.1 u
      obtain ⟨b, rfl⟩ := hp.1 v
      exact ⟨a, b, (hp.2 _ _).mpr h, hu, hv⟩
  have labels : ∀ r ∈ pos ++ neg, F (fun i => r.testBit i.val) ↔ r ∈ pos := by decide
  have transport (D : Circuit) (p : Fin 14 → Fin 14) (hm : Monotone2 D) (hb : ReadsBack 15 D) :
      ∃ T : Circuit, Monotone2 T ∧ ReadsBack 15 T ∧ T.size = D.size ∧
      ∀ (x : Fin 14 → Bool) (b : Bool),
        T.eval (List.ofFn x ++ [b]) = D.eval (List.ofFn (fun i => x (p i)) ++ [b]) := by
    let w (i : ℕ) := if h : i < 14 then (p ⟨i, h⟩).val else i
    let gate (g : Gate) : Gate := ⟨g.op, g.inputs.map w⟩
    let T : Circuit := ⟨D.gates.map gate, w D.output⟩
    have smallW {i m : ℕ} (hm : 14 ≤ m) (hi : i < m) : w i < m := by
      by_cases h : i < 14
      · simpa only [w, dite_eq_left h] using lt_of_lt_of_le (p ⟨i, h⟩).isLt hm
      · simpa [w, h] using hi
    refine ⟨T, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hm g₀ hg₀).1, by simpa [gate] using (hm g₀ hg₀).2⟩
    · intro j hj k hk
      have hjD : j < D.gates.length := by simpa [T] using hj
      have ht : gateAt T j = gate (gateAt D j) := by
        change (D.gates.map gate).getD j _ = gate (D.gates.getD j _)
        simp [List.getD_eq_getElem?_getD, hjD]
      rw [ht] at hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      exact smallW (by omega) (hb j hjD i hi)
    · change (D.gates.map gate).length = D.gates.length
      exact List.length_map gate
    · intro x b
      let R (U V : List Bool) := 14 ≤ U.length ∧ V.length = U.length ∧
        ∀ i, V.getD (w i) false = U.getD i false
      have snoc (U V : List Bool) (r : R U V) (z : Bool) : R (U ++ [z]) (V ++ [z]) := by
        obtain ⟨lo, len, vals⟩ := r
        refine ⟨by simp; omega, by simp [len], ?_⟩
        intro i
        by_cases h : i < U.length
        · rw [List.getD_append _ _ _ _ (len ▸ smallW lo h), List.getD_append _ _ _ _ h]
          exact vals i
        · have hw : w i = i := by simp [w, show ¬ i < 14 by omega]
          rw [hw, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]
      let step (U : List Bool) (g : Gate) := U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]
      have fold (gs : List Gate) (U V : List Bool) (r : R U V) :
          R (gs.foldl step U) ((gs.map gate).foldl step V) := by
        induction gs generalizing U V with
        | nil => exact r
        | cons g gs ih =>
          apply ih
          have same : (gate g).op.eval ((gate g).inputs.map fun i => V.getD i false) =
              g.op.eval (g.inputs.map fun i => U.getD i false) := by
            apply congrArg g.op.eval
            simp only [gate, List.map_map]
            apply List.map_congr_left
            exact fun i _ => r.2.2 i
          change R (U ++ [_]) (V ++ [(gate g).op.eval _])
          rw [same]
          exact snoc U V r _
      have start : R (List.ofFn (fun i => x (p i))) (List.ofFn x) := by
        refine ⟨by simp, by simp, ?_⟩
        intro i
        by_cases h : i < 14
        · have hp := (p ⟨i, h⟩).isLt
          simp only [w, dite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hp, Option.getD_some]
        · simp [w, h, List.getD_eq_getElem?_getD]
      exact (fold D.gates _ _ (snoc _ _ start b)).2.2 D.output
  intro C hmono hback hnested hfun
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil =>
    obtain ⟨i, j, hi, _⟩ := hnested
    change (([] : List Gate).getD i ⟨GateOp.or, []⟩).op = GateOp.and at hi
    simp at hi
  | cons g gs =>
    let D : Circuit := ⟨gs, out⟩
    have hop := hmono g (by simp)
    have small (k : ℕ) (hk : k ∈ g.inputs) : k < 14 := by
      have hh := hback 0 (by simp) k hk
      simpa using hh
    have dm : Monotone2 D := fun z hz => hmono z (List.mem_cons_of_mem _ hz)
    have db : ReadsBack 15 D := by
      intro j hj k hk
      have hj' : j + 1 < (g :: gs).length := by simpa [D] using hj
      have hk' : k ∈ (gateAt (⟨g :: gs, out⟩ : Circuit) (j+1)).inputs := by
        exact hk
      have h := hback (j+1) hj' k hk'
      omega
    obtain ⟨p, hp, hrep⟩ := orbit g.inputs hop.2
    obtain ⟨T, tm, tb, ts, te⟩ := transport D p dm db
    have result :
        (∀ r ∈ pos ++ neg, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
          [g.op.eval ((g.inputs.map (ren p)).map fun k => r.testBit k)]) = decide (r ∈ pos)) → 26 ≤ T.size := by
      rcases (show g.op = GateOp.and ∨ g.op = GateOp.or from hop.1) with ha | ho
      · rw [ha]
        exact andBound T _ tm tb hrep
      · rw [ho]
        exact orBound T _ tm tb hrep
    have ht : 26 ≤ T.size := by
      apply result
      intro r hr
      let x (i : Fin 14) := r.testBit i.val
      let y (i : Fin 14) := x (p i)
      have heq : (g.inputs.map (ren p)).map (fun k => r.testBit k) =
          g.inputs.map (fun k => (List.ofFn y).getD k false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have h := small k hk
        rw [List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn, Function.comp_apply, ren, y, x]
        have cast : Fin.ofNat 14 k = ⟨k, h⟩ := Fin.ext (Nat.mod_eq_of_lt h)
        rw [cast]
      rw [heq, te]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact (hfun y).trans ((invariant p hp x).trans (labels r hr))
    change 27 ≤ (g :: gs).length
    change T.size = gs.length at ts
    simp only [List.length_cons]
    omega
