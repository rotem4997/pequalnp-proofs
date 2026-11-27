import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Use the first two ORs to compute a line with five points.
-- Save the gate in the circuit for the other twenty lines.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2436_1
    (gadget : ∃ D : Circuit, Monotone2 D ∧ ReadsBack 42 D ∧
      D.output < 42 + D.size ∧ D.size ≤ 118 ∧
      (∀ i : Fin 42, i.val ∈ ([0, 1, 4, 14] : List ℕ) →
        ∃ g ∈ D.gates, i.val ∈ g.inputs) ∧
      ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 < v.val ∧
          (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x v = true)
    (pad : ∀ (n : ℕ) (D : Circuit), Monotone2 D → ReadsBack n D →
      D.output < n + D.size →
      ∃ E : Circuit, Monotone2 E ∧ ReadsBack (n + 2) E ∧ E.size = D.size ∧
        E.output < n + 2 + E.size ∧
        (∀ (x : List Bool), x.length = n → ∀ a b : Bool, E.eval (x ++ [a, b]) = D.eval x) ∧
        ∀ i < n, (∃ g ∈ D.gates, i ∈ g.inputs) → ∃ g ∈ E.gates, i ∈ g.inputs)
    : ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ))
        (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧
        x2 < x3 ∧
          (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) ∧
            (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) ∧
              (∀ (x5 : Fin (42 : ℕ)), List.count ↑x5 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) →
                  ∃ x7 ∈ x4.gates, ↑x5 ∈ x7.inputs) ∧
                PEqualNP.MetaComplexity.Monotone2 x4 ∧
                  PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧
                    x4.size ≤ (122 : ℕ) ∧
                      ∀ (x5 : Fin (42 : ℕ) → Bool),
                        have x6 : Fin (43 : ℕ) → Bool :=
                          fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;
                        x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔
                      ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧
                          (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
                          x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  obtain ⟨D, hdM, hdR, hdO, hdS, hdInputs, hdEval⟩ := gadget
  obtain ⟨E, heM, heR, heS, heO, heEval, heInputs⟩ := pad 42 D hdM hdR hdO
  let m := E.gates.length
  let r := 44 + m
  let g1 : Gate := ⟨GateOp.or, [42, 43]⟩
  let g2 : Gate := ⟨GateOp.or, [r, 16]⟩
  let g3 : Gate := ⟨GateOp.and, [21, r + 1]⟩
  let g4 : Gate := ⟨GateOp.or, [E.output, r + 2]⟩
  let tailGates := [g1, g2, g3, g4]
  let C : Circuit := ⟨E.gates ++ tailGates, r + 3⟩
  have hBound : E.output < r := heO
  have cSize : C.size ≤ 122 := by
    change (E.gates ++ tailGates).length ≤ 122
    have helen : E.gates.length = D.size := heS
    simp only [List.length_append, tailGates, List.length_cons, List.length_nil]
    omega
  have cMon : Monotone2 C := by
    intro g hg
    change g ∈ E.gates ++ tailGates at hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact heM g hg
    · simp only [tailGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp [g1, g2, g3, g4]
  have tailRead (j i : ℕ) (hj : j < 4)
      (hi : i ∈ (tailGates.getD j ⟨GateOp.or, []⟩).inputs) : i < r + j := by
    interval_cases j
    all_goals
      simp [tailGates, g1, g2, g3, g4, List.getD_eq_getElem?_getD] at hi
      rcases hi with rfl | rfl
      all_goals dsimp [r]; omega
  have cRead : ReadsBack 44 C := by
    intro j hj i hi
    change j < (E.gates ++ tailGates).length at hj
    change i ∈ ((E.gates ++ tailGates).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < m
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact heR j hj' i hi
    · have hge : E.gates.length ≤ j := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
        ← List.getD_eq_getElem?_getD] at hi
      have ht : (j - E.gates.length) < 4 := by
        simp only [List.length_append, tailGates, List.length_cons, List.length_nil] at hj
        omega
      have hh := tailRead (j - E.gates.length) i ht hi
      dsimp [r, m] at hh
      omega
  let pointSet : List (Fin 42) := [0, 1, 4, 14, 16]
  let linePart (x : Fin 42 → Bool) := x 21 && pointSet.any x
  have pointTest : ∀ u : Fin 42, (u.val < 21 ∧
      (42 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ↔ u ∈ pointSet := by
    decide +kernel
  have hor : ∀ a b : Bool, (a || b) = true ↔ a = true ∨ b = true := by decide
  have hand : ∀ a b : Bool, (a && b) = true ↔ a = true ∧ b = true := by decide
  let st (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldExtends (gs : List Gate) (w : List Bool) :
      ∃ z, gs.foldl st w = w ++ z ∧ z.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨z, hz, hlen⟩ := ih (w ++ [v])
      refine ⟨v :: z, ?_, by simp [hlen]⟩
      change gs.foldl st (w ++ [v]) = _
      rw [hz, List.append_assoc]
      rfl
  have atLast (w : List Bool) (v : Bool) (k : ℕ) (h : w.length = k) :
      (w ++ [v]).getD k false = v := by
    subst k
    simp
  have ofFnLast (n : ℕ) (f : Fin n → Bool) (b : Bool) :
      List.ofFn (Fin.lastCases b f) = List.ofFn f ++ [b] := by
    rw [List.ofFn_succ']
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append]
  have evalC (x : Fin 42 → Bool) :
      C.eval (List.ofFn x ++ [x 0 || x 1, x 4 || x 14]) =
        (D.eval (List.ofFn x) || linePart x) := by
    let A := x 0 || x 1
    let B := x 4 || x 14
    let X := List.ofFn x ++ [A, B]
    let W := E.wires X
    obtain ⟨z, hExt, hZ⟩ := foldExtends E.gates X
    have hW : W = X ++ z := hExt
    have hX : X.length = 44 := by simp [X]
    have hWlen : W.length = r := by rw [hW, List.length_append, hX, hZ]
    have keep (i : ℕ) (hi : i < 44) : W.getD i false = X.getD i false := by
      rw [hW, List.getD_append _ _ _ _ (hX.symm ▸ hi)]
    have bit (i : Fin 42) : W.getD i.val false = x i := by
      rw [keep i.val (by have := i.isLt; omega)]
      change ((List.ofFn x) ++ [A, B]).getD i.val false = _
      have hRaw : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
      rw [List.getD_append _ _ _ _ hRaw, List.getD_eq_getElem _ _ hRaw, List.getElem_ofFn]
    have hA : W.getD 42 false = A := by
      rw [keep 42 (by decide)]
      change ((List.ofFn x) ++ [A, B]).getD 42 false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    have hB : W.getD 43 false = B := by
      rw [keep 43 (by decide)]
      change ((List.ofFn x) ++ [A, B]).getD 43 false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    let s1 := A || B
    let s2 := s1 || x 16
    let s3 := x 21 && s2
    let W1 := W ++ [s1]
    let W2 := W1 ++ [s2]
    let W3 := W2 ++ [s3]
    have hS1 : W1.length = r + 1 := by simp [W1, hWlen]
    have hS2 : W2.length = r + 2 := by simp [W2, hS1]
    have hS3 : W3.length = r + 3 := by simp [W3, hS2]
    have first : st W g1 = W1 := by
      change W ++ [(W.getD 42 false || (W.getD 43 false || false))] = _
      simp only [hA, hB, Bool.or_false, W1, s1]
    have second : st W1 g2 = W2 := by
      have h0 : W1.getD r false = s1 := atLast W _ _ hWlen
      have h16 : W1.getD 16 false = x 16 := by
        change (W ++ [s1]).getD 16 false = _
        rw [List.getD_append _ _ _ _ (by rw [hWlen]; dsimp [r]; omega)]
        exact bit 16
      change W1 ++ [(W1.getD r false || (W1.getD 16 false || false))] = _
      simp only [h0, h16, Bool.or_false, W2, s2]
    have third : st W2 g3 = W3 := by
      have h0 : W2.getD (r + 1) false = s2 := atLast W1 _ _ hS1
      have h21 : W2.getD 21 false = x 21 := by
        have hlt1 : 21 < W1.length := by rw [hS1]; dsimp [r]; omega
        change (W1 ++ [s2]).getD 21 false = _
        rw [List.getD_append _ _ _ _ hlt1]
        change (W ++ [s1]).getD 21 false = _
        rw [List.getD_append _ _ _ _ (by rw [hWlen]; dsimp [r]; omega)]
        exact bit 21
      change W2 ++ [(W2.getD 21 false && (W2.getD (r + 1) false && true))] = _
      simp only [h0, h21, Bool.and_true, W3, s3]
    have fourth : st W3 g4 = W3 ++ [E.eval X || s3] := by
      have h0 : W3.getD (r + 2) false = s3 := atLast W2 _ _ hS2
      have hOld : W3.getD E.output false = E.eval X := by
        change (W2 ++ [s3]).getD E.output false = _
        rw [List.getD_append _ _ _ _ (by rw [hS2]; omega)]
        change (W1 ++ [s2]).getD E.output false = _
        rw [List.getD_append _ _ _ _ (by rw [hS1]; omega)]
        change (W ++ [s1]).getD E.output false = _
        rw [List.getD_append _ _ _ _ (hWlen.symm ▸ hBound)]
        rfl
      change W3 ++ [(W3.getD E.output false || (W3.getD (r + 2) false || false))] = _
      simp only [h0, hOld, Bool.or_false]
    have hLine : s3 = linePart x := by
      simp only [s3, s2, s1, A, B, linePart, pointSet, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_assoc]
    change ((E.gates ++ tailGates).foldl st X).getD (r + 3) false = _
    rw [List.foldl_append]
    change (tailGates.foldl st W).getD (r + 3) false = _
    simp only [tailGates, List.foldl_cons, List.foldl_nil, first, second, third, fourth]
    rw [atLast _ _ _ hS3, hLine, heEval (List.ofFn x) (by simp) A B]
  refine ⟨(1 : Fin 42), (4 : Fin 43), (14 : Fin 43), C, Or.inl rfl,
    by decide, by decide, by decide, ?_, cMon, cRead, cSize, ?_⟩
  · have counts : ∀ i : Fin 42, ([0, 1, 4, 14] : List ℕ).count i.val = 1 →
        i.val ∈ ([0, 1, 4, 14] : List ℕ) := by decide +kernel
    intro i hi
    obtain ⟨g, hg, hgi⟩ := heInputs i.val i.isLt (hdInputs i (counts i hi))
    exact ⟨g, List.mem_append_left _ hg, hgi⟩
  · intro x
    let y : Fin 43 → Bool := Fin.lastCases (x 0 || x 1) x
    have h4 : y 4 = x 4 := rfl
    have h14 : y 14 = x 14 := rfl
    change C.eval (List.ofFn (Fin.lastCases (y 4 || y 14) y)) = true ↔ _
    rw [ofFnLast, h4, h14]
    change C.eval (List.ofFn (Fin.lastCases (x 0 || x 1) x) ++ [x 4 || x 14]) = true ↔ _
    rw [ofFnLast, List.append_assoc]
    change C.eval (List.ofFn x ++ [x 0 || x 1, x 4 || x 14]) = true ↔ _
    rw [evalC x, hor, hdEval x]
    have hLine : linePart x = true ↔ x 21 = true ∧ ∃ p ∈ pointSet, x p = true := by
      change (x 21 && pointSet.any x) = true ↔ _
      rw [hand, List.any_eq_true]
    rw [hLine]
    constructor
    · rintro (⟨u, v, ⟨hu, hv, he⟩, hp, hl⟩ | ⟨hl, u, hu, hp⟩)
      · exact ⟨u, v, ⟨hu, Nat.le_of_lt hv, he⟩, hp, hl⟩
      · obtain ⟨hb, he⟩ := (pointTest u).mpr hu
        exact ⟨u, (21 : Fin 42), ⟨hb, by decide, he⟩, hp, hl⟩
    · rintro ⟨u, v, ⟨hu, hv, he⟩, hp, hl⟩
      by_cases h : v.val = 21
      · have hv' : v = (21 : Fin 42) := Fin.ext h
        subst v
        exact Or.inr ⟨hl, u, (pointTest u).mp ⟨hu, he⟩, hp⟩
      · exact Or.inl ⟨u, v, ⟨hu, by omega, he⟩, hp, hl⟩
