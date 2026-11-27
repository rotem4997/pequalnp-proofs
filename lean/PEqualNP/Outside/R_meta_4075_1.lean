import PEqualNP.Defs

-- Gate elimination cut of L-meta-4075 (AND-top case, first gate AND(x0, x1) or AND(x0, x2)).
-- Fix y := false for y = 0 or y = (1 or 2): the extra input x0 && x(1|2) becomes false too.
-- Child 1 is L-meta-670 verbatim (Petersen minus a vertex needs 16 gates).
-- Child 2 (elimination): if 3 gates of D read y or the extra input 10, fixing y := false kills
-- them, leaving at most 14 gates; with the top AND that is a 15-gate circuit for Petersen minus y,
-- which is Petersen minus 9 after an automorphism moving y to 9.
-- Child 3 (residual): the step itself when both y = 0 and y = (1 or 2) have at most 2 such readers.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4075_1
    (h670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (hElim : ∀ (b : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (u v y : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 → (y = 0 ∨ y = if b = true then 1 else 2) →
      3 ≤ (D.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains y || (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 10).length →
      (∀ x : Fin 10 → Bool, ((D.wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD u false && (D.wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD v false) = [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))) →
      PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))) 15)
    (hLow : ∀ (b : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      (D.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 0 || (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 10).length ≤ 2 →
      (D.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains (if b = true then 1 else 2) || (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 10).length ≤ 2 →
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10));
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [x 0 && if b = true then x 1 else x 2])).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro x1 x2 x3 x4 hfan hsize x7 x8 H1 H2 H3
  have pc10 : ∀ x : Fin 10 → Bool, ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))) = x7 x := by
    intro x
    have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
        (a0 && a1 || (a1 && a2 || (a2 && a3 || (a3 && a4 || (a4 && a0 || (a0 && a5 || (a1 && a6 || (a2 && a7 || (a3 && a8 || (a4 && a9 || (a5 && a7 || (a7 && a9 || (a9 && a6 || (a6 && a8 || (a8 && a5 || false))))))))))))))) =
        (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 || a4 && a9 || a5 && a7 || a7 && a9 || a9 && a6 || a6 && a8 || a8 && a5) := by
      decide
    exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
  have pc9 : (fun x : Fin 9 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
        (a0 && a1 || (a1 && a2 || (a2 && a3 || (a3 && a4 || (a4 && a0 || (a0 && a5 || (a1 && a6 || (a2 && a7 || (a3 && a8 || (a5 && a7 || (a6 && a8 || (a8 && a5 || false)))))))))))) =
        ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
      decide
    exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  -- if the conclusion fails, the two wires meet exactly in the Petersen function
  have eqOf : (¬ ∃ x12 : Fin 10 → Bool, x7 x12 = false ∧ x8 x12 x3 = true ∧ x8 x12 x4 = true) →
      ∀ x : Fin 10 → Bool, (x8 x x3 && x8 x x4) = ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat _ (e / 10)) && x (Fin.ofNat _ (e % 10))) := by
    intro hneg x
    rw [pc10 x]
    cases hP : x7 x with
    | true =>
      obtain ⟨h1, h2⟩ := H3 x hP
      rw [h1, h2]; rfl
    | false =>
      cases h1 : x8 x x3 <;> cases h2 : x8 x x4
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨x, hP, h1, h2⟩ hneg
  by_cases c0 : (x2.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 0 || (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 10).length ≤ 2
  · by_cases cp : (x2.gates.filter fun g => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains (if x1 = true then 1 else 2) || (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains 10).length ≤ 2
    · obtain ⟨x, hx1, hx2, hx3⟩ := hLow x1 x2 x3 x4 hfan hsize c0 cp H1 H2
        (fun x hx => H3 x (by rw [← pc10 x]; exact hx))
      exact ⟨x, by rw [← pc10 x]; exact hx1, hx2, hx3⟩
    · by_contra hneg
      have hc := hElim x1 x2 x3 x4 (if x1 = true then 1 else 2) hfan hsize (Or.inr rfl) (by omega) (eqOf hneg)
      rw [pc9] at hc
      exact h670 hc
  · by_contra hneg
    have hc := hElim x1 x2 x3 x4 0 hfan hsize (Or.inl rfl) (by omega) (eqOf hneg)
    rw [pc9] at hc
    exact h670 hc
