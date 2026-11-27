import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete point 0. The circuit outputs the residual edge function and exposes a second wire.
-- On residual false inputs the wire reads the OR of the four lines through point 0.
-- On residual true inputs it is unrestricted. The two outputs may share gates.
-- The new input at the front restores point 0 with one AND and one OR.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_650_517 :
    (∃ (D : Circuit) (j : ℕ), Monotone2 D ∧ D.size ≤ 61 ∧
      D.output < 25 + D.size ∧ j < 25 + D.size ∧ ∀ y : Fin 25 → Bool,
        let I := fun i k : Fin 25 => i.val < 12 ∧ 12 ≤ k.val ∧
          (i.val + k.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
        let hit := D.eval (List.ofFn y)
        (hit = true ↔ ∃ i k : Fin 25, I i k ∧ y i = true ∧ y k = true) ∧
        (hit = false → (D.wires (List.ofFn y)).getD j false = (y 12 || y 13 || y 15 || y 21))) →
    (∀ (D : Circuit) (j : ℕ), Monotone2 D → D.output < 25 + D.size → j < 25 + D.size →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧ ∀ (b : Bool) (y : Fin 25 → Bool),
        C.eval (b :: List.ofFn y) = (D.eval (List.ofFn y) || (b && (D.wires (List.ofFn y)).getD j false))) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro small attach
  obtain ⟨D, j, hD, budget, hOut, hj, reads⟩ := small
  obtain ⟨C, hC, cost, eval⟩ := attach D j hD hOut hj
  refine ⟨C, hC, by omega, ?_⟩
  let E : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  let I := fun i k : Fin 25 => i.val < 12 ∧ 12 ≤ k.val ∧
    (i.val + k.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  have row0 : ∀ v : Fin 26, (0, v.val) ∈ E ↔ v = 13 ∨ v = 14 ∨ v = 16 ∨ v = 22 := by decide
  have col0 : ∀ i : Fin 25, (i.succ.val, 0) ∉ E := by decide
  have rest : ∀ i k : Fin 25, (i.succ.val, k.succ.val) ∈ E ↔ I i k := by decide
  intro x
  let y := fun i : Fin 25 => x i.succ
  let R := ∃ i k : Fin 25, I i k ∧ y i = true ∧ y k = true
  let N := y 12 || y 13 || y 15 || y 21
  have graph : (∃ u v : Fin 26, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ↔
      R ∨ (x 0 = true ∧ N = true) := by
    constructor
    · rintro ⟨u, v, mem, hu, hv⟩
      cases u using Fin.cases with
      | zero =>
        refine Or.inr ⟨hu, ?_⟩
        change (x 13 || x 14 || x 16 || x 22) = true
        rcases (row0 v).mp mem with rfl | rfl | rfl | rfl <;> simp [hv]
      | succ i =>
        cases v using Fin.cases with
        | zero => exact False.elim (col0 i mem)
        | succ k => exact Or.inl ⟨i, k, (rest i k).mp mem, hu, hv⟩
    · rintro (⟨i, k, hik, hi, hk⟩ | ⟨h0, hn⟩)
      · exact ⟨i.succ, k.succ, (rest i k).mpr hik, hi, hk⟩
      · change (x 13 || x 14 || x 16 || x 22) = true at hn
        have make (v : Fin 26) (h : v = 13 ∨ v = 14 ∨ v = 16 ∨ v = 22) (hv : x v = true) :
            ∃ u v : Fin 26, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true :=
          ⟨0, v, (row0 v).mpr h, h0, hv⟩
        simp only [Bool.or_eq_true_iff] at hn
        rcases hn with ((h | h) | h) | h
        · exact make 13 (by decide) h
        · exact make 14 (by decide) h
        · exact make 16 (by decide) h
        · exact make 22 (by decide) h
  change C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
  rw [graph, List.ofFn_succ, eval]
  obtain ⟨detect, tap⟩ := reads y
  change D.eval (List.ofFn y) = true ↔ R at detect
  change D.eval (List.ofFn y) = false → (D.wires (List.ofFn y)).getD j false = N at tap
  change (D.eval (List.ofFn y) || (x 0 && (D.wires (List.ofFn y)).getD j false)) = true ↔ _
  cases h : D.eval (List.ofFn y) with
  | true => simp [detect.mp h]
  | false =>
    have hr : ¬ R := fun r => Bool.noConfusion (h.symm.trans (detect.mpr r))
    rw [tap h]
    simp only [Bool.false_or, Bool.and_eq_true, hr, false_or]
