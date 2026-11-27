import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A repeated input label forces live AND depth at least two when the singleton is rejected.
-- It suffices to convert circuits that have both sharing and this live depth.
theorem PEqualNP.Outside.R_meta_2223_642
    (depthOfRepeatedLabel : ∀ (n : ℕ) (C : Circuit) (i : Fin n), PEqualNP.TopForm.IsAO2 n C →
      C.eval (List.ofFn (fun j : Fin n => decide (j = i))) = false →
      2 ≤ C.lineDeg n {i.val} →
      2 ≤ (SingleLevel.andDepths C n).getD C.output 0)
    (sharedDeep :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop :=
        fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
        fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧
          (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 →
            (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
              ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧
          ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔
            ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧
              x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
        fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4))
          (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)),
        x2 x4 → x1 x5 x6 →
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} →
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} →
         (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x4 14).getD x4.output 0 → ¬ x3 x4 →
        ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧
          (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧
          (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6}) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop :=
      fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
    have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
      fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧
        (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 →
          (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧
        ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔
          ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧
            x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
    have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
      fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4))
        (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
    ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)),
      x2 x4 → x1 x5 x6 →
       (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} →
       (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} →
       ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧
        (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧
        (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  dsimp only
  intro C p l hC hInc hp hl
  by_cases hTree :
    ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
  · exact ⟨C, hC, hTree, hp, hl⟩
  obtain ⟨hSize, hGates, hCorrect⟩ := hC
  have gates (g : Gate) (hg : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨hOp, a, b, hIn, _⟩ := hGates j g hj
    exact ⟨hOp, by simp [hIn]⟩
  have shape : PEqualNP.TopForm.IsAO2 14 C := by
    refine ⟨fun g hg => (gates g hg).1, ?_, fun g hg => (gates g hg).2⟩
    intro j hj w hw
    change j < C.gates.length at hj
    obtain ⟨_, a, b, hIn, _, ha, hb⟩ := hGates j C.gates[j] (List.getElem?_eq_getElem hj)
    change w ∈ (C.gates.getD j _).inputs at hw
    rw [List.getD_eq_getElem _ _ hj, hIn] at hw
    rcases List.mem_cons.mp hw with h | h
    · exact h ▸ ha
    · exact (List.mem_singleton.mp h) ▸ hb
  have singleton (i : Fin 14) : C.eval (List.ofFn (fun j : Fin 14 => decide (j = i))) = false := by
    cases h : C.eval (List.ofFn (fun j : Fin 14 => decide (j = i))) with
    | false => rfl
    | true =>
      obtain ⟨u, v, _, hu, hv⟩ := (hCorrect _).mp h
      have he := (of_decide_eq_true hu).trans (of_decide_eq_true hv).symm
      have hu' : (Fin.castAdd 7 u).val < 7 := u.isLt
      have hv' : 7 ≤ (Fin.natAdd 7 v).val := Nat.le_add_right _ _
      have he' := congrArg Fin.val he
      omega
  exact sharedDeep C p l ⟨hSize, hGates, hCorrect⟩ hInc hp hl
    (depthOfRepeatedLabel 14 C (Fin.castAdd 7 p) shape (singleton _) hp) hTree
