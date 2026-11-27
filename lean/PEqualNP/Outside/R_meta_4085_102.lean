import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4085_102
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (18 : ℕ) →
      (3 : ℕ) ≤ Set.ncard {j : Fin C.size | ∃ (w : ℕ), (w = (0 : ℕ) ∨ w = (10 : ℕ) ∨ ∃ (i : Fin C.size), w = (11 : ℕ) + ↑i ∧ (((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((C.gates.get i).inputs.head? = some (0 : ℕ) ∨ (C.gates.get i).inputs.head? = some (10 : ℕ))) ∨ ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ (C.gates.get i).inputs) ∨ ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (10 : ℕ) ∈ (C.gates.get i).inputs))) ∧ ((C.gates.get j).inputs.head? = some w ∨ ((C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ (C.gates.get j).inputs))} →
      PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ)
        (fun (y : Fin (9 : ℕ) → Bool) => C.eval (Bool.false :: (List.ofFn y ++ [Bool.true]))) (15 : ℕ))
    (h2 : ¬ PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ)
      (fun (x6 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (9 : ℕ)) (x8 : Fin (9 : ℕ)),
        x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧
        ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ),
          (104 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) (15 : ℕ))
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) →
      Set.ncard {j : Fin x1.size | ∃ (w : ℕ), (w = (0 : ℕ) ∨ w = (10 : ℕ) ∨ ∃ (i : Fin x1.size), w = (11 : ℕ) + ↑i ∧ (((x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((x1.gates.get i).inputs.head? = some (0 : ℕ) ∨ (x1.gates.get i).inputs.head? = some (10 : ℕ))) ∨ ((x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ (x1.gates.get i).inputs) ∨ ((x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (10 : ℕ) ∈ (x1.gates.get i).inputs))) ∧ ((x1.gates.get j).inputs.head? = some w ∨ ((x1.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ (x1.gates.get j).inputs))} ≤ (2 : ℕ) →
      (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin x1.size), ∀ x10 ∈ (x1.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (x1.output ∈ x5 → x1.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (x1.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) →
      ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin x1.size), ∀ x10 ∈ (x1.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (x1.output ∈ x5 → x1.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (x1.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5 := by
  intro x1 hF hs hH
  by_cases hk : (3 : ℕ) ≤ Set.ncard {j : Fin x1.size | ∃ (w : ℕ), (w = (0 : ℕ) ∨ w = (10 : ℕ) ∨ ∃ (i : Fin x1.size), w = (11 : ℕ) + ↑i ∧ (((x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((x1.gates.get i).inputs.head? = some (0 : ℕ) ∨ (x1.gates.get i).inputs.head? = some (10 : ℕ))) ∨ ((x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ (x1.gates.get i).inputs) ∨ ((x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (10 : ℕ) ∈ (x1.gates.get i).inputs))) ∧ ((x1.gates.get j).inputs.head? = some w ∨ ((x1.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ (x1.gates.get j).inputs))}
  · by_contra hall
    push_neg at hall
    apply h2
    obtain ⟨D, hDF, hDs, hDe⟩ := h1 x1 hF hs hk
    refine ⟨D, hDF, hDs, fun y => ?_⟩
    rw [hDe y]
    have hy := hall (Fin.cons Bool.false y)
    have hlist : List.ofFn (Fin.cons Bool.false y : Fin 10 → Bool) ++
        [!(Fin.cons Bool.false y : Fin 10 → Bool) 0] = Bool.false :: (List.ofFn y ++ [Bool.true]) := by
      simp
    rw [hlist] at hy
    beta_reduce
    rw [hy]
    have key : ∀ a b : Fin 9,
        (([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ),
          (104 : ℕ), (208 : ℕ)].getD ((a.succ : Fin 10) : ℕ) (0 : ℕ)).testBit ((b.succ : Fin 10) : ℕ)) =
        (([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ),
          (104 : ℕ)].getD (a : ℕ) (0 : ℕ)).testBit (b : ℕ)) := by
      decide
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      cases a using Fin.cases with
      | zero => simp at ha
      | succ a =>
        cases b using Fin.cases with
        | zero => simp at hb
        | succ b =>
          refine ⟨a, b, by simpa using ha, by simpa using hb, ?_⟩
          rw [← key a b]
          exact hab
    · rintro ⟨a, b, ha, hb, hab⟩
      refine ⟨a.succ, b.succ, by simpa using ha, by simpa using hb, ?_⟩
      rw [key a b]
      exact hab
  · exact h3 x1 hF hs (by omega) hH
