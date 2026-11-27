import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2640_3 :
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
    ¬x2.Colorable (2 : ℕ) →
    (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
    (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
    (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
    (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
    PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →
    (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔
      (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
    ∃ (x12 : Fin x1) (x13 : Fin x1),
      x2.Adj x12 x13 ∧
      ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧
        (x14 (0 : ℕ)).size ≤ x4.size ∧
        PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧
        ∀ x15 < (3 : ℕ),
          ∃ (x17 : ℕ) (x18 : ℕ),
            x17 < (x14 x15).size ∧
            (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧
            x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧
            ((∀ (x19 : Fin x1 → Bool),
                have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update x19 x12 Bool.false));
                x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨
              (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs)) →
  (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x12 x13 : Fin x1) (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
    x2.Adj x12 x13 →
    PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) →
    (∀ x15 < (3 : ℕ),
      ∃ (x17 : ℕ) (x18 : ℕ),
        x17 < (x14 x15).size ∧
        (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧
        x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧
        ((∀ (x19 : Fin x1 → Bool),
            have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update x19 x12 Bool.false));
            x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨
          (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs)) →
    ∃ (y : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
      y (0 : ℕ) = x14 (3 : ℕ) ∧
      ∀ x15 < (4 : ℕ),
        ∃ (x17 : ℕ) (x18 : ℕ),
          x17 < (y x15).size ∧
          (x18 < x1 + x17 ∨ x1 + (y x15).size ≤ x18) ∧
          y (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (y x15) x17 x18 ∧
          ((∀ (x19 : Fin x1 → Bool),
              have x20 : List Bool := (y x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));
              x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨
            (y x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (y x15).gates, x1 + x17 ∉ x19.inputs)) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  intro h1 h2 n G A D hnc hdeg hgirth hiso hedge hmin hsem
  obtain ⟨u, v, huv, C1, hfan, hsz, hfun, hst1⟩ :=
    h1 n G A D hnc hdeg hgirth hiso hedge hmin hsem
  obtain ⟨C2, hC20, hst2⟩ := h2 n G u v C1 huv hfan hst1
  refine ⟨u, v, huv, fun i => if i ≤ 3 then C1 i else C2 (i - 3), hfan, hsz, hfun, ?_⟩
  intro i hi
  by_cases hlt : i < 3
  · obtain ⟨m, p, hm, hp, heq, hcond⟩ := hst1 i hlt
    have hi1 : i ≤ 3 := by omega
    have hi2 : i + 1 ≤ 3 := by omega
    refine ⟨m, p, ?_, ?_, ?_, ?_⟩
    · simpa [hi1] using hm
    · simpa [hi1] using hp
    · simpa [hi1, hi2] using heq
    · rcases hcond with hval | hdead
      · left
        intro x
        have hne : u ≠ v := G.ne_of_adj huv
        have hcomm : Function.update (Function.update x u false) v false =
            Function.update (Function.update x v false) u false :=
          Function.update_comm hne false false x
        simpa [hi1, hcomm] using hval (Function.update x v false)
      · right
        simpa [hi1] using hdead
  · have hge : 3 ≤ i := by omega
    have hj : i - 3 < 4 := by omega
    obtain ⟨m, p, hm, hp, heq, hcond⟩ := hst2 (i - 3) hj
    have hCi : (if i ≤ 3 then C1 i else C2 (i - 3)) = C2 (i - 3) := by
      by_cases h3 : i = 3
      · subst h3; simp [hC20]
      · have : ¬ i ≤ 3 := by omega
        simp [this]
    have hCi1 : (if i + 1 ≤ 3 then C1 (i + 1) else C2 (i + 1 - 3)) = C2 (i - 3 + 1) := by
      have : ¬ i + 1 ≤ 3 := by omega
      have hsub : i + 1 - 3 = i - 3 + 1 := by omega
      simp [this, hsub]
    refine ⟨m, p, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [hCi]; exact hm
    · dsimp only; rw [hCi]; exact hp
    · dsimp only; rw [hCi, hCi1]; exact heq
    · dsimp only; rw [hCi]; exact hcond
