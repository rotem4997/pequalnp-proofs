import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves
open PEqualNP.TopForm PEqualNP.HeptadCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1963_733
    (hErase : ∀ (C : Circuit) (j p : ℕ),
      Monotone2 C → ReadsBack 26 C → j < C.gates.length →
      (gateAt C j).op = GateOp.and → p ∈ (gateAt C j).inputs →
      let D := eraseGate 26 C j p
      Monotone2 D ∧ ReadsBack 26 D ∧ D.size < C.size ∧
      ∀ x : List Bool, x.length = 26 →
        (C.eval x = true → D.eval x = true) ∧
        ((C.wires x).getD (26+j) false = (C.wires x).getD p false → D.eval x = C.eval x))
    (hHard :
      let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ andPairs 26 C →
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
        (∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false) →
        (∀ j < C.size, (gateAt C j).op = GateOp.and →
          ∀ p ∈ (gateAt C j).inputs, ∃ Q ∈ quadrangles singerLines3,
            (C.wires (N Q)).getD (26+j) false ≠ (C.wires (N Q)).getD p false) →
        64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro D Correct Nested C hMono hBack hC hSize hNested hStrict hPairs
  change (∀ p l : Fin 13, p - l ∈ D → C.eval
    (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧ _ at hC
  let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
  let N' (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
  have hInc : ∀ p l : Fin 13, p - l ∈ D ↔ p ∈ singerLines3 l := by decide
  have hGood (Q : Finset (Fin 13)) :
      Q ∈ quadrangles singerLines3 ↔
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2 := by
    have heq (k : Fin 13) : Q ∩ singerLines3 k = Q.filter (fun u => u - k ∈ D) := by
      ext u
      simp [hInc u k]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
        (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, heq]
  have hInputs (Q : Finset (Fin 13)) : N Q = N' Q := by
    have hTail : List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change (v ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun l => Disjoint (singerLines3 l) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← hInc]
      constructor
      · intro h r hr hi
        exact h hi hr
      · intro h r hi hr
        exact h r hr hi
    exact congrArg (fun tail : List Bool => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++ tail) hTail
  have hNeg (Q : Finset (Fin 13)) (hQ : Q ∈ quadrangles singerLines3) :
      C.eval (N Q) = false := by
    rw [hInputs]
    exact hC.2 Q ((hGood Q).mp hQ).1 ((hGood Q).mp hQ).2
  have hAO : IsAO2 26 C := by
    refine ⟨?_, hBack, fun g hg => (hStrict g hg).1⟩
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hMono g hg).1
  let Essential := ∀ j < C.size, (gateAt C j).op = GateOp.and →
    ∀ p ∈ (gateAt C j).inputs, ∃ Q ∈ quadrangles singerLines3,
      (C.wires (N Q)).getD (26+j) false ≠ (C.wires (N Q)).getD p false
  by_cases hE : Essential
  · have hl := hHard C hAO (fun g hg => (hStrict g hg).2) hPairs
        (fun p l h => hC.1 p l ((hInc p l).mpr h)) hNeg hE
    omega
  · unfold Essential at hE
    push Not at hE
    obtain ⟨j, hj, hOp, p, hp, hSame⟩ := hE
    obtain ⟨hm, hb, hs, hEval⟩ := hErase C j p hMono hBack hj hOp hp
    refine ⟨eraseGate 26 C j p, hm, hb, ?_, hs⟩
    constructor
    · intro u v huv
      exact (hEval _ (by simp)).1 (hC.1 u v huv)
    · intro Q hCard hIntersect
      have hQ := (hGood Q).mpr ⟨hCard, hIntersect⟩
      change (eraseGate 26 C j p).eval (N' Q) = false
      rw [← hInputs]
      exact ((hEval (N Q) (by simp [N])).2 (hSame Q hQ)).trans (hNeg Q hQ)
