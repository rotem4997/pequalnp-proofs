import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2517_417
    (padding :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ)
        (x : Fin 9 → Bool) (j : ℕ),
        ((⟨C.gates ++ List.replicate k
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ :
            PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD j false =
          (C.wires (List.ofFn x)).getD j false)
    (search :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.gates.length = 15 →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ p q : Fin C.gates.length, p < q ∧ 4 ≤ p.val ∧ p.val ≤ 7 ∧
          (C.gates.get p).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ j : Fin C.gates.length,
            (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p ∨ j = q) →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
            (([18440827511444797640, 18441957826578283724, 18446744073709222136,
              18446744073709485308, 18446744073708175304, 18446744073709551615,
              18446744073709223928, 18446744073709551615] : List ℕ).getD
                (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit
                (PEqualNP.MetaComplexity.tableIndex x % 64)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (4 : ℕ) ≤ ↑x3 ∧ ↑x3 ≤ (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hC hnot hfirst hfun
  by_contra hsize
  change ¬ 16 ≤ C.gates.length at hsize
  have hle : C.gates.length ≤ 15 := by omega
  let extra := List.replicate (15 - C.gates.length)
    (⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ : PEqualNP.CircuitLowerBounds.Gate)
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ extra, C.output⟩
  have hlen : D.gates.length = 15 := by simp [D, extra]; omega
  have hCD : C.gates.length ≤ D.gates.length := by omega
  have hD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    change g ∈ C.gates ++ extra at hg
    rcases List.mem_append.mp hg with h | h
    · exact hC g h
    · have he : g = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := List.eq_of_mem_replicate h
      subst g
      simp
  let liftIndex (i : Fin C.gates.length) : Fin D.gates.length := ⟨i.val, lt_of_lt_of_le i.isLt hCD⟩
  have oldGate (i : Fin C.gates.length) : D.gates.get (liftIndex i) = C.gates.get i := by
    exact List.getElem_append_left i.isLt
  have newGate (i : Fin D.gates.length) (hi : C.gates.length ≤ i.val) :
      (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    change ((C.gates ++ extra)[i.val]'i.isLt).op = _
    rw [List.getElem_append_right hi]
    simp [extra]
  obtain ⟨p, q, hpq, hp4, hp7, hpnot, hqnot, honly⟩ := hnot
  have hnotD : ∃ p q : Fin D.gates.length, p < q ∧ 4 ≤ p.val ∧ p.val ≤ 7 ∧
      (D.gates.get p).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (D.gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      ∀ i : Fin D.gates.length,
        (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = p ∨ i = q := by
    refine ⟨liftIndex p, liftIndex q, hpq, hp4, hp7, ?_, ?_, ?_⟩
    · rw [oldGate, hpnot]
    · rw [oldGate, hqnot]
    · intro i hnoti
      have hi : i.val < C.gates.length := by
        by_contra! h
        have conflict := (newGate i h).symm.trans hnoti
        contradiction
      let j : Fin C.gates.length := ⟨i.val, hi⟩
      have he : liftIndex j = i := Fin.ext rfl
      have hj : (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        rw [← oldGate j, he, hnoti]
      rcases honly j hj with hp | hq
      · left; exact he.symm.trans (congrArg liftIndex hp)
      · right; exact he.symm.trans (congrArg liftIndex hq)
  have sim (x : Fin 9 → Bool) (i : ℕ) :
      (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false :=
    padding C (15 - C.gates.length) x i
  have hDfirst (x : Fin 9 → Bool) :
      (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
    rw [sim]
    exact hfirst _
  obtain ⟨x, hr⟩ := search D hlen hD hnotD hDfirst
  apply hr
  have hEval : D.eval (List.ofFn x) = PEqualNP.MetaComplexity.circuitFun 9 C x :=
    sim x C.output
  rw [hEval, hfun]
  have truth : ∀ v : Fin 9 → Bool,
      (v 0 && v 1 || v 1 && v 2 || v 2 && v 3 || v 3 && v 4 || v 4 && v 0 ||
        v 0 && v 5 || v 1 && v 6 || v 2 && v 7 || v 3 && v 8 ||
        v 5 && v 7 || v 6 && v 8 || v 8 && v 5) =
      (([18440827511444797640, 18441957826578283724, 18446744073709222136,
        18446744073709485308, 18446744073708175304, 18446744073709551615,
        18446744073709223928, 18446744073709551615] : List ℕ).getD
          (PEqualNP.MetaComplexity.tableIndex v / 64) 0).testBit
          (PEqualNP.MetaComplexity.tableIndex v % 64) := by decide
  exact truth x
