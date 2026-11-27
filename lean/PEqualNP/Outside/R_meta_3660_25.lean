import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- Prepending the two supplied inverters makes the binary-gate lower bound applicable.
-- Once all thirteen suffix gates must be binary, the remaining question is a fixed CNF.
-- Its rows are the minimal positive and maximal negative legal rows in the bitwise order.
theorem PEqualNP.Outside.R_meta_3660_25
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.gates.countP (fun g => !g.op.eval [false]))
    (encode : ∀ (rows : List ℕ) (g : ℕ → Bool) (C : Circuit),
      (∀ r ∈ rows, r < 2048) → Monotone2 C → C.size ≤ 13 →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin 11 => r.testBit i.val)) = g r) →
      FormulaSat (enc 11 13 g rows))
    (unsat : ¬ FormulaSat (enc 11 13
      (fun r : ℕ => ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any fun e => r &&& e == e)
      [7, 13, 21, 37, 69, 133, 261, 325, 518, 524, 628, 644, 788, 804, 836, 1027, 1041, 1057, 1225, 1289, 1345, 1409, 1560, 1578, 1586, 1602, 1640, 1648, 1674, 1696, 1736, 1744, 1800, 1824, 1856, 1938])) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), !x4 (2 : Fin (9 : ℕ))]) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C fan size
  by_contra! agrees
  let B : Circuit := ⟨⟨.not, [0]⟩ :: ⟨.not, [2]⟩ :: C.gates, C.output⟩
  have bfan : FanInTwo B := by
    intro g member
    change g ∈ _ :: _ :: C.gates at member
    rcases List.mem_cons.mp member with rfl | member
    · simp
    rcases List.mem_cons.mp member with rfl | member
    · simp
    exact fan g member
  have same (x : Fin 9 → Bool) : B.eval (List.ofFn x) =
      C.eval (List.ofFn x ++ [!x 0, !x 2]) := by
    have v0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
    have v2 : (List.ofFn x ++ [!x 0]).getD 2 false = x 2 := by
      rw [List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    change C.eval ((List.ofFn x ++ [!((List.ofFn x).getD 0 false)]) ++
      [!((List.ofFn x ++ [!((List.ofFn x).getD 0 false)]).getD 2 false)]) = _
    rw [v0, v2, List.append_assoc]
    rfl
  have lower := binaryBound B bfan (fun x => (same x).trans (agrees x))
  change 13 ≤ C.gates.countP (fun g => !g.op.eval [false]) at lower
  have allPass : C.gates.countP (fun g => !g.op.eval [false]) = C.gates.length := by
    change C.gates.length ≤ 13 at size
    exact le_antisymm (List.countP_le_length) (size.trans lower)
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨op, arity⟩ := fan g hg
    refine ⟨?_, arity⟩
    have passes := (List.countP_eq_length.mp allPass) g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    rcases op with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at passes
      contradiction
  let rows : List ℕ := [7, 13, 21, 37, 69, 133, 261, 325, 518, 524, 628, 644, 788, 804, 836, 1027, 1041, 1057, 1225, 1289, 1345, 1409, 1560, 1578, 1586, 1602, 1640, 1648, 1674, 1696, 1736, 1744, 1800, 1824, 1856, 1938]
  let truth := (fun r : ℕ => ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ).any fun e => r &&& e == e)
  let bits (r : ℕ) (i : Fin 9) := r.testBit i.val
  have legal : ∀ r ∈ rows,
      List.ofFn (fun i : Fin 11 => r.testBit i.val) =
        List.ofFn (bits r) ++ [!(bits r 0), !(bits r 2)] := by decide
  have labels : ∀ r ∈ rows, (let x := bits r; x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = truth r := by decide
  apply unsat
  apply encode rows truth C (by decide) mono size
  intro r hr
  rw [legal r hr]
  exact (agrees (bits r)).trans (labels r hr)
