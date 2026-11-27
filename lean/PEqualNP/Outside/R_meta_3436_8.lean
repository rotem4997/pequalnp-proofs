import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3436_8
  (mixed :
    let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let W := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0)]
    let row := fun b : BitVec 9 => fun i : Fin 9 => b.getLsbD i.val
    ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ b : BitVec 9,
      let x := row b
      C.eval (W x ++ [x i || !(x 0)]) ≠ F x)
  (raw :
    let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let W := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0)]
    let row := fun b : BitVec 9 => fun i : Fin 9 => b.getLsbD i.val
    ∀ a b : Fin 9, 11*a.val + b.val ∈ ([1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 25, 26, 28, 29, 30, 37, 39, 50, 73] : List Nat) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ z : BitVec 9,
      let x := row z
      C.eval (W x ++ [x a || x b]) ≠ F x) :
  ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)] →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  let W := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0)]
  let row := fun b : BitVec 9 => fun i : Fin 9 => b.getLsbD i.val
  let P : List Nat := [1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 25, 26, 28, 29, 30, 37, 39, 50, 73]
  let Q : List Nat := [1, 2, 3, 4, 6, 9, 13, 14, 15, 16, 17, 18, 19, 20, 25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 53, 73, 75]
  have table : ∀ i j : Fin 11, (!Q.contains (11*i.val+j.val) ||
      (decide (i.val < 9) && (j.val == 9 || (decide (j.val < 9) && P.contains (11*i.val+j.val))))) = true := by decide +kernel
  have rd (x : Fin 9 → Bool) (a : Fin 9) :
      (W x).getD a.val false = x a := by
    change (List.ofFn x ++ [!(x 0)]).getD a.val false = x a
    rw [List.getD_append _ _ _ _ (by simpa using a.isLt),List.getD_eq_getElem _ _ (by simpa using a.isLt),
      List.getElem_ofFn]
  have ninth (x : Fin 9 → Bool) : (W x).getD 9 false = !(x 0) := rfl
  intro i j C code fan limit
  have ok : Q.contains (11*i.val+j.val) = true := List.contains_iff_mem.mpr code
  have t := table i j
  simp only [ok,Bool.not_true,Bool.false_or,Bool.and_eq_true_iff,Bool.or_eq_true_iff,
    decide_eq_true_eq,beq_iff_eq,List.contains_iff_mem] at t
  let a : Fin 9 := ⟨i.val,t.1⟩
  have counter : ∃ b : BitVec 9,
      C.eval (W (row b) ++ [(W (row b)).getD i.val false || (W (row b)).getD j.val false]) ≠ F (row b) := by
    rcases t.2 with h | ⟨bound,belongs⟩
    · obtain ⟨z,miss⟩ := mixed a C fan limit
      refine ⟨z,?_⟩
      rw [h,ninth,show (W (row z)).getD i.val false = row z a from rd _ a]
      exact miss
    · let b : Fin 9 := ⟨j.val,bound⟩
      obtain ⟨z,miss⟩ := raw a b belongs C fan limit
      refine ⟨z,?_⟩
      rw [show (W (row z)).getD i.val false = row z a from rd _ a,
          show (W (row z)).getD j.val false = row z b from rd _ b]
      exact miss
  obtain ⟨z,hz⟩ := counter
  refine ⟨z,?_⟩
  dsimp only
  intro eq
  apply hz
  refine eq.trans ?_
  dsimp [F,List.any,row] <;> simp only [Bool.or_false,Bool.or_assoc]
