import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2915_1
    (binary : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      13 ≤ D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op))
    (signed : ∀ (j : Fin 9), 1 ≤ j.val → j.val ≤ 4 →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size = 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, !x j]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     (1 : ℕ) ≤ x1.headD (10 : ℕ) ∧ x1.headD (10 : ℕ) ≤ (4 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro xs _ hr C fan size
  cases xs with
  | nil => simp at hr
  | cons i rest =>
    change 1 ≤ i ∧ i ≤ 4 at hr
    let j : Fin 9 := ⟨i, by omega⟩
    have read (x : Fin 9 → Bool) : (List.ofFn x ++ [!x 0]).getD i false = x j := by
      have hi : i < (List.ofFn x).length := by simp; omega
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hi]
      exact List.getElem_ofFn hi
    let n0 : PEqualNP.CircuitLowerBounds.Gate := ⟨.not, [0]⟩
    let nj : PEqualNP.CircuitLowerBounds.Gate := ⟨.not, [i]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨n0 :: nj :: C.gates, C.output⟩
    have dfan : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      change g ∈ n0 :: nj :: C.gates at hg
      rcases List.mem_cons.mp hg with rfl | h
      · simp [n0]
      rcases List.mem_cons.mp h with rfl | h
      · simp [nj]
      exact fan g h
    by_contra! correct
    have ev (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [!x 0, !x j]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
      have h := Classical.not_not.mp (correct x)
      change C.eval ((List.ofFn x ++ [!x 0]) ++ [!((List.ofFn x ++ [!x 0]).getD i false)]) = _ at h
      rw [read] at h
      exact h
    have deval (x : Fin 9 → Bool) : D.eval (List.ofFn x) =
        C.eval (List.ofFn x ++ [!x 0, !x j]) := by
      let bits := List.ofFn x
      change C.eval ((bits ++ [!(bits.getD 0 false)]) ++
        [!((bits ++ [!(bits.getD 0 false)]).getD i false)]) = _
      dsimp only [bits]
      have first : (List.ofFn x).getD 0 false = x 0 := by
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp
      rw [first, read]
      rfl
    have count := binary D dfan (fun x => (deval x).trans (ev x))
    let pred (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
      PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op
    change 13 ≤ C.gates.countP pred at count
    change C.gates.length ≤ 13 at size
    have bound := List.countP_le_length (l := C.gates) (p := pred)
    have exactCount : C.gates.countP pred = C.gates.length := by omega
    have mono : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨basis, arity⟩ := fan g hg
      have good := List.countP_eq_length.mp exactCount g hg
      refine ⟨?_, arity⟩
      rcases basis with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · change g.op = .not at h
        simp [pred, h] at good
    obtain ⟨x, wrong⟩ := signed j hr.1 hr.2 C mono (by change C.gates.length = 13; omega)
    exact wrong (ev x)
