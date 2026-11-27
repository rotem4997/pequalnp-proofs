import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2151_659
    (disjointWithNegations : ∀ p ∈ ([(1,2),(1,3),(1,5),(1,6),(1,7),(1,8),(2,3),(2,5),(2,6),(2,7),(2,8),(3,5),(3,6),(3,7),(3,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)] : List (Fin 9 × Fin 9)),
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      2 ≤ D.gates.countP (fun g => g.op.eval [false]) →
      ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (remaining :
      ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ((¬ ∃ a b : Fin 9, a ≠ 0 ∧ a ≠ 4 ∧ b ≠ 0 ∧ b ≠ 4 ∧ a < b ∧
          pins.Perm [a.val, b.val]) ∨
        D.gates.countP (fun g => g.op.eval [false]) < 2) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [GateOp.or.eval (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
    (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) ||
      x3 (4 : Fin (9 : ℕ)))) →
    (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
      x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
      x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
      x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
      x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
      x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
      x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
      x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
      x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
      x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
      x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
      x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  let target (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let preset (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step, List.getD_append _ _ _ _ hi]
  intro C fan first correct second
  obtain ⟨gs, o⟩ := C
  rcases gs with _ | ⟨g0, _ | ⟨g1, tail⟩⟩
  · simp at second
  · simp at second
  change some g1.op = some GateOp.or at second
  have orGate : g1.op = GateOp.or := Option.some.inj second
  by_contra short
  change ¬ 16 ≤ (g0 :: g1 :: tail).length at short
  let D : Circuit := ⟨tail, o⟩
  have fanD : FanInTwo D := fun g hg => fan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
  have small : D.size ≤ 13 := by
    simp only [List.length_cons] at short
    change tail.length ≤ 13
    omega
  have pinLen : g1.inputs.length ≤ 2 := (fan g1 (by simp)).2
  have seed (x : Fin 9 → Bool) : step (List.ofFn x) g0 = preset x := by
    have obs := first x
    change ((g1 :: tail).foldl step (step (List.ofFn x) g0)).getD 9 false = _ at obs
    rw [preserve _ _ _ (by simp [step])] at obs
    have bit : g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
      simpa [step, List.getD_eq_getElem?_getD, List.getElem?_append_right] using obs
    simp only [step, preset, bit]
  have evals (x : Fin 9 → Bool) :
      D.eval (preset x ++ [GateOp.or.eval (g1.inputs.map fun i => (preset x).getD i false)]) = target x := by
    have hx := congrFun correct x
    change (tail.foldl step (step (step (List.ofFn x) g0) g1)).getD o false = target x at hx
    rw [seed] at hx
    change (tail.foldl step (preset x ++ [g1.op.eval (g1.inputs.map fun i => (preset x).getD i false)])).getD o false =
      target x at hx
    rw [orGate] at hx
    exact hx
  have allowed : ∀ p : Fin 9 × Fin 9, p ∈ ([(1,2),(1,3),(1,5),(1,6),(1,7),(1,8),(2,3),(2,5),(2,6),(2,7),(2,8),(3,5),(3,6),(3,7),(3,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)] : List (Fin 9 × Fin 9)) ↔
      p.1 ≠ 0 ∧ p.1 ≠ 4 ∧ p.2 ≠ 0 ∧ p.2 ≠ 4 ∧ p.1 < p.2 := by decide +kernel
  by_cases disjoint : ∃ a b : Fin 9, a ≠ 0 ∧ a ≠ 4 ∧ b ≠ 0 ∧ b ≠ 4 ∧ a < b ∧
      g1.inputs.Perm [a.val, b.val]
  · by_cases two : 2 ≤ D.gates.countP (fun g => g.op.eval [false])
    · obtain ⟨a, b, a0, a4, b0, b4, ab, order⟩ := disjoint
      let p : Fin 9 × Fin 9 := (a, b)
      have hp := (allowed p).mpr ⟨a0, a4, b0, b4, ab⟩
      obtain ⟨x, disagrees⟩ := disjointWithNegations p hp D fanD small two
      have read (j : Fin 9) : (preset x).getD j.val false = x j := by
        unfold preset
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]
      have computed : GateOp.or.eval (g1.inputs.map fun i => (preset x).getD i false) =
          (x p.1 || x p.2) := by
        have permuted : GateOp.or.eval (g1.inputs.map fun i => (preset x).getD i false) =
            GateOp.or.eval ([p.1.val,p.2.val].map fun i => (preset x).getD i false) :=
          (order.map (fun i => (preset x).getD i false)).any_eq
        rw [permuted]
        change (([p.1.val, p.2.val].map fun i => (preset x).getD i false).any id) = _
        simp only [List.map_cons, List.map_nil, read, List.any_cons, List.any_nil,
          id_eq, Bool.or_false]
      apply disagrees
      simpa only [computed, preset, List.append_assoc, List.singleton_append] using evals x
    · obtain ⟨x, disagrees⟩ := remaining g1.inputs pinLen D fanD small (Or.inr (by omega))
      exact disagrees (evals x)
  · obtain ⟨x, disagrees⟩ := remaining g1.inputs pinLen D fanD small (Or.inl disjoint)
    exact disagrees (evals x)
