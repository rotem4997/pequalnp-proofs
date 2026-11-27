import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2504_613
    (pinSensitive : ∀ (m : ℕ) (D : Circuit) (w : List (Option (Fin m))) (i k : ℕ),
      FanInTwo D → w[i]? = some none → k ≤ 1 →
      (k = 1 → ∀ g ∈ D.gates, g.op = GateOp.or → i ∉ g.inputs) →
      (∃ u v : List Bool, u.length = w.length ∧ v.length = w.length ∧
        (∀ j, j ≠ i → u.getD j false = v.getD j false) ∧ D.eval u ≠ D.eval v) →
      (∃ x y : Fin m → Bool, D.eval (w.map fun q => q.elim false x) ≠
        D.eval (w.map fun q => q.elim false y)) →
      ∃ E : Circuit, FanInTwo E ∧ E.size + (k + 1) ≤ D.size ∧
        ∀ y : Fin m → Bool, E.eval (List.ofFn y) = D.eval (w.map fun q => q.elim false y))
    (cofactor : ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool =>
      y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
      y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4) 12)
    (minimumOr :
      let read := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j = 6))
      let input := fun (b : Bool) (y : Fin 8 → Bool) =>
        [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
      let H := fun y : Fin 8 → Bool =>
        y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4
      ∀ D : Circuit, FanInTwo D → D.size = 14 → D.gates.countP read ≤ 1 →
        (∃ g ∈ D.gates, g.op = GateOp.or ∧ 6 ∈ g.inputs) →
        (∀ y, D.eval (input false y) = H y) →
        ∃ y, D.eval (input true y) ≠ (H y || y 0 || y 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  let input := fun (b : Bool) (y : Fin 8 → Bool) =>
    [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
  let H := fun y : Fin 8 → Bool =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
    y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4
  let w : List (Option (Fin 8)) := [some 1, some 0, some 4, some 7, some 5,
    some 2, none, some 6, some 3, some 1]
  have wiring (y : Fin 8 → Bool) : (w.map fun q => q.elim false y) = input false y := by
    change [_, _, _, _, _, _, false, _, _, y 1] = [_, _, _, _, _, _, false, _, _, y 1 || false]
    rw [Bool.or_false]
    rfl
  change ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
    D.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
      (fun j => decide (j = 6))) ≤ 1 → (∀ y, D.eval (input false y) = H y) →
    ∃ y, D.eval (input true y) ≠ (H y || y 0 || y 3)
  intro D fan size count low
  change ∀ y, D.eval (input false y) = H y at low
  by_contra! high
  change ∀ y, D.eval (input true y) = (H y || y 0 || y 3) at high
  let x : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
  have sensitive : ∃ u v : List Bool, u.length = w.length ∧ v.length = w.length ∧
      (∀ j, j ≠ 6 → u.getD j false = v.getD j false) ∧ D.eval u ≠ D.eval v := by
    refine ⟨input false x, input true x, rfl, rfl, ?_, ?_⟩
    · intro j hj
      by_cases hj' : j < 10
      · interval_cases j <;> first | rfl | contradiction
      · rw [List.getD_eq_default _ _ (by change 10 ≤ j; omega),
            List.getD_eq_default _ _ (by change 10 ≤ j; omega)]
    · rw [low, high]
      decide
  have varies : ∃ a b : Fin 8 → Bool, D.eval (w.map fun q => q.elim false a) ≠
      D.eval (w.map fun q => q.elim false b) := by
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    rw [wiring, wiring, low (fun _ => false), low (fun i => decide (i = 0 ∨ i = 1))]
    decide
  have bound (k : ℕ) (hk : k ≤ 1)
      (hop : k = 1 → ∀ g ∈ D.gates, g.op = GateOp.or → 6 ∉ g.inputs) :
      13 + (k + 1) ≤ D.size := by
    obtain ⟨E, he, cost, eq⟩ := pinSensitive 8 D w 6 k fan rfl hk hop sensitive varies
    have expensive : 13 ≤ E.size := by
      by_contra! small
      apply cofactor
      refine ⟨E, he, by omega, ?_⟩
      intro y
      exact (eq y).trans ((congrArg D.eval (wiring y)).trans (low y))
    omega
  have one := bound 0 (by decide) (fun h => by omega)
  have reader : ∃ g ∈ D.gates, g.op = GateOp.or ∧ 6 ∈ g.inputs := by
    by_contra! none
    have two := bound 1 (by decide) (fun _ => none)
    omega
  obtain ⟨y, bad⟩ := minimumOr D fan (by omega) count reader low
  exact bad (high y)
