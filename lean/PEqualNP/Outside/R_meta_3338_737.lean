import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3338_737
    (sensitivity :
      let r := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun j => decide (j = 6))
      ∀ (p s : List Gate) (g : Gate) (o : ℕ) (a b : List Bool),
        let D : Circuit := ⟨p ++ g :: s, o⟩
        FanInTwo D → (∀ k ∈ p ++ s, r k = false) → r g = true → g.op = GateOp.or →
        a.length = b.length → 6 < b.length → b.getD 6 false = true →
        (∀ i, i ≠ 6 → a.getD i false = b.getD i false) → o ≠ 6 →
        D.eval a = false → D.eval b = true →
        g.op.eval (g.inputs.map (fun k => ((⟨p, 0⟩ : Circuit).wires a).getD k false)) = false)
    (noTrace :
      let r := fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun j => decide (j = 6))
      let I := fun (b : Bool) (y : Fin 8 → Bool) =>
        [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
      let H := fun (m : ℕ) =>
        ([18369897887404062920, 18446740762289764600, 18446744073709551560,
          18446744073709551608] : List ℕ).getD (m / 64) 0 |>.testBit (m % 64)
      let x := fun (m : ℕ) (j : Fin 8) => m.testBit j.val
      ∀ (p s : List Gate) (g : Gate) (o : ℕ),
        let D : Circuit := ⟨p ++ g :: s, o⟩
        FanInTwo D → p.length + s.length ≤ 13 →
        (∀ k ∈ p ++ s, r k = false) → r g = true → g.op = GateOp.or →
        (∀ m < 256, ((List.ofFn (x m)).count true ≤ 2 ∨ H m = false ∨ m = 255) →
          D.eval (I false (x m)) = H m ∧
          D.eval (I true (x m)) = (H m || x m 0 || x m 3)) →
        (∀ m ∈ ([10,26,74] : List ℕ),
          g.op.eval (g.inputs.map (fun k => ((⟨p,0⟩ : Circuit).wires (I false (x m))).getD k false))
            = false) → False) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) =>   have x4 : ℕ := PEqualNP.MetaComplexity.tableIndex x3;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x4 / (64 : ℕ)) (0 : ℕ)).testBit (x4 % (64 : ℕ)); ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 →     x4.length + x5.length ≤ (13 : ℕ) →       (∀ x11 ∈ x4 ++ x5, x1 x11 = Bool.false) →         x1 x6 = Bool.true →           x6.op = PEqualNP.CircuitLowerBounds.GateOp.or →             (have x14 : Fin (8 : ℕ) → Bool := fun (x14 : Fin (8 : ℕ)) => Decidable.decide (x14 = (1 : Fin (8 : ℕ)) ∨ x14 = (3 : Fin (8 : ℕ)));               have x15 : Bool → Bool := fun (x15 : Bool) => x6.op.eval (List.map (fun (x16 : ℕ) => ({ gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x15 x14)).getD x16 Bool.false) x6.inputs);               x15 Bool.true ≠ x15 Bool.false) →               (∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x3 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x16) ≠ (x3 x16 || x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro p s g o fan size rest marked hor _ low
  by_contra! high
  apply noTrace p s g o fan size rest marked hor
  · intro m hbound _
    let x : Fin 8 → Bool := fun j => m.testBit j.val
    have hindex (r : Fin 256) : tableIndex (fun j : Fin 8 => r.val.testBit j.val) = r.val := by
      revert r
      decide
    have hm : tableIndex x = m := hindex ⟨m,hbound⟩
    have e := low x
    have e' := high x
    rw [hm] at e e'
    exact ⟨e, e'⟩
  · intro m hm
    let a (b : Bool) (y : Fin 8 → Bool) : List Bool :=
      [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]
    let x (j : Fin 8) := m.testBit j.val
    let H (y : Fin 8 → Bool) : Bool :=
      let n := tableIndex y
      ([18369897887404062920, 18446740762289764600, 18446744073709551560,
        18446744073709551608] : List ℕ).getD (n / 64) 0 |>.testBit (n % 64)
    have hcase : m = 10 ∨ m = 26 ∨ m = 74 := by simpa using hm
    have hx1 : x 1 = true := by unfold x; rcases hcase with h | h | h <;> rw [h] <;> decide
    have hx3 : x 3 = true := by unfold x; rcases hcase with h | h | h <;> rw [h] <;> decide
    have hHx : H x = false := by
      unfold H x
      rcases hcase with h | h | h <;> rw [h] <;> decide
    have near (i : ℕ) (hi : i ≠ 6) : (a false x).getD i false = (a true x).getD i false := by
      by_cases hlt : i < 10
      · interval_cases i <;> first | rfl | contradiction | simp [a, hx1]
      · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega),
            List.getD_eq_default _ _ (by change 10 ≤ i; omega)]
    have notOutput : o ≠ 6 := by
      intro e
      let t : List Bool → Gate → List Bool :=
        fun v k => v ++ [k.op.eval (k.inputs.map fun j => v.getD j false)]
      have keep (ks : List Gate) (v : List Bool) (h : 6 < v.length) :
          (ks.foldl t v).getD 6 false = v.getD 6 false := by
        induction ks generalizing v with
        | nil => rfl
        | cons k ks ih =>
          change (ks.foldl t (t v k)).getD 6 false = _
          rw [ih _ (by simp [t]; omega)]
          exact List.getD_append _ _ _ _ h
      let y : Fin 8 → Bool := fun j => decide (j = 0 ∨ j = 1)
      have hy := low y
      change ((p ++ g :: s).foldl t (a false y)).getD o false = H y at hy
      rw [e, keep _ _ (by decide)] at hy
      exact (by decide : (a false y).getD 6 false ≠ H y) hy
    exact sensitivity p s g o (a false x) (a true x) fan rest marked hor rfl
      (by change 6 < 10; decide) rfl near notOutput ((low x).trans hHx)
      ((high x).trans (by change (H x || x 0 || x 3) = true; simp [hx3]))
