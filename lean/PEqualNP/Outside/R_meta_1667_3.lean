import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pin the computed first wire to false and leave its position in the input
-- list of the suffix. If the suffix still computes the whole function, the
-- first gate is dispensable. Otherwise the suffix depends on this extra wire.
-- Constant propagation saves at least one more gate on the false cofactor.
-- The cofactor is nonconstant, as witnessed by the empty set and edge 2,3.
-- In the reverse direction, a 13-gate circuit fitting the promised rows can
-- be completed by computing edge 0,1 first and joining it to the output by OR.

theorem PEqualNP.Outside.R_meta_1667_3
    (pinFalse : ∀ (n : Nat) (C : Circuit), FanInTwo C →
      (∃ a b : Fin n → Bool, C.eval (List.ofFn a ++ [false]) ≠
        C.eval (List.ofFn b ++ [false])) →
      (∃ x : Fin n → Bool, C.eval (List.ofFn x ++ [true]) ≠
        C.eval (List.ofFn x ++ [false])) →
      ∃ D : Circuit, FanInTwo D ∧ D.size < C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [false]) =
          C.eval (List.ofFn x ++ [false]))
    (full : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 15 ≤ D.size)
    (promised : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (x 0 && x 1) = false →
        D.eval (List.ofFn x ++ [false]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 14 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let f : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  intro C hm hfirst hout
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil =>
    have h := hfirst (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp : _ ≤ 9)] at h
    cases h
  | cons g gs =>
    let T : Circuit := ⟨gs, o⟩
    have hT : FanInTwo T := fun k hk => hm k (List.mem_cons_of_mem g hk)
    have sz : (Circuit.mk (g :: gs) o).size = T.size + 1 := rfl
    have correct (x : Fin 9 → Bool) :
        T.eval (List.ofFn x ++ [x 0 && x 1]) = f x := by
      let w := List.ofFn x
      have hw : w.length = 9 := by simp [w]
      let b := g.op.eval (g.inputs.map fun i => w.getD i false)
      have hv := hfirst x
      change (gs.foldl step (w ++ [b])).getD 9 false = _ at hv
      rw [preserved gs (w ++ [b]) 9 (by simp [hw])] at hv
      have hlast := atEnd w b
      rw [hw] at hlast
      rw [hlast] at hv
      have h := congrFun hout x
      change T.eval (w ++ [b]) = f x at h
      simpa only [← hv] using h
    have zeroRow (x : Fin 9 → Bool) (hx : (x 0 && x 1) = false) :
        T.eval (List.ofFn x ++ [false]) = f x := by
      simpa only [hx] using correct x
    by_cases hwhole : ∀ x : Fin 9 → Bool, T.eval (List.ofFn x ++ [false]) = f x
    · have h := full T hT hwhole
      omega
    · have dep : ∃ x : Fin 9 → Bool,
          T.eval (List.ofFn x ++ [true]) ≠ T.eval (List.ofFn x ++ [false]) := by
        by_contra! h
        apply hwhole
        intro x
        cases hbit : (x 0 && x 1) with
        | false => exact zeroRow x hbit
        | true => simpa only [hbit, h x] using correct x
      let a : Fin 9 → Bool := fun _ => false
      let b : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 3)
      have ha := zeroRow a (by decide)
      have hb := zeroRow b (by decide)
      have hab : T.eval (List.ofFn a ++ [false]) ≠ T.eval (List.ofFn b ++ [false]) := by
        rw [ha, hb]
        decide
      obtain ⟨D, hD, hs, heq⟩ := pinFalse 9 T hT ⟨a, b, hab⟩ dep
      have hsmall := promised D hD (fun x hx => (heq x).trans (zeroRow x hx))
      omega
