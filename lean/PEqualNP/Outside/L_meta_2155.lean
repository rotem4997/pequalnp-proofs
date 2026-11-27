import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2155_aux

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp <;> omega

private theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

end PEqualNP.Outside.L_meta_2155_aux

theorem PEqualNP.Outside.L_meta_2155 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size := by
  intro C _ hfirst hfun hnone
  exfalso
  have hlen : C.gates.length ≤ 1 := by
    cases h : C.gates with
    | nil => simp
    | cons g gs =>
      cases gs with
      | nil => simp
      | cons g' rest => simp [h] at hnone
  have hs (i : Fin 9) : C.eval (List.ofFn (fun k : Fin 9 => decide (k = i))) = false := by
    change circuitFun 9 C _ = false
    rw [hfun]
    fin_cases i <;> decide
  let y : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 2)
  have hy : C.eval (List.ofFn y) = true := by
    change circuitFun 9 C y = true
    rw [hfun]
    decide
  rcases lt_trichotomy C.output 9 with ha | ha | ha
  · let i : Fin 9 := ⟨C.output, ha⟩
    let x : Fin 9 → Bool := fun k => decide (k = i)
    have hx := hs i
    have hw : C.output < (List.ofFn x).length := by simpa using ha
    change (L_meta_2155_aux.run C.gates (List.ofFn x)).getD C.output false = false at hx
    rw [L_meta_2155_aux.run_preserves _ _ _ hw, List.getD_eq_getElem _ _ hw, List.getElem_ofFn] at hx
    simp [x, i] at hx
  · change (C.wires (List.ofFn y)).getD C.output false = true at hy
    rw [ha, hfirst y] at hy
    exact Bool.noConfusion ((show (y 0 || y 4) = false by decide).symm.trans hy)
  · change (L_meta_2155_aux.run C.gates (List.ofFn y)).getD C.output false = true at hy
    rw [List.getD_eq_default _ _ (by rw [L_meta_2155_aux.run_length, List.length_ofFn]; omega)] at hy
    contradiction

