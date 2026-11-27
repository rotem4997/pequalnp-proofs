import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1677_361
    (binaryLower : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      13 ≤ C.gates.countP (fun g => !(g.op.eval [false])))
    (lowNegation : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      13 ≤ C.gates.countP (fun g => !(g.op.eval [false])) →
      C.gates.countP (fun g => g.op.eval [false]) ≤ 1 → 15 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size := by
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have before : i < (step w g).length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      rw [ih _ before]
      exact List.getD_append _ _ _ _ hi
  have count (gs : List Gate) :
      gs.countP (fun g => !(g.op.eval [false])) +
        gs.countP (fun g => g.op.eval [false]) = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.countP_cons, List.length_cons]
      cases g.op.eval [false] <;> simp <;> omega
  intro C fan fst eval
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil =>
    have impossible := fst (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at impossible
    rw [List.getD_eq_default _ _ (by simp)] at impossible
    contradiction
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    have tailFan : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    have tailEval (x : Fin 9 → Bool) :
        D.eval (List.ofFn x ++ [x 0 || x 6]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
      let w := List.ofFn x
      let b := g.op.eval (g.inputs.map (fun j => w.getD j false))
      have len : w.length = 9 := List.length_ofFn
      have wire := fst x
      change (gs.foldl step (w ++ [b])).getD 9 false = (x 0 || x 6) at wire
      rw [keep gs _ _ (by simp [len]), List.getD_append_right _ _ _ _ (by omega), len] at wire
      change b = (x 0 || x 6) at wire
      rw [← wire]
      exact congrFun eval x
    have lower := binaryLower D tailFan tailEval
    have total := count gs
    change 13 ≤ gs.countP (fun a => !(a.op.eval [false])) at lower
    change 16 ≤ (g :: gs).length
    by_contra! short
    have cap : gs.countP (fun a => a.op.eval [false]) ≤ 1 := by
      simp only [List.length_cons] at short
      omega
    have bound := lowNegation D tailFan tailEval lower cap
    change 15 ≤ gs.length at bound
    simp only [List.length_cons] at short
    omega
