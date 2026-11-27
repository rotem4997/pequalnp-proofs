import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1670_2
    (trace : ∀ (D : Circuit) (s : List ((Fin 9 → Bool) → Bool)), FanInTwo D →
      ∃ t : List ((Fin 9 → Bool) → Bool), t.length = D.size ∧
      (∀ j : Fin t.length,
        let w := (fun _ => false) :: (fun _ => true) :: (s ++ t.take j.val)
        ∃ a ∈ w, ∃ b ∈ w,
          t.get j = (fun x => a x && b x) ∨ t.get j = (fun x => a x || b x) ∨
          t.get j = (fun x => !(a x))) ∧
      (fun x => D.eval (s.map (fun c => c x))) ∈ (fun _ => false) :: (s ++ t))
    (lower : let s := (List.ofFn (fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4])
      ∀ t : List ((Fin 9 → Bool) → Bool), (∀ j : Fin t.length,
        let w := (fun _ => false) :: (fun _ => true) :: (s ++ t.take j.val)
        ∃ a ∈ w, ∃ b ∈ w,
          t.get j = (fun x => a x && b x) ∨ t.get j = (fun x => a x || b x) ∨
          t.get j = (fun x => !(a x))) →
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ∈ (fun _ => false) :: (s ++ t) →
        15 ≤ t.length) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hC first correct
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have lengthOf (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  cases C with
  | mk gates out =>
    cases gates with
    | nil =>
      have h := first (fun _ => true)
      change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
      have hn : (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = false := by decide
      rw [hn] at h
      contradiction
    | cons g gs =>
      let D : Circuit := ⟨gs,out⟩
      have hh (x : Fin 9 → Bool) :
          step (List.ofFn x) g = List.ofFn x ++ [x 0 && x 4] := by
        have hv := first x
        change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at hv
        rw [keep] at hv
        · have hs (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
            simp [List.getD_eq_getElem?_getD]
          have hx := hs (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))
          rw [List.length_ofFn] at hx
          change (List.ofFn x ++ [_]).getD 9 false = _ at hv
          rw [hx] at hv
          simp only [step, hv]
        · simp [step]
      have hw (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 && x 4]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
        have he := congrFun correct x
        change (gs.foldl step (step (List.ofFn x) g)).getD out false = _ at he
        rw [hh] at he
        exact he
      let s := (List.ofFn (fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4])
      have fan : FanInTwo D := by
        intro v hv
        exact hC v (List.mem_cons_of_mem _ hv)
      obtain ⟨t, hlen, hvalid, hout⟩ := trace D s fan
      have wire (x : Fin 9 → Bool) : s.map (fun c => c x) = List.ofFn x ++ [x 0 && x 4] := by
        simp [s, List.map_ofFn, Function.comp_def]
      have truth : (fun x => D.eval (s.map (fun c => c x))) =
          (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
        funext x
        rw [wire, hw]
      rw [truth] at hout
      have h := lower t hvalid hout
      change t.length = gs.length at hlen
      change 16 ≤ (g :: gs).length
      simp
      omega
