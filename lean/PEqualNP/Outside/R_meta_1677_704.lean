import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1677_704
    (boundary : ∀ T : Circuit, FanInTwo T →
      (∀ x : Fin 9 → Bool, (x 0 = true ∨ x 6 = false) →
        T.eval (List.ofFn x ++ [x 0]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ T.size)
    (optimal : ∀ T : Circuit, FanInTwo T → T.size = 14 →
      (∀ x : Fin 9 → Bool, (x 0 = true ∨ x 6 = false) →
        T.eval (List.ofFn x ++ [x 0]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      (∀ D : Circuit, FanInTwo D →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0]) =
          T.eval (List.ofFn x ++ [x 0])) → 14 ≤ D.size) →
      ∃ x : Fin 9 → Bool, x 0 = false ∧ x 6 = true ∧
        T.eval (List.ofFn x ++ [true]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C ok fst computed
  let graph := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      ((⟨gs,0⟩ : Circuit).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun j => w.getD j false)
      change ((⟨gs,0⟩ : Circuit).wires (w ++ [b])).getD i false = _
      rw [ih (w ++ [b]) (by simp; omega), List.getD_append _ _ _ _ hi]
  obtain ⟨gates,o⟩ := C
  cases gates with
  | nil =>
    have bad := fst (fun _ => true)
    contradiction
  | cons g gs =>
    let T : Circuit := ⟨gs,o⟩
    have okT : FanInTwo T := fun v hv => ok v (List.mem_cons_of_mem _ hv)
    have extn (x : Fin 9 → Bool) : T.eval (List.ofFn x ++ [x 0 || x 6]) = graph x := by
      let w := List.ofFn x
      let b := g.op.eval (g.inputs.map fun j => w.getD j false)
      have hn : w.length = 9 := List.length_ofFn
      have h := fst x
      change ((⟨gs,0⟩ : Circuit).wires (w ++ [b])).getD 9 false = (x 0 || x 6) at h
      rw [keep gs _ _ (by simp [hn]), List.getD_append_right _ _ _ _ (by omega), hn] at h
      change b = (x 0 || x 6) at h
      rw [← h]
      exact congrFun computed x
    have onAlias (x : Fin 9 → Bool) (hx : x 0 = true ∨ x 6 = false) :
        T.eval (List.ofFn x ++ [x 0]) = graph x := by
      have e := extn x
      rcases hx with a|b
      · simpa only [a,Bool.true_or] using e
      · simpa only [b,Bool.or_false] using e
    have bound := boundary T okT onAlias
    have cap (D : Circuit) (hd : FanInTwo D)
        (same : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0]) = T.eval (List.ofFn x ++ [x 0])) :
        14 ≤ D.size := boundary D hd (fun x hx => (same x).trans (onAlias x hx))
    change 16 ≤ (g::gs).length
    change 14 ≤ gs.length at bound
    by_contra! short
    have exactSize : T.size=14 := by change gs.length=14; simp at short; omega
    obtain ⟨x,h0,h6,bad⟩ := optimal T okT exactSize onAlias cap
    apply bad
    change T.eval (List.ofFn x ++ [true]) = graph x
    simpa only [h0,h6,Bool.false_or] using extn x
