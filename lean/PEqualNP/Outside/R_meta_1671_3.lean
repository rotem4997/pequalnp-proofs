import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1671_3
    (unpinned : ∀ D : Circuit, FanInTwo D →
      circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      15 ≤ D.size)
    (deletedVertex : ∀ D : Circuit, FanInTwo D →
      circuitFun 8 D = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 7 && x 5)) →
      13 ≤ D.size)
    (pin : ∀ C : Circuit, IsMinimalCircuit 9 C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) →
      circuitFun 9 C (fun i => decide (i = 8)) ≠
        circuitFun 9 C (fun i => decide (i = 6 ∨ i = 8)) →
      circuitFun 9 C (fun _ => false) ≠
        circuitFun 9 C (fun i => decide (i = 1 ∨ i = 2)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        ∀ y : Fin 9 → Bool, y 6 = false →
          circuitFun 8 D (fun i => y ((6 : Fin 9).succAbove i)) = circuitFun 9 C y) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C basis first correct
  by_cases least : IsMinimalCircuit 9 C
  · have sensitive : circuitFun 9 C (fun i => decide (i = 8)) ≠
        circuitFun 9 C (fun i => decide (i = 6 ∨ i = 8)) := by
      rw [correct]
      decide
    have nonconstant : circuitFun 9 C (fun _ => false) ≠
        circuitFun 9 C (fun i => decide (i = 1 ∨ i = 2)) := by
      rw [correct]
      decide
    obtain ⟨D,hD,hs,he⟩ := pin C least first sensitive nonconstant
    have bound := deletedVertex D hD (by
      funext x
      let y := (6 : Fin 9).insertNth (α := fun _ => Bool) false x
      have at6 : y 6 = false := Fin.insertNth_apply_same _ _ _
      have at0 : y 0 = x 0 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (0 : Fin 8)
      have at1 : y 1 = x 1 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (1 : Fin 8)
      have at2 : y 2 = x 2 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (2 : Fin 8)
      have at3 : y 3 = x 3 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (3 : Fin 8)
      have at4 : y 4 = x 4 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (4 : Fin 8)
      have at5 : y 5 = x 5 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (5 : Fin 8)
      have at7 : y 7 = x 6 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (6 : Fin 8)
      have at8 : y 8 = x 7 := Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false x (7 : Fin 8)
      have hp := he y at6
      have back : (fun i => y ((6 : Fin 9).succAbove i)) = x := by
        funext i
        exact Fin.insertNth_apply_succAbove (α := fun _ => Bool) _ _ _ _
      rw [back] at hp
      rw [hp, correct]
      change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) = _
      simp only [at0, at1, at2, at3, at4, at5, at6, at7, at8, Bool.and_false,
        Bool.false_and, Bool.or_false, Bool.false_or])
    omega
  · by_contra small
    apply least
    refine ⟨basis, ?_⟩
    intro D hD hfun
    have lo := unpinned D hD (hfun.trans correct)
    omega
