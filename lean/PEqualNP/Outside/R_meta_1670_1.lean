import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1670_1
    (peel : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 = C.size ∧
        ∀ x : Fin 9 → Bool, D.eval ((List.ofFn x) ++ [x 0 && x 4]) = C.eval (List.ofFn x))
    (distinguish : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
      (∃ x : Fin 9 → Bool, (x 0 && x 4) = false ∧
        D.eval ((List.ofFn x) ++ [false]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) ∨
      (∃ x : Fin 9 → Bool, (x 0 && x 4) = true ∧ D.eval ((List.ofFn x) ++ [true]) = false)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hfirst hgraph
  by_contra! hsmall
  obtain ⟨D, hD, hsize, hsame⟩ := peel C hfan hfirst
  have val (x : Fin 9 → Bool) : D.eval ((List.ofFn x) ++ [x 0 && x 4]) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x :=
    (hsame x).trans (congrFun hgraph x)
  rcases distinguish D hD (by omega) with ⟨x, hx, hneq⟩ | ⟨x, hx, hfalse⟩
  · apply hneq
    have h := val x
    rw [hx] at h
    have hr : (x 4 && x 0) = false := by rwa [Bool.and_comm]
    simpa only [hr, Bool.or_false] using h
  · have h := val x
    rw [hx, hfalse] at h
    have hr : (x 4 && x 0) = true := by rwa [Bool.and_comm]
    simp [hr] at h
