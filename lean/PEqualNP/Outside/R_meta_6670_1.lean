import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_6670_1
    (seed : ∃ C : Circuit,
      C.size ≤ 22 ∧ IsAO2 14 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      14 ≤ C.output ∧ C.output < 14 + C.size ∧
      (∀ p l : Fin 7, l ≠ 1 → (p = l ∨ p = l + 1 ∨ p = l + 3) →
        C.eval (List.ofFn fun i : Fin 14 =>
          decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) ∧
      (∀ m ∈
        ([127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,
          4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,
          11778,12312,12944,14600,16256] : List ℕ),
        C.eval (List.ofFn fun i : Fin 14 => m.testBit i.val) = false))
    (maximal : ∀ x : Fin 14 → Bool,
      Maximal (fun y : Fin 14 → Bool =>
        ¬ ∃ p l : Fin 7,
          (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          y (Fin.castAdd 7 p) = true ∧ y (Fin.natAdd 7 l) = true) x →
      ∃ m ∈
        ([127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,
          4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,
          11778,12312,12944,14600,16256] : List ℕ),
        ∀ i : Fin 14, x i = m.testBit i.val)
    (criterion : ∀ C : Circuit, IsAO2 14 C →
      (∀ p l : Fin 7, l ≠ 1 → (p = l ∨ p = l + 1 ∨ p = l + 3) →
        C.eval (List.ofFn fun i : Fin 14 =>
          decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) →
      (∀ x : Fin 14 → Bool,
        Maximal (fun y : Fin 14 → Bool =>
          ¬ ∃ p l : Fin 7,
            (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            y (Fin.castAdd 7 p) = true ∧ y (Fin.natAdd 7 l) = true) x →
        C.eval (List.ofFn x) = false) →
      ∀ x : Fin 14 → Bool,
        (C.eval (List.ofFn x) = true →
          ∃ p l : Fin 7,
            (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
        ((∃ p l : Fin 7,
            l ≠ 1 ∧
            (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
          C.eval (List.ofFn x) = true))
    :
    ∃ C : Circuit,
      C.size ≤ 22 ∧ IsAO2 14 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      14 ≤ C.output ∧ C.output < 14 + C.size ∧
      ∀ x : Fin 14 → Bool,
        (C.eval (List.ofFn x) = true →
          ∃ p l : Fin 7,
            (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
        ((∃ p l : Fin 7,
            l ≠ 1 ∧
            (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
          C.eval (List.ofFn x) = true) := by
  classical
  rcases seed with ⟨C, hsize, hao, hnodup, hlow, hhigh, hedges, hmasks⟩
  have hfalse : ∀ x : Fin 14 → Bool,
      Maximal (fun y : Fin 14 → Bool =>
        ¬ ∃ p l : Fin 7,
          (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          y (Fin.castAdd 7 p) = true ∧ y (Fin.natAdd 7 l) = true) x →
      C.eval (List.ofFn x) = false := by
    intro x hx
    obtain ⟨m, hm, heq⟩ := maximal x hx
    have hinput : List.ofFn x =
        List.ofFn (fun i : Fin 14 => m.testBit i.val) := by
      congr 1
      funext i
      exact heq i
    rw [hinput]
    exact hmasks m hm
  have hsem := criterion C hao hedges hfalse
  exact ⟨C, hsize, hao, hnodup, hlow, hhigh, hsem⟩