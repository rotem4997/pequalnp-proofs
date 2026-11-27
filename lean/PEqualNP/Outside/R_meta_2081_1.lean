import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2081_1
    (candidate :
      let E := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let Z := fun (y : Fin 13 → Bool) (l : Fin 13) =>
        !(y l || y (l + 1) || y (l + 3) || y (l + 9))
      ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ p l, E p l → C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p))
          (fun i => decide (i = l)))) = true) ∧
        (∀ y, (∀ p, y p = false → ∃ l, E p l ∧ Z y l = true) →
          C.eval (List.ofFn (Fin.addCases y (Z y))) = false) ∧
        ∀ k : Bool, lineSingle C 26 (fun i => decide (i = if k then 0 else 13)) 0 13 = false)
    (gateParts : ∀ (n p q : ℕ) (C : Circuit), p < n → q < n → p ≠ q → IsAO2 n C →
      let parts := linearParts C (fun i => decide (i = p))
        ((List.range n).map fun i => i == p || i == q)
      let d := fun i => (parts.getD i (false, false)).2
      let w := C.wires (List.ofFn fun i : Fin n => decide (i.val = q))
      ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
        (g.op = .and → d (n + j) = ((w.getD a false && d b) || (d a && w.getD b false))) ∧
        (g.op = .or → d (n + j) = (d a || d b))) :
    let E := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let Z := fun (y : Fin 13 → Bool) (l : Fin 13) =>
      !(y l || y (l + 1) || y (l + 3) || y (l + 9))
    ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ p l, E p l → C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p))
        (fun i => decide (i = l)))) = true) ∧
      (∀ y, (∀ p, y p = false → ∃ l, E p l ∧ Z y l = true) →
        C.eval (List.ofFn (Fin.addCases y (Z y))) = false) ∧
      ∀ k : Bool, ∃ d : ℕ → Bool,
        (∀ i < 26, d i = decide (i = if k then 0 else 13)) ∧
        (∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
          let w := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if k then 13 else 0))
          (g.op = .and → d (26 + j) = ((w.getD a false && d b) || (d a && w.getD b false))) ∧
          (g.op = .or → d (26 + j) = (d a || d b))) ∧ d C.output = false := by
  obtain ⟨C, hs, hao, hd, he, hz, hsingle⟩ := candidate
  refine ⟨C, hs, hao, hd, he, hz, ?_⟩
  intro k
  let mark := fun i : ℕ => decide (i = if k then 0 else 13)
  let bits := (List.range 26).map fun i => i == 0 || i == 13
  let parts := linearParts C mark bits
  let initial := bits.zipIdx.map fun p => if mark p.2 then (false, p.1) else (p.1, false)
  have hprefix : initial <+: parts := by
    have keepsPrefix (value : List (Bool × Bool) → Gate → Bool × Bool)
        (gs : List Gate) (w : List (Bool × Bool)) :
        w <+: gs.foldl (fun v g => v ++ [value v g]) w := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih => exact List.IsPrefix.trans ⟨[value w g], rfl⟩ (ih _)
    exact keepsPrefix _ C.gates initial
  refine ⟨fun i => (parts.getD i (false, false)).2, ?_, ?_, hsingle k⟩
  · intro i hi
    obtain ⟨tail, ht⟩ := hprefix
    have hlen : i < initial.length := by simpa [initial, bits] using hi
    change (parts.getD i (false, false)).2 = mark i
    rw [← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
    have initOK (j : Fin 26) :
        ((initial[j.val]?).getD (false, false)).2 = mark j.val := by
      revert j
      cases k <;> decide
    exact initOK ⟨i, hi⟩
  · cases k
    · exact gateParts 26 13 0 C (by decide) (by decide) (by decide) hao
    · exact gateParts 26 0 13 C (by decide) (by decide) (by decide) hao
