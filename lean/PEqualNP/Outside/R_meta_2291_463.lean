import Mathlib.Tactic.NormNum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize malformed references, constants and copies before separating the two bases.
theorem PEqualNP.Outside.R_meta_2291_463
    (normalize : ∀ (gs : List Gate) (a b : ℕ), FanInTwo ⟨gs, 0⟩ →
      a < b → b < 10 + gs.length →
      ∃ (ks : List Gate) (u v : ℕ), ks.length ≤ gs.length ∧
        u < 12 + ks.length ∧ v < 12 + ks.length ∧ FanInTwo ⟨ks, 0⟩ ∧
        (∀ i : Fin ks.length, let g := ks.get i
        (∀ j ∈ g.inputs, j < 12 + i.val) ∧ g.inputs.Nodup ∧
        ((g.op = .not ∧ g.inputs.length = 1) ∨
          (g.op ≠ .not ∧ g.inputs.length = 2))) ∧
        ∀ inp : List Bool, inp.length = 10 →
          ((Circuit.mk ks u).eval (inp ++ [false, true]) ||
            (Circuit.mk ks v).eval (inp ++ [false, true])) =
          ((Circuit.mk gs a).eval inp || (Circuit.mk gs b).eval inp))
    (monotone : ∀ (ks : List Gate) (u v : ℕ), ks.length ≤ 13 →
      u < 12 + ks.length → v < 12 + ks.length → FanInTwo ⟨ks, 0⟩ →
      (∀ i : Fin ks.length, let g := ks.get i
        (∀ j ∈ g.inputs, j < 12 + i.val) ∧ g.inputs.Nodup ∧
        ((g.op = .not ∧ g.inputs.length = 1) ∨
          (g.op ≠ .not ∧ g.inputs.length = 2))) →
      (∀ g ∈ ks, g.op ≠ .not) → ∃ x : Fin 9 → Bool,
        let inp := List.ofFn x ++ [x 0 && x 6, false, true]
        ((Circuit.mk ks u).eval inp || (Circuit.mk ks v).eval inp) ≠
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (signed : ∀ (ks : List Gate) (u v : ℕ), ks.length ≤ 13 →
      u < 12 + ks.length → v < 12 + ks.length → FanInTwo ⟨ks, 0⟩ →
      (∀ i : Fin ks.length, let g := ks.get i
        (∀ j ∈ g.inputs, j < 12 + i.val) ∧ g.inputs.Nodup ∧
        ((g.op = .not ∧ g.inputs.length = 1) ∨
          (g.op ≠ .not ∧ g.inputs.length = 2))) →
      (∃ g ∈ ks, g.op = .not) → ∃ x : Fin 9 → Bool,
        let inp := List.ofFn x ++ [x 0 && x 6, false, true]
        ((Circuit.mk ks u).eval inp || (Circuit.mk ks v).eval inp) ≠
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length → (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) := by
  classical
  intro gs a b basis budget ordered bounded same
  obtain ⟨ks, u, v, size, hu, hv, good, canonical, preserves⟩ :=
    normalize gs a b basis ordered bounded
  have ksBudget : ks.length ≤ 13 := size.trans budget
  have mismatch : ∃ x : Fin 9 → Bool,
      let inp := List.ofFn x ++ [x 0 && x 6, false, true]
      ((Circuit.mk ks u).eval inp || (Circuit.mk ks v).eval inp) ≠
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    by_cases useNot : ∃ g ∈ ks, g.op = .not
    · exact signed ks u v ksBudget hu hv good canonical useNot
    · exact monotone ks u v ksBudget hu hv good canonical
        (fun g hg op => useNot ⟨g, hg, op⟩)
  obtain ⟨x, bad⟩ := mismatch
  have he := preserves (List.ofFn x ++ [x 0 && x 6]) (by simp)
  apply bad
  simp only [List.append_assoc, List.cons_append, List.nil_append] at he
  rw [he, congrFun same x]
  norm_num [List.any, Bool.or_assoc] <;> rfl
