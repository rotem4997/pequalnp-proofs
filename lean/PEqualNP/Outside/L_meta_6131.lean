import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_6131 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  constructor
  · let C : Circuit := ⟨[⟨.and, []⟩], 8⟩
    refine ⟨C, ?_, by decide, ?_⟩
    · simp [C, Monotone2]
    · decide +kernel
  · rintro ⟨⟨gs, o⟩, _, hs, rep⟩
    have e : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
    subst gs
    have a := rep 0 0
    have b := rep 1 1
    change (oneEach (0 : Fin 4) (0 : Fin 4)).getD o false = true at a
    change (oneEach (1 : Fin 4) (1 : Fin 4)).getD o false = true at b
    by_cases ho : o < 8
    · have disjoint : ∀ i : Fin 8,
          ¬ ((oneEach (0 : Fin 4) (0 : Fin 4)).getD i.val false = true ∧
             (oneEach (1 : Fin 4) (1 : Fin 4)).getD i.val false = true) := by decide +kernel
      exact disjoint ⟨o, ho⟩ ⟨a, b⟩
    · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)] at a
      contradiction
