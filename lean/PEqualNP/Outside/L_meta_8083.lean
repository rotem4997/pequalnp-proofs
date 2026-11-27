import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8083

theorem noPair : ∀ m ∈ ([127, 245, 361, 481, 595, 721, 1063, 1189, 2127, 2245, 2377, 2627, 3009, 3079, 4125, 4245, 6157, 7301, 8251, 8369, 8489, 8723, 9251, 9633, 10251, 11779, 12313, 12945, 14601, 16257] : List ℕ), ∀ p l : Fin 7, p ≠ 0 →
    (p = l ∨ p = l + 1 ∨ p = l + 3) → m.testBit p.val = true → m.testBit (7 + l.val) = true → False := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem keyBool : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool, (b1 && b8) = false → (b1 && b7) = false → (b1 && b12) = false → (b2 && b9) = false → (b2 && b8) = false → (b2 && b13) = false → (b3 && b10) = false → (b3 && b9) = false → (b3 && b7) = false → (b4 && b11) = false → (b4 && b10) = false → (b4 && b8) = false → (b5 && b12) = false → (b5 && b11) = false → (b5 && b9) = false → (b6 && b13) = false → (b6 && b12) = false → (b6 && b10) = false →
    ∃ m ∈ ([127, 245, 361, 481, 595, 721, 1063, 1189, 2127, 2245, 2377, 2627, 3009, 3079, 4125, 4245, 6157, 7301, 8251, 8369, 8489, 8723, 9251, 9633, 10251, 11779, 12313, 12945, 14601, 16257] : List ℕ), ∀ i : Fin 14, (![true, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] : Fin 14 → Bool) i ≤ m.testBit i := by
  decide

end PEqualNP.Outside.L_meta_8083

open PEqualNP.Outside.L_meta_8083 in
theorem PEqualNP.Outside.L_meta_8083 : ∀ (x1 : Fin (14 : ℕ) → Bool), (∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), x2 ≠ (0 : Fin (7 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true) ↔ ∀ x2 ∈ [(127 : ℕ), (245 : ℕ), (361 : ℕ), (481 : ℕ), (595 : ℕ), (721 : ℕ), (1063 : ℕ), (1189 : ℕ), (2127 : ℕ), (2245 : ℕ), (2377 : ℕ), (2627 : ℕ), (3009 : ℕ), (3079 : ℕ), (4125 : ℕ), (4245 : ℕ), (6157 : ℕ), (7301 : ℕ), (8251 : ℕ), (8369 : ℕ), (8489 : ℕ), (8723 : ℕ), (9251 : ℕ), (9633 : ℕ), (10251 : ℕ), (11779 : ℕ), (12313 : ℕ), (12945 : ℕ), (14601 : ℕ), (16257 : ℕ)], ¬x1 ≤ fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4 := by
  intro x
  constructor
  · rintro ⟨p, l, hp0, hinc, hxp, hxl⟩ m hm hle
    have h1 : m.testBit (Fin.castAdd 7 p).val = true := by
      have := hle (Fin.castAdd 7 p)
      dsimp only at this
      rw [hxp] at this
      revert this
      cases m.testBit (Fin.castAdd 7 p).val <;> simp
    have h2 : m.testBit (Fin.natAdd 7 l).val = true := by
      have := hle (Fin.natAdd 7 l)
      dsimp only at this
      rw [hxl] at this
      revert this
      cases m.testBit (Fin.natAdd 7 l).val <;> simp
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
    exact noPair m hm p l hp0 hinc h1 h2
  · intro hall
    by_contra hF
    have e : ∀ p l : Fin 7, p ≠ 0 → (p = l ∨ p = l + 1 ∨ p = l + 3) →
        (x (Fin.castAdd 7 p) && x (Fin.natAdd 7 l)) = false := by
      intro p l hp hi
      cases hxp : x (Fin.castAdd 7 p) <;> cases hxl : x (Fin.natAdd 7 l)
      all_goals first
        | rfl
        | exact absurd ⟨p, l, hp, hi, hxp, hxl⟩ hF
    obtain ⟨m, hm, hle⟩ := keyBool (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)
      (e 1 1 (by decide) (by decide))
      (e 1 0 (by decide) (by decide))
      (e 1 5 (by decide) (by decide))
      (e 2 2 (by decide) (by decide))
      (e 2 1 (by decide) (by decide))
      (e 2 6 (by decide) (by decide))
      (e 3 3 (by decide) (by decide))
      (e 3 2 (by decide) (by decide))
      (e 3 0 (by decide) (by decide))
      (e 4 4 (by decide) (by decide))
      (e 4 3 (by decide) (by decide))
      (e 4 1 (by decide) (by decide))
      (e 5 5 (by decide) (by decide))
      (e 5 4 (by decide) (by decide))
      (e 5 2 (by decide) (by decide))
      (e 6 6 (by decide) (by decide))
      (e 6 5 (by decide) (by decide))
      (e 6 3 (by decide) (by decide))
    apply hall m hm
    rw [Pi.le_def]
    intro i
    have h1 := hle i
    fin_cases i <;> first | exact h1 | exact le_trans (Bool.le_true _) h1
