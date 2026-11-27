import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4647_aux

def tbl : List ℕ := [16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]

def col (k : ℕ) (i : Fin 14) : Bool := (tbl.getD i.val 0).testBit k

theorem T1 : ∀ k : Fin 58, ((∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    col k.val (Fin.castAdd 7 p) = true ∧ col k.val (Fin.natAdd 7 l) = true) ↔ k.val < 21) := by
  decide +kernel

theorem T2 : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
    ∃ k : Fin 58, k.val < 21 ∧ ∀ i : Fin 14, col k.val i = true →
      (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by
  decide +kernel

theorem T3 : ∀ m : Fin 128, ∃ k : Fin 58, 21 ≤ k.val ∧
    (∀ l : Fin 7, m.val.testBit l.val = true → col k.val (Fin.natAdd 7 l) = true) ∧
    (∀ p : Fin 7, (∀ l : Fin 7, m.val.testBit l.val = true → ¬ (p = l ∨ p = l + 1 ∨ p = l + 3)) →
      col k.val (Fin.castAdd 7 p) = true) := by
  decide +kernel

theorem main (f : (Fin 14 → Bool) → Bool) :
    (∀ x : Fin 14 → Bool, f x = true ↔ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ↔
    Monotone f ∧ ∀ k : Fin 58, f (fun i : Fin 14 => col k.val i) = decide (k.val < 21) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      rw [Bool.le_iff_imp]
      intro hx
      obtain ⟨p, l, hi, hp, hl⟩ := (h x).1 hx
      refine (h y).2 ⟨p, l, hi, ?_, ?_⟩
      · exact Bool.le_iff_imp.1 (hxy _) hp
      · exact Bool.le_iff_imp.1 (hxy _) hl
    · intro k
      rw [Bool.eq_iff_iff, h, decide_eq_true_iff]
      exact T1 k
  · rintro ⟨hm, hv⟩ x
    constructor
    · intro hx
      by_contra hno
      have hm7 : Nat.ofBits (fun l : Fin 7 => x (Fin.natAdd 7 l)) < 128 :=
        Nat.ofBits_lt_two_pow _
      obtain ⟨k, hk21, hL, hP⟩ := T3 ⟨_, hm7⟩
      have hbit : ∀ l : Fin 7, (Nat.ofBits (fun l : Fin 7 => x (Fin.natAdd 7 l))).testBit l.val
          = x (Fin.natAdd 7 l) := fun l => Nat.testBit_ofBits_lt _ _ l.isLt
      have hle : x ≤ (fun i : Fin 14 => col k.val i) := by
        intro i
        refine Fin.addCases (m := 7) (n := 7) (motive := fun i => x i ≤ col k.val i) ?_ ?_ i
        · intro p
          rw [Bool.le_iff_imp]
          intro hp
          apply hP p
          intro l hl hinc
          exact hno ⟨p, l, hinc, hp, (hbit l) ▸ hl⟩
        · intro l
          rw [Bool.le_iff_imp]
          intro hl
          apply hL l
          show (Nat.ofBits (fun l : Fin 7 => x (Fin.natAdd 7 l))).testBit l.val = true
          rw [hbit l]
          exact hl
      have h1 := hm hle
      rw [hx, hv k, decide_eq_false (by omega)] at h1
      exact absurd h1 (by decide)
    · rintro ⟨p, l, hinc, hp, hl⟩
      obtain ⟨k, hk, hsub⟩ := T2 p l hinc
      have hle : (fun i : Fin 14 => col k.val i) ≤ x := by
        intro i
        rw [Bool.le_iff_imp]
        intro hi
        rcases hsub i hi with rfl | rfl
        · exact hp
        · exact hl
      have h1 := hm hle
      rw [hv k, decide_eq_true hk] at h1
      exact Bool.eq_true_of_true_le h1

end PEqualNP.Outside.L_meta_4647_aux

theorem PEqualNP.Outside.L_meta_4647 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool), (∀ (x2 : Fin (14 : ℕ) → Bool), x1 x2 = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ↔ Monotone x1 ∧ ∀ (x2 : Fin (58 : ℕ)), (x1 fun (x3 : Fin (14 : ℕ)) => ([(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x2) = Decidable.decide (↑x2 < (21 : ℕ)) := by
  intro f
  exact PEqualNP.Outside.L_meta_4647_aux.main f
