import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4932
open PEqualNP.CircuitLowerBounds



def xs : List (BitVec 58) := [(95229015649943559 : BitVec 58), (63038587666488 : BitVec 58), (256462815680 : BitVec 58), (4292497062759936 : BitVec 58), (8521481482240 : BitVec 58), (14003410187812864 : BitVec 58), (55389823207997440 : BitVec 58), (189297016294081033 : BitVec 58), (155696362464477250 : BitVec 58), (218994303132270608 : BitVec 58), (183565875465490436 : BitVec 58), (229736628138025984 : BitVec 58), (270286071508633728 : BitVec 58), (288160007407550752 : BitVec 58)]

def rows : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112, 127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

set_option maxRecDepth 100000 in
theorem rows_ok : ∀ r : Fin 58, ∀ i : Fin 14,
    (rows.getD r.1 0).testBit i.1 = (xs.getD i.1 0).getLsbD r.1 := by decide +kernel

theorem rows_lt : ∀ r : Fin 58, rows.getD r.1 0 < 16384 := by decide +kernel

def chk (m : ℕ) : Bool :=
  !((rows.take 21).all fun R => R &&& m != R) || (rows.drop 21).any fun R => m &&& R == m

set_option maxRecDepth 100000 in
theorem all_ok : (List.range 16384).all chk = true := by decide +kernel

theorem sub_iff (R m : ℕ) (hR : R < 16384) :
    R &&& m = R ↔ ∀ i : Fin 14, R.testBit i.1 = true → m.testBit i.1 = true := by
  constructor
  · intro h i hi
    have h2 := congrArg (fun t => t.testBit i.1) h
    simp only [Nat.testBit_and] at h2
    rw [hi] at h2
    simpa using h2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 14
    · cases hr : R.testBit i with
      | false => rfl
      | true => rw [h ⟨i, hi⟩ hr]; rfl
    · have : R.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        calc R < 16384 := hR
          _ = 2 ^ 14 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [this]; rfl

end PEqualNP.Outside.L_meta_4932

open PEqualNP.Outside.L_meta_4932 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4932 : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; have x2 : ℕ → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 : Fin (14 : ℕ)) => (x1.getD ↑x3 (0 : BitVec (58 : ℕ))).getLsbD x2; ∀ (x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (21 : ℕ)), ¬x2 ↑x4 ≤ x3) → ∃ (x5 : Fin (37 : ℕ)), x3 ≤ x2 ((21 : ℕ) + ↑x5) := by
  intro X F x hno
  have hm : Nat.ofBits x < 16384 := Nat.ofBits_lt_two_pow x
  have hx : ∀ i : Fin 14, (Nat.ofBits x).testBit i.1 = x i := fun i => Nat.testBit_ofBits_lt x i.1 i.2
  have hF : ∀ (r : Fin 58) (i : Fin 14), F r.1 i = (rows.getD r.1 0).testBit i.1 := by
    intro r i
    rw [rows_ok r i]
    rfl
  have hlen : rows.length = 58 := by decide
  have hchk := List.all_eq_true.1 all_ok (Nat.ofBits x) (List.mem_range.2 hm)
  unfold chk at hchk
  by_cases hall : ((rows.take 21).all fun R => R &&& Nat.ofBits x != R) = true
  · rw [hall] at hchk
    have hany : ((rows.drop 21).any fun R => Nat.ofBits x &&& R == Nat.ofBits x) = true := by
      simpa using hchk
    obtain ⟨R, hR, hRe⟩ := List.any_eq_true.1 hany
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hR
    rw [List.length_drop, hlen] at hj
    rw [List.getElem_drop] at e
    have hRe' : Nat.ofBits x &&& R = Nat.ofBits x := by simpa using hRe
    have hRg : rows.getD (21 + j) 0 = R := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]; exact e
    refine ⟨⟨j, hj⟩, ?_⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hxi
    show F (21 + j) i = true
    have h1 := hF ⟨21 + j, by omega⟩ i
    rw [h1, hRg]
    have h2 := (sub_iff (Nat.ofBits x) R hm).1 hRe' i
    apply h2
    rw [hx i]; exact hxi
  · exfalso
    rw [List.all_eq_true] at hall
    push_neg at hall
    obtain ⟨R, hR, hRe⟩ := hall
    obtain ⟨r, hr, e⟩ := List.getElem_of_mem hR
    rw [List.length_take, hlen] at hr
    rw [List.getElem_take] at e
    have hr' : r < 21 := by omega
    have hRe' : R &&& Nat.ofBits x = R := by simpa using hRe
    have hRg : rows.getD r 0 = R := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]; exact e
    have hRlt : R < 16384 := by
      have := rows_lt ⟨r, by omega⟩
      rw [hRg] at this
      exact this
    apply hno ⟨r, hr'⟩
    intro i
    rw [Bool.le_iff_imp]
    intro hFi
    have hFi' : F r i = true := hFi
    have h1 := hF ⟨r, by omega⟩ i
    rw [h1, hRg] at hFi'
    have h2 := (sub_iff R (Nat.ofBits x) hRlt).1 hRe' i hFi'
    rw [hx i] at h2
    exact h2
