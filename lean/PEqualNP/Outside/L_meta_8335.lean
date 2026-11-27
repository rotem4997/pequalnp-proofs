import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8335

def codes : List ℕ := [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95]

def L : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def indep (s : ℕ) : Bool := codes.all fun c => !(s.testBit (c / 14) && s.testBit (c % 14))

def covered (s : ℕ) : Bool := L.any fun m => Nat.beq (Nat.land s m) s

def check : ℕ → Bool
  | 0 => true
  | n + 1 => (!indep n || covered n) && check n

theorem check_ok : check 16384 = true := by decide +kernel

theorem codes_lt : ∀ c ∈ codes, c < 196 := by decide

theorem check_spec : ∀ n, check n = true → ∀ s < n, indep s = true → covered s = true := by
  intro n
  induction n with
  | zero =>
    intro _ s hs
    exact absurd hs (Nat.not_lt_zero _)
  | succ n ih =>
    intro hc s hs hi
    have hc2 := hc
    simp only [check, Bool.and_eq_true_iff] at hc2
    by_cases hsn : s = n
    · rw [hsn] at hi ⊢
      have h1 := hc2.1
      rw [hi] at h1
      simpa using h1
    · exact ih hc2.2 s (by omega) hi

theorem mask_exists : ∀ (n : ℕ) (f : ℕ → Bool), ∃ s, s < 2 ^ n ∧ ∀ i < n, s.testBit i = f i := by
  intro n f
  induction n with
  | zero => exact ⟨0, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨s, hs, hb⟩ := ih
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ]
      omega
    cases hf : f n with
    | false =>
      refine ⟨s, by omega, fun i hi => ?_⟩
      by_cases hin : i = n
      · rw [hin, hf]
        exact Nat.testBit_lt_two_pow hs
      · exact hb i (by omega)
    | true =>
      refine ⟨2 ^ n + s, by omega, fun i hi => ?_⟩
      by_cases hin : i = n
      · rw [hin, hf, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hs]
        rfl
      · rw [Nat.testBit_two_pow_add_gt (by omega)]
        exact hb i (by omega)

theorem main (x1 : Fin 14 → Bool)
    (hx : ¬∃ (a : Fin 14) (b : Fin 14), 14 * (a : ℕ) + (b : ℕ) ∈ codes ∧ x1 a = true ∧ x1 b = true) :
    ∃ m ∈ L, ∀ (i : Fin 14), x1 i = true → m.testBit ↑i = true := by
  obtain ⟨s, hs, hbits⟩ := mask_exists 14 (fun i => if h : i < 14 then x1 ⟨i, h⟩ else false)
  have hb : ∀ i : Fin 14, s.testBit ↑i = x1 i := by
    intro i
    rw [hbits _ i.isLt, dif_pos i.isLt]
  have hs2 : s < 16384 := by
    have h2 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    omega
  have hind : indep s = true := by
    unfold indep
    rw [List.all_eq_true]
    intro c hc
    by_contra hcon
    have hboth : s.testBit (c / 14) = true ∧ s.testBit (c % 14) = true := by
      revert hcon
      cases s.testBit (c / 14) <;> cases s.testBit (c % 14) <;> simp
    have hc196 := codes_lt c hc
    have ha : c / 14 < 14 := by omega
    have hbm : c % 14 < 14 := Nat.mod_lt _ (by decide)
    apply hx
    refine ⟨⟨c / 14, ha⟩, ⟨c % 14, hbm⟩, ?_, ?_, ?_⟩
    · show 14 * (c / 14) + c % 14 ∈ codes
      rw [Nat.div_add_mod]
      exact hc
    · exact (hb ⟨c / 14, ha⟩).symm.trans hboth.1
    · exact (hb ⟨c % 14, hbm⟩).symm.trans hboth.2
  have hcov := check_spec 16384 check_ok s hs2 hind
  unfold covered at hcov
  rw [List.any_eq_true] at hcov
  obtain ⟨m, hm, hbeq⟩ := hcov
  have hland : Nat.land s m = s := Nat.eq_of_beq_eq_true hbeq
  refine ⟨m, hm, fun i hi => ?_⟩
  have h1 : s.testBit ↑i = true := (hb i).trans hi
  have h2 : (Nat.land s m).testBit ↑i = true := by
    rw [hland]
    exact h1
  have h3 : (s &&& m).testBit ↑i = true := h2
  rw [Nat.testBit_land] at h3
  exact (Bool.and_eq_true_iff.1 h3).2

end PEqualNP.Outside.L_meta_8335

theorem PEqualNP.Outside.L_meta_8335 : ∀ (x1 : Fin (14 : ℕ) → Bool),   (¬∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true) →     ∃       x3 ∈         have x4 : List ℕ :=           have x4 : List ℕ :=             have x4 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];             (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x4;           have x5 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x4;           (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x5;         have x5 : List ℕ :=           have x5 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x4;           (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x5;         have x6 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x5;         (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x6,       ∀ (x4 : Fin (14 : ℕ)), x1 x4 = Bool.true → x3.testBit ↑x4 = Bool.true := by
  intro x1 hx
  exact PEqualNP.Outside.L_meta_8335.main x1 hx
