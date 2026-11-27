import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7647

def EL : List ℕ := [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95]

def XL : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338,
  2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288,
  9992, 10273, 10656, 12353, 13504, 14849, 16256]

def MS : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22]

def good (N : ℕ) : Bool :=
  !((EL.all fun c => !(N.testBit (c / 14) && N.testBit (c % 14))) &&
    ((List.range 14).all fun i => N.testBit i || (N &&& MS.getD i 0 != 0))) || decide (N ∈ XL)

theorem good_all :
    ((List.range 128).all fun h => (List.range 128).all fun l => good (128 * h + l)) = true := by
  decide +kernel

theorem good_lt (N : ℕ) (hN : N < 16384) : good N = true := by
  have h := good_all
  simp only [List.all_eq_true, List.mem_range] at h
  have h2 := h (N / 128) (by omega) (N % 128) (by omega)
  rwa [Nat.div_add_mod N 128] at h2

def enc : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (enc l)

theorem enc_testBit : ∀ (l : List Bool) (i : ℕ), (enc l).testBit i = l.getD i false
  | [], i => by simp [enc]
  | b :: l, 0 => by simp [enc, Nat.testBit_bit_zero]
  | b :: l, i + 1 => by
    show (Nat.bit b (enc l)).testBit (Nat.succ i) = _
    rw [Nat.testBit_bit_succ, enc_testBit l i]
    simp

theorem adjM : ∀ a b : Fin 14, 14 * (a : ℕ) + (b : ℕ) ∈ EL →
    (MS.getD a 0).testBit b = true ∧ (MS.getD b 0).testBit a = true := by
  decide +kernel

theorem noLoop : ∀ a : Fin 14, 14 * (a : ℕ) + (a : ℕ) ∉ EL := by
  decide +kernel

theorem elFin : ∀ c ∈ EL, c / 14 < 14 ∧ c % 14 < 14 ∧ 14 * (c / 14) + c % 14 ∈ EL := by
  decide +kernel

theorem land_ne (N M j : ℕ) (h1 : N.testBit j = true) (h2 : M.testBit j = true) :
    (N &&& M != 0) = true := by
  have h3 : (N &&& M).testBit j = true := by rw [Nat.testBit_land, h1, h2]; rfl
  rw [bne_iff_ne]
  intro h
  rw [h, Nat.zero_testBit] at h3
  exact Bool.false_ne_true h3

end PEqualNP.Outside.L_meta_7647

theorem PEqualNP.Outside.L_meta_7647 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∀ (x2 : Fin (14 : ℕ) → Bool),   ¬x1 x2 →     (∀ (x4 : Fin (14 : ℕ) → Bool), x2 ≤ x4 → ¬x1 x4 → x4 = x2) →       ∃         x5 ∈           have x6 : List ℕ :=             have x6 : List ℕ :=               have x6 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];               (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x6;             have x7 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x6;             (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x7;           have x7 : List ℕ :=             have x7 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x6;             (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x7;           have x8 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x7;           (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x8,         (fun (x6 : Fin (14 : ℕ)) => x5.testBit ↑x6) = x2 := by
  dsimp only
  intro x2 hx hmax
  obtain ⟨N, hbit, hlt⟩ : ∃ N : ℕ, (∀ i : Fin 14, N.testBit i = x2 i) ∧ N < 16384 := by
    refine ⟨PEqualNP.Outside.L_meta_7647.enc (List.ofFn x2), ?_, ?_⟩
    · intro i
      rw [PEqualNP.Outside.L_meta_7647.enc_testBit,
        List.getD_eq_getElem (l := List.ofFn x2) (d := false) (n := (i : ℕ))
          (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
    · have := Nat.lt_pow_two_of_testBit (n := 14) (PEqualNP.Outside.L_meta_7647.enc (List.ofFn x2))
        (fun i hi => by
          rw [PEqualNP.Outside.L_meta_7647.enc_testBit]
          exact List.getD_eq_default (l := List.ofFn x2) (d := false) (by rw [List.length_ofFn]; omega))
      simpa using this
  have hind : (PEqualNP.Outside.L_meta_7647.EL.all
      fun c => !(N.testBit (c / 14) && N.testBit (c % 14))) = true := by
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨h1, h2, h3⟩ := PEqualNP.Outside.L_meta_7647.elFin c hc
    by_contra hcon
    have ha : N.testBit (c / 14) = true := by
      revert hcon; cases N.testBit (c / 14) <;> simp
    have hb : N.testBit (c % 14) = true := by
      revert hcon; cases N.testBit (c % 14) <;> simp
    exact hx ⟨⟨c / 14, h1⟩, ⟨c % 14, h2⟩, h3, (hbit ⟨c / 14, h1⟩).symm.trans ha,
      (hbit ⟨c % 14, h2⟩).symm.trans hb⟩
  have hmx : ((List.range 14).all fun i =>
      N.testBit i || (N &&& PEqualNP.Outside.L_meta_7647.MS.getD i 0 != 0)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    cases hxi : x2 ⟨i, hi⟩
    · have hy : ∃ a b : Fin 14, 14 * (a : ℕ) + (b : ℕ) ∈ PEqualNP.Outside.L_meta_7647.EL ∧
          Function.update x2 ⟨i, hi⟩ true a = true ∧ Function.update x2 ⟨i, hi⟩ true b = true := by
        by_contra hne
        have hle : x2 ≤ Function.update x2 ⟨i, hi⟩ true := Pi.le_def.2 fun j => by
          by_cases hj : j = ⟨i, hi⟩
          · subst hj; simp [hxi]
          · simp [Function.update_of_ne hj]
        have h5 := hmax (Function.update x2 ⟨i, hi⟩ true) hle hne
        have h6 := congrFun h5 ⟨i, hi⟩
        simp [hxi] at h6
      obtain ⟨a, b, hab, hya, hyb⟩ := hy
      have hupd : ∀ j : Fin 14, j ≠ ⟨i, hi⟩ → Function.update x2 ⟨i, hi⟩ true j = x2 j :=
        fun j hj => Function.update_of_ne hj _ _
      suffices hs : (N &&& PEqualNP.Outside.L_meta_7647.MS.getD i 0 != 0) = true by
        rw [hs, Bool.or_true]
      by_cases ha : a = ⟨i, hi⟩
      · subst ha
        by_cases hb : b = ⟨i, hi⟩
        · subst hb
          exact absurd hab (PEqualNP.Outside.L_meta_7647.noLoop _)
        · have hxb : x2 b = true := by rw [← hupd b hb]; exact hyb
          exact PEqualNP.Outside.L_meta_7647.land_ne N _ b ((hbit b).trans hxb)
            (PEqualNP.Outside.L_meta_7647.adjM _ b hab).1
      · have hxa : x2 a = true := by rw [← hupd a ha]; exact hya
        by_cases hb : b = ⟨i, hi⟩
        · subst hb
          exact PEqualNP.Outside.L_meta_7647.land_ne N _ a ((hbit a).trans hxa)
            (PEqualNP.Outside.L_meta_7647.adjM a _ hab).2
        · have hxb : x2 b = true := by rw [← hupd b hb]; exact hyb
          exact (hx ⟨a, b, hab, hxa, hxb⟩).elim
    · have ht : N.testBit i = true := (hbit ⟨i, hi⟩).trans hxi
      simp [ht]
  have hg := PEqualNP.Outside.L_meta_7647.good_lt N hlt
  unfold PEqualNP.Outside.L_meta_7647.good at hg
  rw [hind, hmx] at hg
  have hmem : N ∈ PEqualNP.Outside.L_meta_7647.XL := of_decide_eq_true hg
  exact ⟨N, hmem, funext fun i => hbit i⟩
