import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Helpers.PolyBelowExp

/-!
# Evasion chain: exponential padding (`StmtPadExp`)

`padP s x = 1^((s-1)|x|) ++ false :: x` has length `s|x| + 1`. The unpadder `padU s y` returns
the part after the first `false` when the leading run of `y` has exactly `(s-1)` times its
length, and the empty string otherwise; so `|padU s y| * s ≤ |y|` and `padU s (padP s x) = x`.
Both are polynomial-time, by the string combinators of `Universal/PrimsCPT.lean`. The padded
language is `{y | padU s y ∈ L}`; each direction is one `comp_time`.
-/

namespace PEqualNP.Library.Evasion

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines

local notation "CPTm" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptE {f f' : List Bool → List Bool} (h : CPTm f) (e : ∀ a, f a = f' a) :
    CPTm f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- Nonempty exactly when the first string is no longer than the second. -/
def leF (a b : List Bool) : List Bool := if a.length ≤ b.length then [true] else []

theorem cpt_leF {a b : List Bool → List Bool} (ha : CPTm a) (hb : CPTm b) :
    CPTm (fun y => leF (a y) (b y)) :=
  cptE (cpt_bitFlag (cpt_comp (cpt_pair hb ha) LenCmp.lenLE_polyTime)) (fun y => by simp [leF])

/-- `1^((s-1) * |rest after the first false|)`. -/
def padM (s : ℕ) (y : List Bool) : List Bool := mulU (un (s - 1)) (dropN y)

/-- The unpadder. -/
def padU (s : ℕ) (y : List Bool) : List Bool :=
  sel (leF (hd y) (padM s y)) [] (sel (leF (padM s y) (hd y)) [] (dropN y))

/-- The padder. -/
def padP (s : ℕ) (x : List Bool) : List Bool := mulU (un (s - 1)) x ++ ([false] ++ x)

theorem cpt_padU (s : ℕ) : CPTm (padU s) := by
  have hM : CPTm (padM s) :=
    cptE (cpt_mulU2 (cpt_const (un (s - 1))) cpt_dropN) (fun _ => rfl)
  exact cptE (cpt_sel (cpt_leF cpt_hd hM) (cpt_const [])
    (cpt_sel (cpt_leF hM cpt_hd) (cpt_const []) cpt_dropN)) (fun _ => rfl)

theorem cpt_padP (s : ℕ) : CPTm (padP s) :=
  cptE (cpt_app2 (cpt_mulU2 (cpt_const (un (s - 1))) cpt_id)
    (cpt_app2 (cpt_const [false]) cpt_id)) (fun _ => rfl)

theorem padP_eq (s : ℕ) (x : List Bool) : padP s x = un ((s - 1) * x.length) ++ false :: x := by
  simp [padP, mulU]

theorem padP_length (s : ℕ) (hs : 1 ≤ s) (x : List Bool) :
    (padP s x).length = s * x.length + 1 := by
  rw [padP_eq]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  simp only [List.length_append, un_length, List.length_cons, Nat.add_sub_cancel]
  ring

theorem padU_padP (s : ℕ) (x : List Bool) : padU s (padP s x) = x := by
  rw [padP_eq]
  have h1 := hd_un ((s - 1) * x.length) x
  have h2 := dropN_un ((s - 1) * x.length) x
  have hm : padM s (un ((s - 1) * x.length) ++ false :: x) = un ((s - 1) * x.length) := by
    rw [padM, h2, mulU, un_length]
  simp [padU, hm, h1, h2, leF, sel]

theorem dropN_split (y : List Bool) : dropN y = [] ∨ y = hd y ++ false :: dropN y := by
  induction y with
  | nil => left; rfl
  | cons b r ih =>
    cases b
    · right; simp [hd, dropN]
    · have e1 : hd (true :: r) = true :: hd r := by simp [hd]
      have e2 : dropN (true :: r) = dropN r := by simp [dropN]
      rw [e1, e2]
      rcases ih with h | h
      · left; exact h
      · right; exact congrArg (List.cons true) h

theorem padU_mul_le (s : ℕ) (hs : 1 ≤ s) (y : List Bool) : (padU s y).length * s ≤ y.length := by
  by_cases hA : leF (hd y) (padM s y) = []
  · simp [padU, sel, hA]
  by_cases hB : leF (padM s y) (hd y) = []
  · simp [padU, sel, hA, hB]
  have e : padU s y = dropN y := by simp [padU, sel, hA, hB]
  have hA' : (hd y).length ≤ (padM s y).length := by
    by_contra h; exact hA (by simp [leF, h])
  have hB' : (padM s y).length ≤ (hd y).length := by
    by_contra h; exact hB (by simp [leF, h])
  have hM : (padM s y).length = (s - 1) * (dropN y).length := by simp [padM, mulU]
  rw [e]
  rcases dropN_split y with h | h
  · rw [h]; simp
  · have hl := congrArg List.length h
    simp only [List.length_append, List.length_cons] at hl
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hM
    have : (hd y).length = s' * (dropN y).length := by omega
    rw [hl, this]
    nlinarith

theorem padU_le (s : ℕ) (hs : 1 ≤ s) (y : List Bool) : (padU s y).length ≤ y.length / s :=
  (Nat.le_div_iff_mul_le hs).2 (padU_mul_le s hs y)

theorem padExp : StmtPadExp := by
  intro s q hs hq L hL
  obtain ⟨K, fL, hfL, hcL⟩ := hL
  obtain ⟨pu, hpu⟩ := time_of_polyTime (cpt_padU s)
  obtain ⟨Cu, hCu⟩ := Helpers.polynomial_le_two_pow_pow_add_const pu 1 le_rfl
  have hA := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    Computability.encodeBool (padU s) fL (fun n => pu.eval n)
    (fun n => K * 2 ^ (q * s * n) + K) (fun n => n / s) hpu hcL
    (fun a b hab => by
      show K * 2 ^ (q * s * a) + K ≤ K * 2 ^ (q * s * b) + K
      exact Nat.add_le_add_right (Nat.mul_le_mul_left K
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hab))) K)
    (fun y => padU_le s hs y)
  refine ⟨{y | padU s y ∈ L}, ⟨K + Cu + 4, fun y => fL (padU s y), fun y => hfL _,
    time_mono hA fun n => ?_⟩, ?_⟩
  · show pu.eval n + (2 * (n / s) + 2) + (K * 2 ^ (q * s * (n / s)) + K) ≤
      (K + Cu + 4) * 2 ^ (q * n) + (K + Cu + 4)
    have b1 := hCu n
    rw [pow_one] at b1
    have b2 : n / s ≤ n := Nat.div_le_self n s
    have b3 : n < 2 ^ n := Nat.lt_two_pow_self
    have b4 : 2 ^ n ≤ 2 ^ (q * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left n hq)
    have b5 : 2 ^ (q * s * (n / s)) ≤ 2 ^ (q * n) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left q (Nat.mul_div_le n s)
    have b6 : K * 2 ^ (q * s * (n / s)) ≤ K * 2 ^ (q * n) := Nat.mul_le_mul_left K b5
    generalize 2 ^ (q * n) = E at *
    generalize 2 ^ n = F at *
    generalize K * 2 ^ (q * s * (n / s)) = G at *
    have hE : 1 ≤ E := by omega
    nlinarith [Nat.mul_le_mul_left Cu hE]
  · intro t ht hL'
    obtain ⟨K2, g, hg, hcg⟩ := hL'
    obtain ⟨pp, hpp⟩ := time_of_polyTime (cpt_padP s)
    obtain ⟨Cp, hCp⟩ := Helpers.polynomial_le_two_pow_pow_add_const pp 1 le_rfl
    have hC := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
      Computability.encodeBool (padP s) g (fun n => pp.eval n)
      (fun n => K2 * t n + K2) (fun m => s * m + 1) hpp hcg
      (fun a b hab => Nat.add_le_add_right (Nat.mul_le_mul_left K2 (ht hab)) K2)
      (fun x => le_of_eq (padP_length s hs x))
    refine ⟨K2 + Cp + 2 * s + 4, fun x => g (padP s x), fun x => ?_, time_mono hC fun m => ?_⟩
    · rw [← hg]
      show x ∈ L ↔ padU s (padP s x) ∈ L
      rw [padU_padP]
    · show pp.eval m + (2 * (s * m + 1) + 2) + (K2 * t (s * m + 1) + K2) ≤
        (K2 + Cp + 2 * s + 4) * (t (s * m + 1) + 2 ^ m) + (K2 + Cp + 2 * s + 4)
      have b1 := hCp m
      rw [pow_one] at b1
      have b3 : m < 2 ^ m := Nat.lt_two_pow_self
      have b4 : s * m ≤ s * 2 ^ m := Nat.mul_le_mul_left s b3.le
      generalize t (s * m + 1) = T at *
      generalize 2 ^ m = E at *
      nlinarith [Nat.zero_le (Cp * T), Nat.zero_le (s * T), Nat.zero_le (Cp * E)]

end PEqualNP.Library.Evasion
