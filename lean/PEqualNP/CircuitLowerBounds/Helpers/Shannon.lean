import PEqualNP.CircuitLowerBounds.Helpers.Count

/-!
Helpers for L-clb-005: for every polynomial size bound the descriptor count falls below the
number of functions at some length, and a language that is hard at every such length.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

theorem exists_lin_lt_two_pow (A c : ℕ) : ∃ m, A + c * m < 2 ^ m := by
  generalize hk : A + 2 * c + 1 = k
  refine ⟨2 * k, ?_⟩
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
  have h3 : k * k < 2 ^ k * 2 ^ k := Nat.mul_lt_mul'' h1 h1
  have e : k * k = k * A + 2 * c * k + k := by rw [← hk]; ring
  have hA : A ≤ k * A := Nat.le_mul_of_pos_left _ (by omega)
  rw [h2]
  nlinarith

theorem poly_le_pow (p : Polynomial ℕ) : ∃ e, ∀ n, 2 ≤ n → p.eval n ≤ n ^ e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 1, fun n hn => ?_⟩
    rw [Polynomial.eval_add]
    have h1 : n ^ a ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : n ^ b ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : n ^ (a + b + 1) = n ^ (a + b) * n := pow_succ _ _
    have h4 := Nat.mul_le_mul_left (n ^ (a + b)) hn
    have := ha n hn
    have := hb n hn
    omega
  | monomial k a =>
    refine ⟨a + k, fun n hn => ?_⟩
    rw [Polynomial.eval_monomial, pow_add]
    have : a ≤ n ^ a := le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hn a)
    exact Nat.mul_le_mul_right _ this

theorem count_le (n e q : ℕ) (hn : 2 ≤ n) (he : 1 ≤ e) (hq : q ≤ n ^ e) :
    count n q ≤ n ^ ((3 * e + 8) * n ^ e) := by
  have hn0 : 0 < n := by omega
  have hpos : 1 ≤ n ^ e := Nat.one_le_pow _ _ hn0
  have ha : n ≤ n ^ e := Nat.le_self_pow (by omega) n
  have h4 : 4 ≤ n ^ 2 := by nlinarith
  have hb : n + q + 2 ≤ n ^ (e + 2) := by
    rw [pow_add]; nlinarith
  have hc : 3 * ((n + q + 2) * (n + q + 2)) ≤ n ^ (2 * e + 6) := by
    have : n ^ (2 * e + 6) = n ^ 2 * (n ^ (e + 2) * n ^ (e + 2)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]
    have := Nat.mul_le_mul hb hb
    nlinarith
  have hd : (3 * ((n + q + 2) * (n + q + 2))) ^ q ≤ n ^ ((2 * e + 6) * n ^ e) := by
    calc (3 * ((n + q + 2) * (n + q + 2))) ^ q ≤ (n ^ (2 * e + 6)) ^ q :=
          Nat.pow_le_pow_left hc q
      _ ≤ (n ^ (2 * e + 6)) ^ (n ^ e) :=
          Nat.pow_le_pow_right (Nat.one_le_pow _ _ hn0) hq
      _ = n ^ ((2 * e + 6) * n ^ e) := by rw [← pow_mul]
  have he' : n + q + 1 ≤ n ^ ((e + 2) * n ^ e) := by
    calc n + q + 1 ≤ n ^ (e + 2) := by omega
      _ ≤ n ^ ((e + 2) * n ^ e) :=
          Nat.pow_le_pow_right hn0 (Nat.le_mul_of_pos_right _ hpos)
  calc count n q ≤ n ^ ((2 * e + 6) * n ^ e) * n ^ ((e + 2) * n ^ e) :=
        Nat.mul_le_mul hd he'
    _ = n ^ ((3 * e + 8) * n ^ e) := by rw [← pow_add]; congr 1; ring

theorem exists_count_lt (p : Polynomial ℕ) : ∃ n, count n (p.eval n) < 2 ^ 2 ^ n := by
  obtain ⟨e0, he0⟩ := poly_le_pow p
  obtain ⟨m, hm⟩ := exists_lin_lt_two_pow (3 * (e0 + 1) + 8) (e0 + 2)
  have hm1 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    subst this
    simp at hm
  refine ⟨2 ^ m, ?_⟩
  generalize hn' : 2 ^ m = n at *
  have hn : 2 ≤ n := by
    rw [← hn']
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm1
  have hn0 : 0 < n := by omega
  have hq : p.eval n ≤ n ^ (e0 + 1) :=
    le_trans (he0 n hn) (Nat.pow_le_pow_right hn0 (by omega))
  have h1 := count_le n (e0 + 1) (p.eval n) hn (by omega) hq
  have hKpos : (3 * (e0 + 1) + 8) * n ^ (e0 + 1) ≠ 0 := by
    have : 1 ≤ n ^ (e0 + 1) := Nat.one_le_pow _ _ hn0
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) this)
  have h2 : n ^ ((3 * (e0 + 1) + 8) * n ^ (e0 + 1)) <
      (2 ^ n) ^ ((3 * (e0 + 1) + 8) * n ^ (e0 + 1)) :=
    Nat.pow_lt_pow_left Nat.lt_two_pow_self hKpos
  have h3 : n * ((3 * (e0 + 1) + 8) * n ^ (e0 + 1)) ≤ 2 ^ n := by
    have hA : 3 * (e0 + 1) + 8 ≤ 2 ^ (3 * (e0 + 1) + 8) := le_of_lt Nat.lt_two_pow_self
    have hpow : n * n ^ (e0 + 1) = 2 ^ ((e0 + 2) * m) := by
      rw [← hn', ← pow_succ', ← pow_mul]; congr 1; ring
    calc n * ((3 * (e0 + 1) + 8) * n ^ (e0 + 1))
        = (3 * (e0 + 1) + 8) * (n * n ^ (e0 + 1)) := by ring
      _ ≤ 2 ^ (3 * (e0 + 1) + 8) * 2 ^ ((e0 + 2) * m) := by
          rw [hpow]; exact Nat.mul_le_mul_right _ hA
      _ = 2 ^ (3 * (e0 + 1) + 8 + (e0 + 2) * m) := by rw [← pow_add]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (le_of_lt hm)
  calc count n (p.eval n) ≤ n ^ ((3 * (e0 + 1) + 8) * n ^ (e0 + 1)) := h1
    _ < (2 ^ n) ^ ((3 * (e0 + 1) + 8) * n ^ (e0 + 1)) := h2
    _ = 2 ^ (n * ((3 * (e0 + 1) + 8) * n ^ (e0 + 1))) := by rw [← pow_mul]
    _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by omega) h3

theorem self_lt_count (n s : ℕ) : s < count n s := by
  have : 1 ≤ (3 * ((n + s + 2) * (n + s + 2))) ^ s :=
    Nat.one_le_pow _ _ (by positivity)
  calc s < n + s + 1 := by omega
    _ = 1 * (n + s + 1) := (one_mul _).symm
    _ ≤ count n s := Nat.mul_le_mul_right _ this

open Classical in
/-- The largest size bound the counting argument beats at length `n`. -/
noncomputable def bestSize (n : ℕ) : ℕ :=
  Nat.findGreatest (fun s => count n s < 2 ^ 2 ^ n) (2 ^ 2 ^ n)

open Classical in
/-- A function on `n` bits with no basic circuit of at most `bestSize n` gates, when the
counting argument gives one. -/
noncomputable def hard (n : ℕ) : (Fin n → Bool) → Bool :=
  if h : count n (bestSize n) < 2 ^ 2 ^ n then Classical.choose (exists_hard n (bestSize n) h)
  else fun _ => false

/-- The language whose slice at each length `n` is `hard n`. -/
def hardLang : Language Bool :=
  {x : List Bool | ∃ (n : ℕ) (v : Fin n → Bool), x = List.ofFn v ∧ hard n v = true}

theorem mem_hardLang {n : ℕ} (v : Fin n → Bool) :
    List.ofFn v ∈ hardLang ↔ hard n v = true := by
  constructor
  · rintro ⟨n', v', h, hv⟩
    have h' := List.ofFn_inj'.mp h
    cases h'
    exact hv
  · intro h
    exact ⟨n, v, rfl, h⟩

theorem hardLang_not_ppoly : hardLang ∉ PPoly := by
  rintro ⟨p, hp⟩
  obtain ⟨n, hn⟩ := exists_count_lt p
  have hb : p.eval n ≤ 2 ^ 2 ^ n := le_of_lt (lt_trans (self_lt_count _ _) hn)
  have hle : p.eval n ≤ bestSize n := by
    classical
    exact Nat.le_findGreatest hb hn
  have hS : count n (bestSize n) < 2 ^ 2 ^ n := by
    classical
    exact Nat.findGreatest_spec (P := fun s => count n s < 2 ^ 2 ^ n) hb hn
  obtain ⟨C, hC, hsize, hdec⟩ := hp n
  have hspec := Classical.choose_spec (exists_hard n (bestSize n) hS)
  obtain ⟨v, hv⟩ := hspec C hC (le_trans hsize hle)
  apply hv
  have h1 := hdec (List.ofFn v) List.length_ofFn
  rw [mem_hardLang] at h1
  have h2 : hard n = Classical.choose (exists_hard n (bestSize n) hS) := by
    simp [hard, hS]
  rw [← h2]
  exact Bool.eq_iff_iff.mpr h1

end PEqualNP.CircuitLowerBounds.Helpers
