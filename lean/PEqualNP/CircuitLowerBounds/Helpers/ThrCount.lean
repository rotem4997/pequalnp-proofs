import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.Shannon

/-!
Helpers for L-clb-018: a counting lower bound for depth-two threshold circuits.

A threshold function is determined by its Chow parameters (the number of true points, and for
each coordinate the number of true points where that coordinate is true), so there are at most
`(2 ^ m + 1) ^ (m + 1)` threshold functions on `m` bits. A depth-two threshold circuit with at
most `K` bottom gates computes a composition of `K` threshold functions on the inputs with one
threshold function on `K` bits, so few functions have such a circuit. For a polynomial `K` the
count falls below the number of Boolean functions at some length.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-- A bit as an integer. -/
def bz (b : Bool) : ℤ := if b = true then 1 else 0

theorem bz_nonneg (b : Bool) : 0 ≤ bz b := by cases b <;> simp [bz]

theorem bz_le_one (b : Bool) : bz b ≤ 1 := by cases b <;> simp [bz]

/-- The weighted sum of the bits of `x`. -/
def lin {m : ℕ} (w : Fin m → ℤ) (x : Fin m → Bool) : ℤ := ∑ i, w i * bz (x i)

/-- The threshold function with weights `w` and threshold `t`. -/
def thrFun {m : ℕ} (w : Fin m → ℤ) (t : ℤ) (x : Fin m → Bool) : Bool := decide (t ≤ lin w x)

/-- The number of true points of `f`. -/
def chow0 {m : ℕ} (f : (Fin m → Bool) → Bool) : ℤ := ∑ x, bz (f x)

/-- The number of true points of `f` where coordinate `i` is true. -/
def chow1 {m : ℕ} (f : (Fin m → Bool) → Bool) (i : Fin m) : ℤ := ∑ x, bz (f x) * bz (x i)

/-- Chow's theorem: a function with the Chow parameters of a threshold function is that
threshold function. -/
theorem chow_inj {m : ℕ} (w : Fin m → ℤ) (t : ℤ) (f : (Fin m → Bool) → Bool)
    (h0 : chow0 f = chow0 (thrFun w t)) (h1 : chow1 f = chow1 (thrFun w t)) :
    f = thrFun w t := by
  have hD0 : ∑ x, (bz (thrFun w t x) - bz (f x)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have := h0
    unfold chow0 at this
    rw [this]; ring
  have hDi : ∀ i, ∑ x, (bz (thrFun w t x) - bz (f x)) * bz (x i) = 0 := by
    intro i
    simp only [sub_mul, Finset.sum_sub_distrib]
    have := congrFun h1 i
    unfold chow1 at this
    rw [this]; ring
  have hsum : ∑ x, (bz (thrFun w t x) - bz (f x)) * (2 * lin w x - 2 * t + 1) = 0 := by
    have e : ∀ x, (bz (thrFun w t x) - bz (f x)) * (2 * lin w x - 2 * t + 1) =
        2 * ∑ i, w i * ((bz (thrFun w t x) - bz (f x)) * bz (x i)) -
          (2 * t - 1) * (bz (thrFun w t x) - bz (f x)) := by
      intro x
      have : ∑ i, w i * ((bz (thrFun w t x) - bz (f x)) * bz (x i)) =
          (bz (thrFun w t x) - bz (f x)) * lin w x := by
        unfold lin
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; ring
    simp only [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hD0, Finset.sum_comm]
    have : ∑ i, ∑ x, w i * ((bz (thrFun w t x) - bz (f x)) * bz (x i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, hDi i, mul_zero]
    rw [this]; ring
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (Fin m → Bool)),
      0 ≤ (bz (thrFun w t x) - bz (f x)) * (2 * lin w x - 2 * t + 1) := by
    intro x _
    have hf0 := bz_nonneg (f x)
    have hf1 := bz_le_one (f x)
    by_cases hg : t ≤ lin w x
    · have : bz (thrFun w t x) = 1 := by simp [thrFun, bz, hg]
      rw [this]
      exact mul_nonneg (by linarith) (by linarith)
    · have : bz (thrFun w t x) = 0 := by simp [thrFun, bz, hg]
      rw [this]
      have hg' : lin w x ≤ t - 1 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  funext x
  have hx := hzero x (Finset.mem_univ x)
  rcases mul_eq_zero.mp hx with h | h
  · revert h
    cases f x <;> cases thrFun w t x <;> simp [bz]
  · omega

open Classical in
/-- The threshold functions on `m` bits. -/
noncomputable def thrSet (m : ℕ) : Finset ((Fin m → Bool) → Bool) :=
  Finset.univ.filter fun f => ∃ (w : Fin m → ℤ) (t : ℤ), f = thrFun w t

theorem mem_thrSet {m : ℕ} (w : Fin m → ℤ) (t : ℤ) : thrFun w t ∈ thrSet m := by
  classical
  simp only [thrSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨w, t, rfl⟩

theorem sum_one_bits (m : ℕ) : ∑ _x : Fin m → Bool, (1 : ℤ) = 2 ^ m := by
  simp

theorem chow0_mem {m : ℕ} (f : (Fin m → Bool) → Bool) :
    chow0 f ∈ Finset.Icc (0 : ℤ) (2 ^ m) := by
  rw [Finset.mem_Icc]
  constructor
  · exact Finset.sum_nonneg fun x _ => bz_nonneg _
  · rw [← sum_one_bits m]
    exact Finset.sum_le_sum fun x _ => bz_le_one _

theorem chow1_mem {m : ℕ} (f : (Fin m → Bool) → Bool) (i : Fin m) :
    chow1 f i ∈ Finset.Icc (0 : ℤ) (2 ^ m) := by
  rw [Finset.mem_Icc]
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (bz_nonneg _) (bz_nonneg _)
  · rw [← sum_one_bits m]
    refine Finset.sum_le_sum fun x _ => ?_
    have a0 := bz_nonneg (f x)
    have a1 := bz_le_one (f x)
    have b0 := bz_nonneg (x i)
    have b1 := bz_le_one (x i)
    nlinarith

theorem card_Icc_two_pow (m : ℕ) : (Finset.Icc (0 : ℤ) (2 ^ m)).card = 2 ^ m + 1 := by
  rw [Int.card_Icc]
  have : ((2 : ℤ) ^ m + 1 - 0) = ((2 ^ m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

/-- There are at most `(2 ^ m + 1) ^ (m + 1)` threshold functions on `m` bits. -/
theorem card_thrSet_le (m : ℕ) : (thrSet m).card ≤ (2 ^ m + 1) ^ (m + 1) := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := thrSet m)
    (t := Finset.Icc (0 : ℤ) (2 ^ m) ×ˢ
      Fintype.piFinset (fun _ : Fin m => Finset.Icc (0 : ℤ) (2 ^ m)))
    (fun f => (chow0 f, chow1 f))
    (fun f _ => Finset.mem_product.mpr
      ⟨chow0_mem f, Fintype.mem_piFinset.mpr fun i => chow1_mem f i⟩)
    (by
      intro f _ g hg hfg
      have hg' := hg
      simp only [thrSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg'
      obtain ⟨w, t, rfl⟩ := hg'
      have h0 : chow0 f = chow0 (thrFun w t) := congrArg Prod.fst hfg
      have h1 : chow1 f = chow1 (thrFun w t) := congrArg Prod.snd hfg
      exact chow_inj w t f h0 h1)
  rw [Finset.card_product, Fintype.card_piFinset_const, card_Icc_two_pow,
    ← pow_succ'] at h
  exact h

/-- The function of a depth-two circuit: bottom functions `g`, top function `h`. -/
def thrComp {n K : ℕ} (g : Fin K → (Fin n → Bool) → Bool) (h : (Fin K → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => h fun j => g j x

open Classical in
/-- The functions on `n` bits computed by a depth-two threshold circuit with exactly `K`
bottom gates. -/
noncomputable def circSet (n K : ℕ) : Finset ((Fin n → Bool) → Bool) :=
  Finset.image
    (fun p : (Fin K → (Fin n → Bool) → Bool) × ((Fin K → Bool) → Bool) => thrComp p.1 p.2)
    (Fintype.piFinset (fun _ : Fin K => thrSet n) ×ˢ thrSet K)

/-- The bound on the number of functions with a depth-two threshold circuit of `K` gates. -/
def thrCount (n K : ℕ) : ℕ := ((2 ^ n + 1) ^ (n + 1)) ^ K * (2 ^ K + 1) ^ (K + 1)

theorem card_circSet_le (n K : ℕ) : (circSet n K).card ≤ thrCount n K := by
  classical
  unfold circSet thrCount
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product, Fintype.card_piFinset_const]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_thrSet_le n) K) (card_thrSet_le K)

/-- A function with a depth-two threshold circuit of at most `K` bottom gates is in
`circSet n K`: pad with gates of top weight zero. -/
theorem mem_circSet {n k K : ℕ} (hk : k ≤ K) (w : Fin k → Fin n → ℤ) (t : Fin k → ℤ)
    (a : Fin k → ℤ) (t0 : ℤ) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin n → Bool, f x = true ↔
      t0 ≤ ∑ j : Fin k, a j *
        (if t j ≤ ∑ i : Fin n, w j i * (if x i = true then 1 else 0) then 1 else 0)) :
    f ∈ circSet n K := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold circSet
  rw [Finset.mem_image]
  refine ⟨(fun j => thrFun (Fin.append w (fun _ _ => 0) j) (Fin.append t (fun _ => 0) j),
    thrFun (Fin.append a (fun _ => 0)) t0), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr fun j => mem_thrSet _ _, mem_thrSet _ _⟩
  · funext x
    rw [Bool.eq_iff_iff, hf x]
    simp [thrComp, thrFun, lin, bz, Fin.sum_univ_add]

theorem exists_thrHard (n K : ℕ) (h : thrCount n K < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, f ∉ circSet n K := by
  by_contra hcon
  have hall : ∀ f, f ∈ circSet n K := by
    intro f
    by_contra hf
    exact hcon ⟨f, hf⟩
  have huniv : circSet n K = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  have hcard : (circSet n K).card = 2 ^ 2 ^ n := by
    rw [huniv, Finset.card_univ]
    simp
  have := card_circSet_le n K
  omega

theorem thrCount_le_pow (n K : ℕ) :
    thrCount n K ≤ 2 ^ ((n + 1) * (n + 1) * K + (K + 1) * (K + 1)) := by
  have h1 : ∀ m : ℕ, 2 ^ m + 1 ≤ 2 ^ (m + 1) := by
    intro m
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ]; omega
  unfold thrCount
  calc ((2 ^ n + 1) ^ (n + 1)) ^ K * (2 ^ K + 1) ^ (K + 1)
      ≤ ((2 ^ (n + 1)) ^ (n + 1)) ^ K * (2 ^ (K + 1)) ^ (K + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.pow_le_pow_left (h1 n) _) _)
          (Nat.pow_le_pow_left (h1 K) _)
    _ = 2 ^ ((n + 1) * (n + 1) * K + (K + 1) * (K + 1)) := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, mul_assoc]

theorem exists_thrCount_lt (p : Polynomial ℕ) : ∃ n, thrCount n (p.eval n) < 2 ^ 2 ^ n := by
  obtain ⟨e, he⟩ := poly_le_pow p
  obtain ⟨m, hm⟩ := exists_lin_lt_two_pow 1 (2 * e + 5)
  have hm1 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    subst this
    simp at hm
  refine ⟨2 ^ m, ?_⟩
  have hpow : (2 ^ m) ^ (2 * e + 5) = 2 ^ ((2 * e + 5) * m) := by
    rw [← pow_mul]; congr 1; ring
  generalize hn' : 2 ^ m = n at *
  have hn : 2 ≤ n := by
    rw [← hn']
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm1
  have hn0 : 0 < n := by omega
  generalize hK : p.eval n = K
  have hKQ : K ≤ n ^ e := hK ▸ he n hn
  generalize hQ : n ^ e = Q at hKQ
  have hQ1 : 1 ≤ Q := hQ ▸ Nat.one_le_pow _ _ hn0
  have hQQ : Q ≤ Q * Q := Nat.le_mul_of_pos_left _ hQ1
  have hn2 : n + 1 ≤ n ^ 2 := by nlinarith
  have hn4 : (n + 1) * (n + 1) ≤ n ^ 4 := by
    calc (n + 1) * (n + 1) ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul hn2 hn2
      _ = n ^ 4 := by ring
  have hA : (n + 1) * (n + 1) * K ≤ n ^ 4 * (Q * Q) :=
    Nat.mul_le_mul hn4 (le_trans hKQ hQQ)
  have hK1 : K + 1 ≤ n * Q := by nlinarith
  have hn24 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right hn0 (by omega)
  have hB : (K + 1) * (K + 1) ≤ n ^ 4 * (Q * Q) := by
    calc (K + 1) * (K + 1) ≤ (n * Q) * (n * Q) := Nat.mul_le_mul hK1 hK1
      _ = n ^ 2 * (Q * Q) := by ring
      _ ≤ n ^ 4 * (Q * Q) := Nat.mul_le_mul_right _ hn24
  have hE : (n + 1) * (n + 1) * K + (K + 1) * (K + 1) ≤ n ^ (2 * e + 5) := by
    have h5 : n ^ (2 * e + 5) = n * (n ^ 4 * (Q * Q)) := by
      rw [← hQ]; ring
    rw [h5]
    have : 2 * (n ^ 4 * (Q * Q)) ≤ n * (n ^ 4 * (Q * Q)) := Nat.mul_le_mul_right _ hn
    omega
  have hlt : (2 * e + 5) * m < n := by omega
  calc thrCount n K ≤ 2 ^ ((n + 1) * (n + 1) * K + (K + 1) * (K + 1)) := thrCount_le_pow n K
    _ ≤ 2 ^ (n ^ (2 * e + 5)) := Nat.pow_le_pow_right (by omega) hE
    _ = 2 ^ (2 ^ ((2 * e + 5) * m)) := by rw [hpow]
    _ < 2 ^ 2 ^ n :=
        Nat.pow_lt_pow_right (by omega) (Nat.pow_lt_pow_right (by omega) hlt)

theorem self_lt_thrCount (n s : ℕ) : s < thrCount n s := by
  have h1 : 1 ≤ ((2 ^ n + 1) ^ (n + 1)) ^ s := Nat.one_le_pow _ _ (by positivity)
  have h2 : 2 ^ s + 1 ≤ (2 ^ s + 1) ^ (s + 1) := Nat.le_self_pow (by omega) _
  have h3 : s < 2 ^ s := Nat.lt_two_pow_self
  calc s < 2 ^ s + 1 := by omega
    _ ≤ (2 ^ s + 1) ^ (s + 1) := h2
    _ = 1 * (2 ^ s + 1) ^ (s + 1) := (one_mul _).symm
    _ ≤ thrCount n s := Nat.mul_le_mul_right _ h1

open Classical in
/-- The largest number of bottom gates the counting argument beats at length `n`. -/
noncomputable def thrBestSize (n : ℕ) : ℕ :=
  Nat.findGreatest (fun s => thrCount n s < 2 ^ 2 ^ n) (2 ^ 2 ^ n)

open Classical in
/-- A function on `n` bits with no depth-two threshold circuit of at most `thrBestSize n`
bottom gates, when the counting argument gives one. -/
noncomputable def thrHard (n : ℕ) : (Fin n → Bool) → Bool :=
  if h : thrCount n (thrBestSize n) < 2 ^ 2 ^ n then
    Classical.choose (exists_thrHard n (thrBestSize n) h)
  else fun _ => false

/-- The language whose slice at each length `n` is `thrHard n`. -/
def thrHardLang : Language Bool :=
  {x : List Bool | ∃ (n : ℕ) (v : Fin n → Bool), x = List.ofFn v ∧ thrHard n v = true}

theorem mem_thrHardLang {n : ℕ} (v : Fin n → Bool) :
    List.ofFn v ∈ thrHardLang ↔ thrHard n v = true := by
  constructor
  · rintro ⟨n', v', h, hv⟩
    have h' := List.ofFn_inj'.mp h
    cases h'
    exact hv
  · intro h
    exact ⟨n, v, rfl, h⟩

/-- The hard language has no depth-two threshold circuits of polynomial size. -/
theorem thrHardLang_not_thrthr (p : Polynomial ℕ) :
    thrHardLang ∉ THRTHR (fun n => p.eval n) := by
  intro hp
  obtain ⟨n, hn⟩ := exists_thrCount_lt p
  have hb : p.eval n ≤ 2 ^ 2 ^ n := le_of_lt (lt_trans (self_lt_thrCount _ _) hn)
  have hle : p.eval n ≤ thrBestSize n := by
    classical
    exact Nat.le_findGreatest hb hn
  have hS : thrCount n (thrBestSize n) < 2 ^ 2 ^ n := by
    classical
    exact Nat.findGreatest_spec (P := fun s => thrCount n s < 2 ^ 2 ^ n) hb hn
  obtain ⟨k, w, t, a, t0, hk, hdec⟩ := hp n
  have hspec := Classical.choose_spec (exists_thrHard n (thrBestSize n) hS)
  have h2 : thrHard n = Classical.choose (exists_thrHard n (thrBestSize n) hS) := by
    simp [thrHard, hS]
  apply hspec
  rw [← h2]
  refine mem_circSet (le_trans hk hle) w t a t0 _ fun x => ?_
  rw [← mem_thrHardLang]
  exact hdec x

theorem exists_not_thrthr :
    ∃ L : Language Bool, ∀ p : Polynomial ℕ, L ∉ THRTHR (fun n => p.eval n) :=
  ⟨thrHardLang, thrHardLang_not_thrthr⟩

end PEqualNP.CircuitLowerBounds.Helpers
