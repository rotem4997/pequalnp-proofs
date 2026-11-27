import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.WeightBound

/-!
Helper for L-clb-030: the symmetric difference of two languages with depth-two threshold
circuits has depth-two threshold circuits with polynomially many bottom gates.

The route (Hansen and Podolskii, exact threshold circuits; Chen and Williams):

* a threshold gate on `n` inputs is, after its weights are made small (`WeightBound`), a sum
  of at most `1 + ((n + 2) ^ 2 + 1) * (n * n)` exact threshold gates `[linear form = value]`
  with pairwise disjoint supports (`gate_esum`). With `D i` the form whose weights and
  threshold are the originals divided by `2 ^ i` and rounded down, `D i - 2 * D (i + 1)` lies
  in `[-1, n]`, so once `D i ≥ 1` it stays so for smaller `i`, and `D 0 ≥ 1` holds exactly
  when `D m = 1` at the top or the pair `(D (i + 1), D i)` takes one of the `n * n` values
  with `-n < D (i + 1) ≤ 0` and `1 ≤ D i ≤ n` for exactly one `i`;
* the product of two exact gates is one exact gate (`ESum.mul`);
* an exact gate is a difference of two threshold gates (`ESum.toTSum`);
* with `P = 2 * S1 + 1 - 2 * t01` and `Q = 2 * S2 + 1 - 2 * t02` the symmetric difference is
  `P * Q < 0`, and `P * Q` is a combination of `S1 * S2`, `S1`, `S2` and a constant.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

/-- The value of an integer linear form on a Boolean input. -/
def lin {n : ℕ} (w : Fin n → ℤ) (x : Fin n → Bool) : ℤ :=
  ∑ i : Fin n, w i * (if x i = true then 1 else 0)

/-- `F` is an integer combination of at most `N` exact threshold gates. -/
def ESum (n N : ℕ) (F : (Fin n → Bool) → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → Fin n → ℤ) (v a : ι → ℤ), Fintype.card ι ≤ N ∧
    ∀ x, F x = ∑ j : ι, a j * (if lin (w j) x = v j then 1 else 0)

/-- `F` is an integer combination of at most `N` threshold gates. -/
def TSum (n N : ℕ) (F : (Fin n → Bool) → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → Fin n → ℤ) (v a : ι → ℤ), Fintype.card ι ≤ N ∧
    ∀ x, F x = ∑ j : ι, a j * (if v j ≤ lin (w j) x then 1 else 0)

theorem lin_abs_le {n : ℕ} (w : Fin n → ℤ) (x : Fin n → Bool) :
    |lin w x| ≤ ∑ i : Fin n, |w i| := by
  unfold lin
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  split_ifs <;> simp

theorem lin_add_mul {n : ℕ} (w w' : Fin n → ℤ) (M : ℤ) (x : Fin n → Bool) :
    lin (fun i => w i + M * w' i) x = lin w x + M * lin w' x := by
  unfold lin
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ESum.mono {n N N' : ℕ} {F : (Fin n → Bool) → ℤ} (h : ESum n N F) (hN : N ≤ N') :
    ESum n N' F := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := h
  exact ⟨ι, i, w, v, a, hc.trans hN, hF⟩

theorem ESum.zero (n : ℕ) : ESum n 0 (fun _ => 0) :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, by simp, by simp⟩

theorem ESum.single {n : ℕ} (w : Fin n → ℤ) (v : ℤ) :
    ESum n 1 (fun x => if lin w x = v then 1 else 0) :=
  ⟨Unit, inferInstance, fun _ => w, fun _ => v, fun _ => 1, by simp, by simp⟩

theorem ESum.add {n N N' : ℕ} {F G : (Fin n → Bool) → ℤ} (hF : ESum n N F) (hG : ESum n N' G) :
    ESum n (N + N') (fun x => F x + G x) := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := hF
  obtain ⟨κ, i', w', v', a', hc', hG⟩ := hG
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim w w', Sum.elim v v', Sum.elim a a', ?_, fun x => ?_⟩
  · rw [Fintype.card_sum]; omega
  · simp only [Fintype.sum_sum_type, hF x, hG x, Sum.elim_inl, Sum.elim_inr]
    rfl

theorem ESum.smul {n N : ℕ} {F : (Fin n → Bool) → ℤ} (c : ℤ) (hF : ESum n N F) :
    ESum n N (fun x => c * F x) := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := hF
  refine ⟨ι, i, w, v, fun j => c * a j, hc, fun x => ?_⟩
  simp only [hF x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The conjunction of two exact gates is one exact gate. -/
theorem exact_and {n : ℕ} (w w' : Fin n → ℤ) (v v' : ℤ) (x : Fin n → Bool) :
    (lin (fun i => w i + (1 + ∑ i : Fin n, |w i| + |v|) * w' i) x =
        v + (1 + ∑ i : Fin n, |w i| + |v|) * v') ↔ (lin w x = v ∧ lin w' x = v') := by
  rw [lin_add_mul]
  have hb := lin_abs_le w x
  set M : ℤ := 1 + ∑ i : Fin n, |w i| + |v| with hM
  constructor
  · intro h
    have h1 : lin w x - v = M * (v' - lin w' x) := by linarith
    have h2 : |lin w x - v| < M := by
      have := abs_sub (lin w x) v
      omega
    have h3 : v' - lin w' x = 0 := by
      by_contra hne
      have h4 : (1 : ℤ) ≤ |v' - lin w' x| := Int.one_le_abs hne
      have h5 : |lin w x - v| = |M| * |v' - lin w' x| := by rw [h1, abs_mul]
      have h6 : (0 : ℤ) ≤ M := by have := abs_nonneg (lin w x - v); omega
      rw [abs_of_nonneg h6] at h5
      nlinarith
    rw [h3] at h1
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem ESum.mul {n N N' : ℕ} {F G : (Fin n → Bool) → ℤ} (hF : ESum n N F) (hG : ESum n N' G) :
    ESum n (N * N') (fun x => F x * G x) := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := hF
  obtain ⟨κ, i', w', v', a', hc', hG⟩ := hG
  refine ⟨ι × κ, inferInstance,
    fun p => fun i => w p.1 i + (1 + ∑ i : Fin n, |w p.1 i| + |v p.1|) * w' p.2 i,
    fun p => v p.1 + (1 + ∑ i : Fin n, |w p.1 i| + |v p.1|) * v' p.2,
    fun p => a p.1 * a' p.2, ?_, fun x => ?_⟩
  · rw [Fintype.card_prod]; exact Nat.mul_le_mul hc hc'
  · simp only [hF x, hG x, Fintype.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have h := exact_and (w j) (w' k) (v j) (v' k) x
    by_cases h1 : lin (w j) x = v j <;> by_cases h2 : lin (w' k) x = v' k <;>
      simp [h, h1, h2]

theorem ESum.sum {n N : ℕ} {α : Type*} (S : Finset α) (F : α → (Fin n → Bool) → ℤ)
    (h : ∀ s ∈ S, ESum n N (F s)) : ESum n (S.card * N) (fun x => ∑ s ∈ S, F s x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ESum.zero n
  | insert s S hs ih =>
    have h1 := (h s (Finset.mem_insert_self s S)).add
      (ih fun s' hs' => h s' (Finset.mem_insert_of_mem hs'))
    have h2 : (fun x => ∑ s' ∈ insert s S, F s' x) = fun x => F s x + ∑ s' ∈ S, F s' x := by
      funext x; rw [Finset.sum_insert hs]
    rw [h2, Finset.card_insert_of_notMem hs]
    exact h1.mono (by ring_nf; omega)

theorem TSum.add {n N N' : ℕ} {F G : (Fin n → Bool) → ℤ} (hF : TSum n N F) (hG : TSum n N' G) :
    TSum n (N + N') (fun x => F x + G x) := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := hF
  obtain ⟨κ, i', w', v', a', hc', hG⟩ := hG
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim w w', Sum.elim v v', Sum.elim a a', ?_, fun x => ?_⟩
  · rw [Fintype.card_sum]; omega
  · simp only [Fintype.sum_sum_type, hF x, hG x, Sum.elim_inl, Sum.elim_inr]
    rfl

theorem TSum.smul {n N : ℕ} {F : (Fin n → Bool) → ℤ} (c : ℤ) (hF : TSum n N F) :
    TSum n N (fun x => c * F x) := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := hF
  refine ⟨ι, i, w, v, fun j => c * a j, hc, fun x => ?_⟩
  simp only [hF x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- An exact gate is a difference of two threshold gates. -/
theorem ESum.toTSum {n N : ℕ} {F : (Fin n → Bool) → ℤ} (hF : ESum n N F) : TSum n (2 * N) F := by
  obtain ⟨ι, i, w, v, a, hc, hF⟩ := hF
  refine ⟨ι ⊕ ι, inferInstance, Sum.elim w w, Sum.elim v (fun j => v j + 1),
    Sum.elim a (fun j => -a j), ?_, fun x => ?_⟩
  · rw [Fintype.card_sum]; omega
  · rw [Fintype.sum_sum_type, hF x, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    by_cases h1 : lin (w j) x = v j
    · simp [h1]
    · by_cases h2 : v j ≤ lin (w j) x
      · have h3 : v j + 1 ≤ lin (w j) x := by omega
        simp only [h1, h2, h3, ↓reduceIte]; ring
      · have h3 : ¬ v j + 1 ≤ lin (w j) x := by omega
        simp only [h1, h2, h3, ↓reduceIte]; ring

/-- If the weights `u` and `2 * u'` differ by `0` or `1` in each place, the forms differ by
between `0` and `n`. -/
theorem lin_halve {n : ℕ} (u u' : Fin n → ℤ) (h : ∀ j, 0 ≤ u j - 2 * u' j ∧ u j - 2 * u' j ≤ 1)
    (x : Fin n → Bool) : 0 ≤ lin u x - 2 * lin u' x ∧ lin u x - 2 * lin u' x ≤ n := by
  have e : lin u x - 2 * lin u' x =
      ∑ i : Fin n, (u i - 2 * u' i) * (if x i = true then 1 else 0) := by
    unfold lin
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  constructor
  · refine Finset.sum_nonneg fun i _ => ?_
    have := (h i).1
    split_ifs
    · rw [mul_one]; exact this
    · simp
  · have h1 : ∑ i : Fin n, (u i - 2 * u' i) * (if x i = true then (1 : ℤ) else 0) ≤
        ∑ _i : Fin n, (1 : ℤ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := (h i).2
      split_ifs
      · rw [mul_one]; exact this
      · simp
    simpa using h1

theorem ediv_halve (a : ℤ) (i : ℕ) :
    0 ≤ a / 2 ^ i - 2 * (a / 2 ^ (i + 1)) ∧ a / 2 ^ i - 2 * (a / 2 ^ (i + 1)) ≤ 1 := by
  have h : a / 2 ^ (i + 1) = a / 2 ^ i / 2 := by
    rw [pow_succ, Int.ediv_ediv_of_nonneg (by positivity)]
  rw [h]
  omega

/-- A threshold gate whose weights are below `2 ^ m` and whose threshold is at least
`-2 ^ m` is a sum of at most `1 + m * (n * n)` exact gates. -/
theorem gate_esum_bdd (n m : ℕ) (w : Fin n → ℤ) (T : ℤ) (hw : ∀ j, w j < 2 ^ m)
    (hT : -2 ^ m ≤ T) :
    ESum n (1 + m * (n * n)) (fun x => if 1 ≤ lin w x - T then 1 else 0) := by
  classical
  set D : ℕ → (Fin n → Bool) → ℤ := fun i x => lin (fun j => w j / 2 ^ i) x - T / 2 ^ i with hD
  have hstep : ∀ i x, 2 * D (i + 1) x - 1 ≤ D i x ∧ D i x ≤ 2 * D (i + 1) x + n := by
    intro i x
    have h1 := lin_halve (fun j => w j / 2 ^ i) (fun j => w j / 2 ^ (i + 1))
      (fun j => ediv_halve (w j) i) x
    have h2 := ediv_halve T i
    simp only [hD]
    omega
  have hD0 : ∀ x, D 0 x = lin w x - T := by
    intro x; simp [hD]
  have key : ∀ k : ℕ, ∃ R : (Fin n → Bool) → ℤ, ESum n (k * (n * n)) R ∧
      ∀ x, (if 1 ≤ D 0 x then (1 : ℤ) else 0) = (if 1 ≤ D k x then 1 else 0) + R x := by
    intro k
    induction k with
    | zero => exact ⟨fun _ => 0, by simpa using ESum.zero n, by simp⟩
    | succ k ih =>
      obtain ⟨R, hR, hRx⟩ := ih
      set S : Finset (ℤ × ℤ) := Finset.Ioc (-(n : ℤ)) 0 ×ˢ Finset.Icc 1 (n : ℤ) with hS
      have hcard : S.card = n * n := by
        simp [hS]
      have hE : ESum n (S.card * 1) (fun x => ∑ p ∈ S,
          (if lin (fun j => w j / 2 ^ (k + 1)) x = p.1 + T / 2 ^ (k + 1) then (1 : ℤ) else 0) *
          (if lin (fun j => w j / 2 ^ k) x = p.2 + T / 2 ^ k then 1 else 0)) := by
        refine ESum.sum S _ fun p _ => ?_
        simpa using (ESum.single (fun j => w j / 2 ^ (k + 1)) (p.1 + T / 2 ^ (k + 1))).mul
          (ESum.single (fun j => w j / 2 ^ k) (p.2 + T / 2 ^ k))
      refine ⟨_, (hR.add hE).mono (by rw [hcard]; ring_nf; omega), fun x => ?_⟩
      rw [hRx x]
      have hsum : (∑ p ∈ S,
          (if lin (fun j => w j / 2 ^ (k + 1)) x = p.1 + T / 2 ^ (k + 1) then (1 : ℤ) else 0) *
          (if lin (fun j => w j / 2 ^ k) x = p.2 + T / 2 ^ k then 1 else 0)) =
          if (D (k + 1) x, D k x) ∈ S then 1 else 0 := by
        rw [← Finset.sum_ite_eq' S (D (k + 1) x, D k x) (fun _ => (1 : ℤ))]
        refine Finset.sum_congr rfl fun p _ => ?_
        obtain ⟨p1, p2⟩ := p
        simp only [hD, Prod.mk.injEq]
        have h3 : (p1 = lin (fun j => w j / 2 ^ (k + 1)) x - T / 2 ^ (k + 1) ∧
            p2 = lin (fun j => w j / 2 ^ k) x - T / 2 ^ k) ↔
            (lin (fun j => w j / 2 ^ (k + 1)) x = p1 + T / 2 ^ (k + 1) ∧
              lin (fun j => w j / 2 ^ k) x = p2 + T / 2 ^ k) := by
          constructor <;> rintro ⟨_, _⟩ <;> constructor <;> omega
        simp only [h3]
        by_cases h1 : lin (fun j => w j / 2 ^ (k + 1)) x = p1 + T / 2 ^ (k + 1) <;>
          by_cases h2 : lin (fun j => w j / 2 ^ k) x = p2 + T / 2 ^ k <;> simp [h1, h2]
      rw [hsum]
      have hmem : (D (k + 1) x, D k x) ∈ S ↔
          (-(n : ℤ) < D (k + 1) x ∧ D (k + 1) x ≤ 0) ∧ 1 ≤ D k x ∧ D k x ≤ n := by
        simp [hS]
      have hs := hstep k x
      by_cases h1 : 1 ≤ D (k + 1) x
      · have h2 : 1 ≤ D k x := by omega
        have h3 : ¬ (D (k + 1) x, D k x) ∈ S := by rw [hmem]; omega
        simp only [h1, h2, h3, ↓reduceIte]; ring
      · by_cases h2 : 1 ≤ D k x
        · have h3 : (D (k + 1) x, D k x) ∈ S := by rw [hmem]; omega
          simp only [h1, h2, h3, ↓reduceIte]; ring
        · have h3 : ¬ (D (k + 1) x, D k x) ∈ S := by rw [hmem]; omega
          simp only [h1, h2, h3, ↓reduceIte]; ring
  obtain ⟨R, hR, hRx⟩ := key m
  have htop : ∀ x, D m x ≤ 1 := by
    intro x
    have h1 : lin (fun j => w j / 2 ^ m) x ≤ 0 := by
      unfold lin
      refine Finset.sum_nonpos fun i _ => ?_
      have h2 : w i / 2 ^ m ≤ 0 := by
        have : w i / 2 ^ m < 1 := Int.ediv_lt_of_lt_mul (by positivity) (by simpa using hw i)
        omega
      split_ifs <;> simp [h2]
    have h2 : -1 ≤ T / 2 ^ m := by
      rw [Int.le_ediv_iff_mul_le (by positivity)]
      linarith
    simp only [hD]
    omega
  have hfin := (ESum.single (fun j => w j / 2 ^ m) (1 + T / 2 ^ m)).add hR
  have heq : (fun x => if 1 ≤ lin w x - T then (1 : ℤ) else 0) =
      fun x => (if lin (fun j => w j / 2 ^ m) x = 1 + T / 2 ^ m then 1 else 0) + R x := by
    funext x
    rw [← hD0 x, hRx x]
    have h1 := htop x
    have h2 : (1 ≤ D m x) ↔ lin (fun j => w j / 2 ^ m) x = 1 + T / 2 ^ m := by
      simp only [hD] at h1 ⊢
      omega
    simp only [h2]
  rw [heq]
  exact hfin

/-- Every threshold gate on `n` inputs, whatever its weights, is a sum of at most
`1 + ((n + 2) ^ 2 + 1) * (n * n)` exact gates. -/
theorem gate_esum (n : ℕ) (w : Fin n → ℤ) (t : ℤ) :
    ESum n (1 + ((n + 2) ^ 2 + 1) * (n * n)) (fun x => if t ≤ lin w x then 1 else 0) := by
  obtain ⟨w', t', hb, hiff⟩ := threshold_small_weights n w t
  set B : ℤ := ((n : ℤ) + 2) ^ (n + 2) with hB
  have hBpos : 0 ≤ B := by positivity
  have hB2 : B + 1 ≤ 2 ^ ((n + 2) ^ 2 + 1) := by
    have h1 : ((n : ℤ) + 2) ≤ 2 ^ (n + 2) := by
      have : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have h2 : B ≤ (2 ^ (n + 2)) ^ (n + 2) := pow_le_pow_left₀ (by positivity) h1 _
    have h3 : ((2 : ℤ) ^ (n + 2)) ^ (n + 2) = 2 ^ ((n + 2) ^ 2) := by
      rw [← pow_mul, sq]
    have h4 : (1 : ℤ) ≤ 2 ^ ((n + 2) ^ 2) := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  set T : ℤ := max (-B) (min t' (B + 1)) - 1 with hT
  have hwj : ∀ j, w' j < 2 ^ ((n + 2) ^ 2 + 1) := by
    intro j
    have h1 : |w' j| ≤ ∑ i : Fin n, |w' i| :=
      Finset.single_le_sum (f := fun i => |w' i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := le_abs_self (w' j)
    linarith
  have hTl : -2 ^ ((n + 2) ^ 2 + 1) ≤ T := by
    have : -B ≤ max (-B) (min t' (B + 1)) := le_max_left _ _
    linarith
  have h := gate_esum_bdd n ((n + 2) ^ 2 + 1) w' T hwj hTl
  have heq : (fun x => if t ≤ lin w x then (1 : ℤ) else 0) =
      fun x => if 1 ≤ lin w' x - T then 1 else 0 := by
    funext x
    have h1 : (t ≤ lin w x) ↔ (t' ≤ lin w' x) := hiff x
    have h2 := lin_abs_le w' x
    have h3 : |lin w' x| ≤ B := h2.trans hb
    have h4 := abs_le.mp h3
    have h5 : (t' ≤ lin w' x) ↔ (1 ≤ lin w' x - T) := by
      simp only [hT]
      omega
    simp only [h1, h5]
  rw [heq]
  exact h

/-- The count: `2 * (k1 * N * (k2 * N)) + (k1 + k2)` bottom gates fit under
`73 * (s1 + s2 + n + 1) ^ 73`. -/
theorem xor_count (n k1 k2 s1 s2 : ℕ) (h1 : k1 ≤ s1) (h2 : k2 ≤ s2) :
    2 * (k1 * (1 + ((n + 2) ^ 2 + 1) * (n * n)) * (k2 * (1 + ((n + 2) ^ 2 + 1) * (n * n)))) +
      (k1 + k2) ≤ 73 * (s1 + s2 + n + 1) ^ 73 := by
  set u := s1 + s2 + n + 1 with hu
  have hu1 : 1 ≤ u := by omega
  have hk1 : k1 ≤ u := by omega
  have hk2 : k2 ≤ u := by omega
  have hn : n ≤ u := by omega
  have hN : 1 + ((n + 2) ^ 2 + 1) * (n * n) ≤ 6 * u ^ 4 := by
    have h3 : n + 2 ≤ 2 * u := by omega
    have h4 : (n + 2) ^ 2 + 1 ≤ 5 * u ^ 2 := by nlinarith
    have h5 : n * n ≤ u ^ 2 := by nlinarith
    have h6 : 1 ≤ u ^ 4 := Nat.one_le_pow _ _ hu1
    calc 1 + ((n + 2) ^ 2 + 1) * (n * n) ≤ u ^ 4 + 5 * u ^ 2 * u ^ 2 := by gcongr
      _ = 6 * u ^ 4 := by ring
  have h7 : u ≤ u ^ 10 := Nat.le_self_pow (by norm_num) u
  have h8 : u ^ 10 ≤ u ^ 73 := Nat.pow_le_pow_right hu1 (by norm_num)
  calc 2 * (k1 * (1 + ((n + 2) ^ 2 + 1) * (n * n)) * (k2 * (1 + ((n + 2) ^ 2 + 1) * (n * n)))) +
        (k1 + k2)
      ≤ 2 * (u * (6 * u ^ 4) * (u * (6 * u ^ 4))) + u := by gcongr; omega
    _ = 72 * u ^ 10 + u := by ring
    _ ≤ 72 * u ^ 10 + u ^ 10 := by gcongr
    _ = 73 * u ^ 10 := by ring
    _ ≤ 73 * u ^ 73 := by gcongr

/-- The sign of a product of two odd quantities. -/
theorem xor_sign (S1 S2 t1 t2 : ℤ) :
    ((t1 ≤ S1 ∧ ¬ t2 ≤ S2) ∨ (¬ t1 ≤ S1 ∧ t2 ≤ S2)) ↔
      1 + (1 - 2 * t1) * (1 - 2 * t2) ≤
        -4 * (S1 * S2) + (-2 * (1 - 2 * t2)) * S1 + (-2 * (1 - 2 * t1)) * S2 := by
  have e : -4 * (S1 * S2) + (-2 * (1 - 2 * t2)) * S1 + (-2 * (1 - 2 * t1)) * S2 -
      (1 - 2 * t1) * (1 - 2 * t2) = -((2 * S1 + 1 - 2 * t1) * (2 * S2 + 1 - 2 * t2)) := by ring
  by_cases h1 : t1 ≤ S1 <;> by_cases h2 : t2 ≤ S2
  · have : 0 < (2 * S1 + 1 - 2 * t1) * (2 * S2 + 1 - 2 * t2) :=
      mul_pos (by omega) (by omega)
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact absurd ‹_› h
    · intro h; exfalso; linarith
  · have : (2 * S1 + 1 - 2 * t1) * (2 * S2 + 1 - 2 * t2) ≤ -1 := by nlinarith
    constructor
    · intro _; linarith
    · intro _; exact Or.inl ⟨h1, h2⟩
  · have : (2 * S1 + 1 - 2 * t1) * (2 * S2 + 1 - 2 * t2) ≤ -1 := by nlinarith
    constructor
    · intro _; linarith
    · intro _; exact Or.inr ⟨h1, h2⟩
  · have : 0 < (2 * S1 + 1 - 2 * t1) * (2 * S2 + 1 - 2 * t2) :=
      mul_pos_of_neg_of_neg (by omega) (by omega)
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact absurd h ‹_›
    · intro h; exfalso; linarith

theorem thrthr_xor :
    ∃ c : ℕ, ∀ (s1 s2 : ℕ → ℕ) (L1 L2 : Language Bool),
      L1 ∈ PEqualNP.CircuitLowerBounds.THRTHR s1 →
      L2 ∈ PEqualNP.CircuitLowerBounds.THRTHR s2 →
      ({x : List Bool | (x ∈ L1 ∧ x ∉ L2) ∨ (x ∉ L1 ∧ x ∈ L2)} : Language Bool) ∈
        PEqualNP.CircuitLowerBounds.THRTHR (fun n : ℕ => c * (s1 n + s2 n + n + 1) ^ c) := by
  refine ⟨73, fun s1 s2 L1 L2 h1 h2 n => ?_⟩
  obtain ⟨k1, w1, t1, a1, t01, hk1, hx1⟩ := h1 n
  obtain ⟨k2, w2, t2, a2, t02, hk2, hx2⟩ := h2 n
  set S1 : (Fin n → Bool) → ℤ := fun x =>
    ∑ j : Fin k1, a1 j * (if t1 j ≤ lin (w1 j) x then 1 else 0) with hS1
  set S2 : (Fin n → Bool) → ℤ := fun x =>
    ∑ j : Fin k2, a2 j * (if t2 j ≤ lin (w2 j) x then 1 else 0) with hS2
  have e1 : ESum n (k1 * (1 + ((n + 2) ^ 2 + 1) * (n * n))) S1 := by
    have := ESum.sum (Finset.univ : Finset (Fin k1))
      (fun j x => a1 j * (if t1 j ≤ lin (w1 j) x then 1 else 0))
      (fun j _ => (gate_esum n (w1 j) (t1 j)).smul (a1 j))
    simpa only [Finset.card_univ, Fintype.card_fin] using this
  have e2 : ESum n (k2 * (1 + ((n + 2) ^ 2 + 1) * (n * n))) S2 := by
    have := ESum.sum (Finset.univ : Finset (Fin k2))
      (fun j x => a2 j * (if t2 j ≤ lin (w2 j) x then 1 else 0))
      (fun j _ => (gate_esum n (w2 j) (t2 j)).smul (a2 j))
    simpa only [Finset.card_univ, Fintype.card_fin] using this
  have g1 : TSum n k1 S1 := ⟨Fin k1, inferInstance, w1, t1, a1, by simp, fun x => rfl⟩
  have g2 : TSum n k2 S2 := ⟨Fin k2, inferInstance, w2, t2, a2, by simp, fun x => rfl⟩
  have hG := ((((e1.mul e2).toTSum.smul (-4)).add (g1.smul (-2 * (1 - 2 * t02)))).add
    (g2.smul (-2 * (1 - 2 * t01))))
  obtain ⟨ι, inst, w, v, a, hc, hGx⟩ := hG
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => w (e.symm j), fun j => v (e.symm j), fun j => a (e.symm j),
    1 + (1 - 2 * t01) * (1 - 2 * t02), ?_, fun x => ?_⟩
  · show Fintype.card ι ≤ 73 * (s1 n + s2 n + n + 1) ^ 73
    refine le_trans hc ?_
    have := xor_count n k1 k2 (s1 n) (s2 n) hk1 hk2
    omega
  · have hsum : (∑ j : Fin (Fintype.card ι), a (e.symm j) *
        (if v (e.symm j) ≤ ∑ i : Fin n, w (e.symm j) i * (if x i = true then 1 else 0)
          then 1 else 0)) =
        ∑ j : ι, a j * (if v j ≤ lin (w j) x then 1 else 0) :=
      Equiv.sum_comp e.symm (fun j => a j * (if v j ≤ lin (w j) x then 1 else 0))
    rw [hsum, ← hGx x]
    have m1 : List.ofFn x ∈ L1 ↔ t01 ≤ S1 x := hx1 x
    have m2 : List.ofFn x ∈ L2 ↔ t02 ≤ S2 x := hx2 x
    have := xor_sign (S1 x) (S2 x) t01 t02
    rw [← m1, ← m2] at this
    exact this

end PEqualNP.CircuitLowerBounds.Helpers
