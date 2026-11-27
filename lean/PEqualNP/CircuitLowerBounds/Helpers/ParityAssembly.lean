import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.Approx
import PEqualNP.CircuitLowerBounds.Helpers.ParitySmol

/-!
Helper module, proofs only: the assembly of L-clb-007 (parity is not in AC0) from the
approximation of circuits by polynomials over `ZMod 3` (`Helpers.approx`), the degree bound
for parity and the binomial tail (`ParitySmol.smolensky`, `ParitySmol.tailUsable`).

For a size polynomial `q` and a depth `d`, take `l` with `4 * q(n) < 2 ^ l` at the length
`n = 16 * ((2 * l) ^ d + 1) ^ 2`. A circuit of size `q(n)` and depth `d` for parity on `n`
inputs agrees with a polynomial of degree `(2 * l) ^ d` outside fewer than a quarter of the
points, while such a polynomial agrees with parity on at most three quarters of them.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.ParityAC0

open PEqualNP.CircuitLowerBounds

/-- An exponential beats a linear function. -/
theorem pow_beats (a K : ℕ) : ∃ m, a + m * K < 2 ^ m := by
  obtain ⟨j, hjdef⟩ : ∃ j, j = a + 2 * K + 1 := ⟨_, rfl⟩
  refine ⟨2 * j, ?_⟩
  have hj := Nat.lt_two_pow_self (n := j)
  have e : 2 ^ (2 * j) = 2 ^ j * 2 ^ j := by rw [two_mul, pow_add]
  rw [e]
  have h1 : j * j < 2 ^ j * 2 ^ j := Nat.mul_lt_mul'' hj hj
  have h2 : j * j = j * a + 2 * j * K + j := by rw [hjdef]; ring
  have h3 : a ≤ j * a := Nat.le_mul_of_pos_left a (by omega)
  linarith

/-- A polynomial with natural coefficients is at most its value at `1` times a power. -/
theorem eval_le (q : Polynomial ℕ) (n M : ℕ) (hn : n ≤ M) (hM : 1 ≤ M) :
    q.eval n ≤ q.eval 1 * M ^ q.natDegree := by
  have h1 : q.eval 1 = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i := by
    rw [Polynomial.eval_eq_sum_range]; simp
  rw [h1, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ q.natDegree := by
    have := Finset.mem_range.1 hi
    omega
  exact Nat.mul_le_mul_left _
    (le_trans (Nat.pow_le_pow_left hn i) (Nat.pow_le_pow_right hM hi'))

/-- The choice of the parameter `l` for a size polynomial `q` and a depth `d`. -/
theorem exists_large (q : Polynomial ℕ) (d : ℕ) :
    ∃ l, 1 ≤ l ∧ 4 * q.eval (16 * ((2 * l) ^ d + 1) ^ 2) < 2 ^ l := by
  obtain ⟨k, hk⟩ : ∃ k, k = q.natDegree := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = q.eval 1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := pow_beats (2 + c + 6 * k + 2 * d * k) (2 * d * k)
  refine ⟨2 ^ m, Nat.one_le_two_pow, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T, T = 2 ^ ((m + 1) * d) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hT]; exact Nat.one_le_two_pow
  have hTe : (2 * 2 ^ m) ^ d = T := by rw [hT, ← pow_succ', ← pow_mul]
  have hM : 2 ^ (6 + 2 * d * (m + 1)) = 64 * T ^ 2 := by
    rw [hT, ← pow_mul, pow_add]
    congr 2
    ring
  have hn : 16 * ((2 * 2 ^ m) ^ d + 1) ^ 2 ≤ 2 ^ (6 + 2 * d * (m + 1)) := by
    rw [hM, hTe]
    nlinarith [Nat.mul_le_mul hT1 hT1, Nat.mul_le_mul_right T hT1]
  have hev := eval_le q _ _ hn Nat.one_le_two_pow
  rw [← hk, ← hc, ← pow_mul] at hev
  have hclt := Nat.lt_two_pow_self (n := c)
  have hX : 0 < 2 ^ ((6 + 2 * d * (m + 1)) * k) := by positivity
  calc 4 * q.eval (16 * ((2 * 2 ^ m) ^ d + 1) ^ 2)
      ≤ 4 * (c * 2 ^ ((6 + 2 * d * (m + 1)) * k)) := Nat.mul_le_mul_left _ hev
    _ < 2 ^ 2 * (2 ^ c * 2 ^ ((6 + 2 * d * (m + 1)) * k)) := by
        have := Nat.mul_lt_mul_of_pos_right hclt hX
        omega
    _ = 2 ^ (2 + c + (6 + 2 * d * (m + 1)) * k) := by rw [← pow_add, ← pow_add, Nat.add_assoc]
    _ ≤ 2 ^ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by
        have : (6 + 2 * d * (m + 1)) * k = 6 * k + 2 * d * k + m * (2 * d * k) := by ring
        omega)

/-- Parity is not in AC0 (Razborov 1987, Smolensky 1987). -/
theorem parity_not_AC0 :
    ({x : List Bool | x.count true % 2 = 1} : Language Bool) ∉ AC0 := by
  classical
  rintro ⟨q, d, h⟩
  obtain ⟨l, hl, hbig⟩ := exists_large q d
  obtain ⟨D, hD⟩ : ∃ D, D = (2 * l) ^ d := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = 16 * (D + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hD, ← hn] at hbig
  obtain ⟨C, hg, hs, hd, hdec⟩ := h n
  obtain ⟨P, hP, hbad⟩ := Helpers.approx 3 Nat.prime_three n (q.eval n) d l C
    (fun g hg' => by
      have := (hg g hg').1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
      tauto) hs hd hl
  have hP' : P.totalDegree ≤ D := by rw [hD]; simpa using hP
  obtain ⟨E, hE⟩ : ∃ E : Finset (Fin n → Bool), E = Finset.univ.filter fun x : Fin n → Bool =>
      MvPolynomial.eval (fun i => if x i = true then (1 : ZMod 3) else 0) P ≠
        (if C.eval (List.ofFn x) = true then (1 : ZMod 3) else 0) := ⟨_, rfl⟩
  rw [← hE] at hbad
  have hA := ParitySmol.smolensky n D P Eᶜ hP' (fun x hx => by
    have hx' : MvPolynomial.eval (fun i => if x i = true then (1 : ZMod 3) else 0) P =
        (if C.eval (List.ofFn x) = true then (1 : ZMod 3) else 0) := by
      by_contra hne
      exact (Finset.mem_compl.1 hx) (by rw [hE]; simp [hne])
    have hiff : C.eval (List.ofFn x) = true ↔ ParitySmol.OddWeight x := by
      refine (hdec (List.ofFn x) (List.length_ofFn)).trans ?_
      show (List.ofFn x).count true % 2 = 1 ↔ _
      rw [List.count_ofFn]
      rfl
    show MvPolynomial.eval (fun i => if x i = true then (1 : ZMod 3) else 0) P = _
    by_cases ho : ParitySmol.OddWeight x
    · rw [if_pos ho]; rw [if_pos (hiff.2 ho)] at hx'; exact hx'
    · rw [if_neg ho]; rw [if_neg (mt hiff.1 ho)] at hx'; exact hx')
  have hT := ParitySmol.tailUsable n D (le_of_eq hn.symm)
  have hcard : E.card + Eᶜ.card = 2 ^ n := by
    rw [Finset.card_add_card_compl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h4 : 2 ^ n ≤ 4 * E.card := by omega
  have h1 : 2 ^ n * 2 ^ l ≤ 4 * E.card * 2 ^ l := Nat.mul_le_mul_right _ h4
  have h2 : 4 * q.eval n * 2 ^ n < 2 ^ l * 2 ^ n :=
    Nat.mul_lt_mul_of_pos_right hbig (by positivity)
  nlinarith

end PEqualNP.CircuitLowerBounds.Helpers.ParityAC0
