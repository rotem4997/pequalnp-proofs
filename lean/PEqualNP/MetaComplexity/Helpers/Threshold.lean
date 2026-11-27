import PEqualNP.Defs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The representing threshold, rebuilt: a family above (4 + 1/d) 2^k with an NP edge language
puts NP outside P/poly, given the sharp conversion (as a hypothesis, the statement of a checked row).
-/

namespace PEqualNP.MetaComplexity.Threshold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Filter Topology

/-- A polynomial over ℕ is at most its value at 1 times `(n + 1) ^ natDegree`. -/
theorem poly_le (p : Polynomial ℕ) (n : ℕ) : p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := by simpa [Nat.lt_succ_iff] using hi
  simp only [one_pow, mul_one]
  apply Nat.mul_le_mul_left
  calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
    _ ≤ (n + 1) ^ p.natDegree := Nat.pow_le_pow_right (Nat.succ_pos n) hi'

/-- Eventually `C (k + 1) ^ D 2 ^ ((k + 1) / 2) ≤ 2 ^ k`. -/
theorem eventually_small (C D : ℕ) :
    ∃ k0, ∀ k, k0 ≤ k → C * (k + 1) ^ D * 2 ^ ((k + 1) / 2) ≤ 2 ^ k := by
  have hr : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ht := tendsto_pow_const_div_const_pow_of_one_lt D hr
  have hpos : (0 : ℝ) < (C : ℝ) * 2 ^ D * 2 + 1 := by positivity
  have hev := (ht.eventually (gt_mem_nhds (inv_pos.2 hpos)))
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 hev
  refine ⟨max k1 1, fun k hk => ?_⟩
  have hk1' := hk1 k (le_of_max_le_left hk)
  have hk0 : 1 ≤ k := le_of_max_le_right hk
  have hs : (0 : ℝ) < Real.sqrt 2 ^ k := by positivity
  have hsq : Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = (2 : ℝ) ^ k := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
  -- from the limit: k ^ D < sqrt 2 ^ k / (C 2^D 2 + 1)
  have h1 : (k : ℝ) ^ D * ((C : ℝ) * 2 ^ D * 2 + 1) < Real.sqrt 2 ^ k := by
    have := (div_lt_iff₀ hs).1 hk1'
    rw [lt_inv_mul_iff₀ hpos] at *
    · nlinarith [this, hpos]
    all_goals positivity
  -- (k + 1) ^ D ≤ 2 ^ D k ^ D
  have h2 : ((k : ℝ) + 1) ^ D ≤ 2 ^ D * (k : ℝ) ^ D := by
    rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    linarith
  -- 2 ^ ((k + 1) / 2) ≤ 2 sqrt 2 ^ k
  have h3 : (2 : ℝ) ^ ((k + 1) / 2) ≤ 2 * Real.sqrt 2 ^ k := by
    have e : (2 : ℝ) ^ ((k + 1) / 2) = Real.sqrt 2 ^ (2 * ((k + 1) / 2)) := by
      rw [pow_mul, Real.sq_sqrt (by norm_num)]
    rw [e]
    calc Real.sqrt 2 ^ (2 * ((k + 1) / 2)) ≤ Real.sqrt 2 ^ (k + 1) :=
          pow_le_pow_right₀ hr.le (by omega)
      _ = Real.sqrt 2 * Real.sqrt 2 ^ k := by ring
      _ ≤ 2 * Real.sqrt 2 ^ k := by
          apply mul_le_mul_of_nonneg_right _ hs.le
          rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by norm_num)
  have key : (C : ℝ) * ((k : ℝ) + 1) ^ D * (2 : ℝ) ^ ((k + 1) / 2) ≤ (2 : ℝ) ^ k := by
    have hC : (0 : ℝ) ≤ C := by positivity
    calc (C : ℝ) * ((k : ℝ) + 1) ^ D * (2 : ℝ) ^ ((k + 1) / 2)
        ≤ (C : ℝ) * (2 ^ D * (k : ℝ) ^ D) * (2 * Real.sqrt 2 ^ k) := by
          gcongr
      _ = ((k : ℝ) ^ D * ((C : ℝ) * 2 ^ D * 2)) * Real.sqrt 2 ^ k := by ring
      _ ≤ ((k : ℝ) ^ D * ((C : ℝ) * 2 ^ D * 2 + 1)) * Real.sqrt 2 ^ k := by
          gcongr; linarith
      _ ≤ Real.sqrt 2 ^ k * Real.sqrt 2 ^ k := by
          exact mul_le_mul_of_nonneg_right h1.le hs.le
      _ = (2 : ℝ) ^ k := hsq
  exact_mod_cast key

/-- Monotonicity of the representing bound. -/
theorem rep_mono {n m : ℕ} {A : Fin n → Fin m → Bool} {s t : ℕ} (h : RepSizeAtMost A s)
    (hst : s ≤ t) : RepSizeAtMost A t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, h2.trans hst, h3⟩

/-- Reading a list's bits back as a function, with the index cast. -/
theorem adj_cast (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (k m : ℕ) (hm : m = k)
    (g : Fin (m + m) → Bool) :
    adjFun (k := m) (l := m) (A m) g = adjFun (k := k) (l := k) (A k)
      (fun i => g (Fin.cast (by omega) i)) := by
  subst hm; rfl

theorem threshold : ∀ (hB : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), HasCircuitSize (k + l) (adjFun A) s → RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PPoly := by
  intro hB A d K hd hcost hNP hsub
  obtain ⟨p, hp⟩ := hsub hNP
  set M := p.eval 1
  set D := p.natDegree
  obtain ⟨k0, hk0⟩ := eventually_small (d * (2 * M * 2 ^ D + 2)) (D + 1)
  set k := max K k0
  obtain ⟨C, hC1, hC2, hC3⟩ := hp (k + k)
  -- the circuit computes the adjacency function
  have hcirc : HasCircuitSize (k + k) (adjFun (A k)) (p.eval (k + k)) := by
    refine ⟨C, hC1, hC2, fun x => ?_⟩
    have hl : (List.ofFn x).length = k + k := List.length_ofFn
    have hm : (List.ofFn x).length / 2 = k := by rw [hl]; omega
    have hmem := hC3 (List.ofFn x) hl
    change _ ↔ (Even (List.ofFn x).length ∧ _) at hmem
    have hval : adjFun (k := (List.ofFn x).length / 2) (l := (List.ofFn x).length / 2)
        (A ((List.ofFn x).length / 2)) (fun i => (List.ofFn x).getD i false) = adjFun (A k) x := by
      rw [adj_cast A k _ hm]
      congr 1
      funext i
      simp [List.getD_eq_getElem?_getD]
    rw [hval] at hmem
    have hev : Even (List.ofFn x).length := by rw [hl]; exact ⟨k, rfl⟩
    apply Bool.eq_iff_iff.2
    rw [hmem]
    exact ⟨fun h => h.2, fun h => ⟨hev, h⟩⟩
  have hrep := hB k k _ (A k) hcirc
  -- the size is below the threshold
  have hpk : p.eval (k + k) ≤ M * 2 ^ D * (k + 1) ^ D := by
    calc p.eval (k + k) ≤ M * (k + k + 1) ^ D := poly_le p _
      _ ≤ M * (2 * (k + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
      _ = M * 2 ^ D * (k + 1) ^ D := by rw [mul_pow]; ring
  have hsmall := hk0 k (le_max_right K k0)
  have hpow : 1 ≤ 2 ^ ((k + 1) / 2) := Nat.one_le_two_pow
  have hkp : (k + 1) ^ D ≤ (k + 1) ^ (D + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hT : d * (2 * p.eval (k + k) + 2 * (k * 2 ^ ((k + 1) / 2))) ≤ 2 ^ k := by
    refine le_trans ?_ hsmall
    have e1 : 2 * p.eval (k + k) ≤ 2 * M * 2 ^ D * ((k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2)) := by
      have h1 : (k + 1) ^ D * 1 ≤ (k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2) := Nat.mul_le_mul hkp hpow
      rw [mul_one] at h1
      calc 2 * p.eval (k + k) ≤ 2 * (M * 2 ^ D * (k + 1) ^ D) := Nat.mul_le_mul_left 2 hpk
        _ ≤ 2 * (M * 2 ^ D * ((k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2))) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h1)
        _ = 2 * M * 2 ^ D * ((k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2)) := by ring
    have e2 : 2 * (k * 2 ^ ((k + 1) / 2)) ≤ 2 * ((k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2)) := by
      have : k ≤ (k + 1) ^ (D + 1) := by
        calc k ≤ k + 1 := Nat.le_succ k
          _ = (k + 1) ^ 1 := (pow_one _).symm
          _ ≤ (k + 1) ^ (D + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have := Nat.mul_le_mul_right (2 ^ ((k + 1) / 2)) this
      omega
    calc d * (2 * p.eval (k + k) + 2 * (k * 2 ^ ((k + 1) / 2)))
        ≤ d * ((2 * M * 2 ^ D + 2) * ((k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2))) := by
          apply Nat.mul_le_mul_left; nlinarith [e1, e2]
      _ = d * (2 * M * 2 ^ D + 2) * (k + 1) ^ (D + 1) * 2 ^ ((k + 1) / 2) := by ring
  have hdiv : 2 * p.eval (k + k) + 2 * (k * 2 ^ ((k + 1) / 2)) ≤ 2 ^ k / d :=
    (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hT)
  apply hcost k (le_max_left K k0)
  refine rep_mono hrep ?_
  omega

end PEqualNP.MetaComplexity.Threshold
