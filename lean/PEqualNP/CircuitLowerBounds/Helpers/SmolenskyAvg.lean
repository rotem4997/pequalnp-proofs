import PEqualNP.CircuitLowerBounds.Helpers.Approx
import PEqualNP.CircuitLowerBounds.Helpers.Smolensky1
import PEqualNP.CircuitLowerBounds.Helpers.Smolensky2
import PEqualNP.CircuitLowerBounds.Helpers.Smolensky3

/-!
# Parity is hard on average for AC0[p], p an odd prime

Helper module (proofs only, no statement may use it). A circuit of polynomial size and constant
depth over AND, OR, NOT and MOD `p` gates, `p` an odd prime, agrees with parity on at most a
`1 / 2 + 1 / (2 * K)` fraction of the inputs of every large length. The approximating
polynomial `F` of the circuit gives `1 - 2 * F`, which equals `(-1) ^ count` wherever the
circuit agrees with both `F` and parity; Smolensky's counting step bounds that set by the
binomial sum up to `n / 2 + D`, which is half the cube plus `D + 1` central binomial
coefficients; the numbers finish, at every large `n`.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds MvPolynomial

/-- The binomial coefficients strictly below the middle add up to at most half of `2 ^ n`. -/
theorem avg_sum_lower_half (n h : ℕ) (hh : 2 * h ≤ n) :
    2 * ∑ i ∈ Finset.range h, n.choose i ≤ 2 ^ n := by
  have himg : ∑ i ∈ (Finset.range h).image (fun i => n - i), n.choose i =
      ∑ i ∈ Finset.range h, n.choose i := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.mp hi
      exact Nat.choose_symm (by omega)
    · intro i hi j hj hij
      have := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      have := Finset.mem_range.mp (Finset.mem_coe.mp hj)
      simp only at hij
      omega
  have hdisj : Disjoint (Finset.range h) ((Finset.range h).image (fun i => n - i)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi'
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  have hsub : Finset.range h ∪ (Finset.range h).image (fun i => n - i) ⊆
      Finset.range (n + 1) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have := Finset.mem_range.mp hi
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (by omega)
  calc 2 * ∑ i ∈ Finset.range h, n.choose i
      = ∑ i ∈ Finset.range h, n.choose i +
          ∑ i ∈ (Finset.range h).image (fun i => n - i), n.choose i := by rw [himg]; ring
    _ = ∑ i ∈ Finset.range h ∪ (Finset.range h).image (fun i => n - i), n.choose i :=
        (Finset.sum_union hdisj).symm
    _ ≤ ∑ i ∈ Finset.range (n + 1), n.choose i :=
        Finset.sum_le_sum_of_subset hsub
    _ = 2 ^ n := Nat.sum_range_choose n

/-- Each further term of a binomial sum costs at most the middle coefficient. -/
theorem avg_sum_extend (n h k : ℕ) :
    ∑ i ∈ Finset.range (h + k), n.choose i ≤
      ∑ i ∈ Finset.range h, n.choose i + k * n.choose (n / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_range_succ]
    have := Nat.choose_le_middle (h + k) n
    calc _ ≤ ∑ i ∈ Finset.range h, n.choose i + k * n.choose (n / 2) + n.choose (n / 2) :=
          Nat.add_le_add ih this
      _ = _ := by ring

/-- The binomial sum up to `n / 2 + D` is at most half of `2 ^ n` plus `D + 1` middle
coefficients. -/
theorem avg_sum_choose_le (n D : ℕ) :
    2 * ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i ≤
      2 ^ n + 2 * (D + 1) * n.choose (n / 2) := by
  have h1 := avg_sum_extend n (n / 2) (D + 1)
  have h2 := avg_sum_lower_half n (n / 2) (by omega)
  rw [add_assoc]
  calc _ ≤ 2 * (∑ i ∈ Finset.range (n / 2), n.choose i + (D + 1) * n.choose (n / 2)) :=
        Nat.mul_le_mul_left _ h1
    _ = 2 * ∑ i ∈ Finset.range (n / 2), n.choose i + 2 * (D + 1) * n.choose (n / 2) := by ring
    _ ≤ _ := Nat.add_le_add_right h2 _

/-- The middle binomial coefficient is at most `2 ^ n / sqrt (n + 1)`. -/
theorem avg_middle_sq_le (n : ℕ) : (n.choose (n / 2)) ^ 2 * (n + 1) ≤ (2 ^ n) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h := centralBinom_sq_mul_le m
    rw [show 2 * m / 2 = m by omega]
    rw [Nat.centralBinom] at h
    calc _ ≤ 16 ^ m := h
      _ = (2 ^ (2 * m)) ^ 2 := by
          rw [← pow_mul, show 2 * m * 2 = 4 * m by ring, pow_mul]
          norm_num
  · have h := centralBinom_sq_mul_le (m + 1)
    rw [show (2 * m + 1) / 2 = m by omega]
    have h4 : Nat.centralBinom (m + 1) = 2 * (2 * m + 1).choose m := by
      have h7 : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := Nat.choose_symm_half m
      have h8 : (2 * m + 1 + 1).choose (m + 1) =
          (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := Nat.choose_succ_succ' _ _
      rw [Nat.centralBinom, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, h8, h7]
      ring
    rw [h4] at h
    have h5 : (2 ^ (2 * m + 1)) ^ 2 * 4 = 16 ^ (m + 1) := by
      rw [← pow_mul, show (2 * m + 1) * 2 = 4 * m + 2 by ring, pow_add, pow_mul, pow_succ]
      norm_num
      ring
    have h6 : ((2 * m + 1).choose m) ^ 2 * (2 * m + 1 + 1) * 4 ≤ (2 ^ (2 * m + 1)) ^ 2 * 4 := by
      rw [h5]
      refine le_trans ?_ h
      nlinarith [Nat.zero_le (((2 * m + 1).choose m) ^ 2)]
    exact Nat.le_of_mul_le_mul_right h6 (by norm_num)

/-- A power of `m + 1` times a constant is below `2 ^ m` from some point on. -/
theorem avg_pow_le_two_pow (c t : ℕ) : ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → c * (m + 1) ^ t ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt t (r := (2 : ℝ)) (by norm_num)
  have hpos : (0 : ℝ) < 1 / ((c : ℝ) * 2 ^ t + 1) := by positivity
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
  refine ⟨max m0 1, fun m hm => ?_⟩
  have hk := hm0 m (le_trans (le_max_left _ _) hm)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hk
  have h2 : ((c : ℝ) * 2 ^ t) * (m : ℝ) ^ t ≤ 2 ^ m := by
    have : (0 : ℝ) ≤ (m : ℝ) ^ t := by positivity
    nlinarith
  have h3 : c * 2 ^ t * m ^ t ≤ 2 ^ m := by exact_mod_cast h2
  calc c * (m + 1) ^ t ≤ c * (2 * m) ^ t :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = c * 2 ^ t * m ^ t := by rw [mul_pow]; ring
    _ ≤ 2 ^ m := h3

/-- The choice of the error parameter at every large input length: `2 ^ l` beats the size
bound, and the degree `((p - 1) * l) ^ d` is small against the square root of the length. -/
theorem avg_params (P : Polynomial ℕ) (p d K : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∃ l : ℕ, 1 ≤ l ∧ 4 * K * P.eval n ≤ 2 ^ l ∧
      16 * K ^ 2 * (((p - 1) * l) ^ d + 1) ^ 2 ≤ n + 1 := by
  set e := P.natDegree with he
  set c := P.eval 1 with hc
  set B := K + 3 + c + e with hB
  set M := (p - 1) * B + 1 with hM
  obtain ⟨m0, hm0⟩ := avg_pow_le_two_pow (64 * K ^ 2 * M ^ (2 * d)) (2 * d)
  refine ⟨2 ^ m0, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  set m := Nat.log 2 n with hmdef
  have hlo : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hmm : m0 ≤ m := by
    by_contra hlt
    have : 2 ^ (m + 1) ≤ 2 ^ m0 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨K + 3 + c + (m + 1) * e, by omega, ?_, ?_⟩
  · have hs : P.eval n ≤ 2 ^ c * 2 ^ ((m + 1) * e) := by
      refine (poly_eval_le P _ hn1).trans ?_
      refine Nat.mul_le_mul Nat.lt_two_pow_self.le ?_
      rw [pow_mul]
      exact Nat.pow_le_pow_left hhi.le _
    have hK : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
    calc 4 * K * P.eval n ≤ 4 * 2 ^ K * (2 ^ c * 2 ^ ((m + 1) * e)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) hs
      _ ≤ 8 * 2 ^ K * (2 ^ c * 2 ^ ((m + 1) * e)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
      _ = 2 ^ (K + 3 + c + (m + 1) * e) := by ring
  · have hl : (p - 1) * (K + 3 + c + (m + 1) * e) ≤ (p - 1) * B * (m + 1) := by
      rw [mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      rw [hB]
      nlinarith
    have hl' : (p - 1) * (K + 3 + c + (m + 1) * e) ≤ M * (m + 1) :=
      hl.trans (Nat.mul_le_mul_right _ (by omega))
    have hone : 1 ≤ (M * (m + 1)) ^ d := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    have hD : ((p - 1) * (K + 3 + c + (m + 1) * e)) ^ d + 1 ≤ 2 * (M * (m + 1)) ^ d := by
      have := Nat.pow_le_pow_left hl' d
      omega
    calc 16 * K ^ 2 * (((p - 1) * (K + 3 + c + (m + 1) * e)) ^ d + 1) ^ 2
        ≤ 16 * K ^ 2 * (2 * (M * (m + 1)) ^ d) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD _)
      _ = 64 * K ^ 2 * M ^ (2 * d) * (m + 1) ^ (2 * d) := by
          have h : ((M * (m + 1)) ^ d) ^ 2 = M ^ (2 * d) * (m + 1) ^ (2 * d) := by
            rw [← pow_mul, mul_pow, mul_comm d 2]
          rw [mul_pow 2, h]
          ring
      _ ≤ 2 ^ m := hm0 m hmm
      _ ≤ n + 1 := by omega

/-- Where a polynomial `F` over `ZMod p`, `p` odd, takes the 0/1 value of parity, the
polynomial `1 - 2 * F` takes the value `(-1) ^ count`. -/
theorem avg_sign_eval {p n : ℕ} [Fact p.Prime] (F : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool)
    (b : Bool) (hb : b = decide ((List.ofFn x).count true % 2 = 1))
    (hF : eval (fun i => if x i = true then (1 : ZMod p) else 0) F =
      (if b = true then (1 : ZMod p) else 0)) :
    eval (fun i => if x i = true then (1 : ZMod p) else 0) (C 1 - C 2 * F) =
      ∏ i, (if x i = true then (-1 : ZMod p) else 1) := by
  rw [smol_prod_eq_pow, map_sub, map_mul, eval_C, eval_C, hF, hb]
  by_cases h : (List.ofFn x).count true % 2 = 1
  · rw [decide_eq_true h, if_pos rfl, (Nat.odd_iff.mpr h).neg_one_pow]
    ring
  · rw [decide_eq_false h, if_neg (by simp),
      (Nat.even_iff.mpr (by omega : (List.ofFn x).count true % 2 = 0)).neg_one_pow]
    ring

theorem avg_sign_deg {p n : ℕ} (F : MvPolynomial (Fin n) (ZMod p)) :
    (C 1 - C 2 * F : MvPolynomial (Fin n) (ZMod p)).totalDegree ≤ F.totalDegree := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_C]
    exact Nat.zero_le _
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]

/-- Parity is hard on average for AC0[`p`], `p` an odd prime: at every large input length a
circuit of polynomial size and constant depth over AND, OR, NOT and MOD `p` agrees with parity
on at most a `1 / 2 + 1 / (2 * K)` fraction of the inputs. -/
theorem parity_avg_hard :
    ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ∀ (P : Polynomial ℕ) (d K : ℕ), ∃ n0 : ℕ, ∀ n : ℕ,
      n0 ≤ n → ∀ C : Circuit,
      (∀ g ∈ C.gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp)) →
      C.size ≤ P.eval n → C.depth n ≤ d →
      (Finset.univ.filter fun x : Fin n → Bool =>
        C.eval (List.ofFn x) = decide ((List.ofFn x).count true % 2 = 1)).card * (2 * K) ≤
        (K + 1) * 2 ^ n := by
  intro p hp hp2 P d K
  obtain ⟨n0, hn0⟩ := avg_params P p d K
  refine ⟨n0, fun n hn Cc hgates hsize hdepth => ?_⟩
  obtain ⟨l, hl1, hsz, hdeg⟩ := hn0 n hn
  obtain ⟨F, hFdeg, hErr⟩ := approx p hp n (P.eval n) d l Cc hgates hsize hdepth hl1
  haveI : Fact p.Prime := ⟨hp⟩
  have hω1 : (-1 : ZMod p) ≠ 1 := by
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
    exact ZMod.neg_one_ne_one
  have hω0 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  classical
  set E := (Finset.univ.filter fun x : Fin n → Bool =>
    MvPolynomial.eval (fun i => if x i = true then (1 : ZMod p) else 0) F ≠
      (if Cc.eval (List.ofFn x) = true then (1 : ZMod p) else 0)) with hE
  set Agr := (Finset.univ.filter fun x : Fin n → Bool =>
    Cc.eval (List.ofFn x) = decide ((List.ofFn x).count true % 2 = 1)) with hAgr
  have hG : ∀ x ∈ Agr \ E, eval (fun i => if x i = true then (1 : ZMod p) else 0)
      (MvPolynomial.C 1 - MvPolynomial.C 2 * F) =
        ∏ i, (if x i = true then (-1 : ZMod p) else 1) := by
    intro x hx
    obtain ⟨hxA, hxE⟩ := Finset.mem_sdiff.mp hx
    rw [hE, Finset.mem_filter, not_and, not_not] at hxE
    exact avg_sign_eval F x _ (Finset.mem_filter.mp hxA).2 (hxE (Finset.mem_univ _))
  have hcard := smolensky_card_le (-1 : ZMod p) hω0 hω1 (((p - 1) * l) ^ d) _
    ((avg_sign_deg F).trans hFdeg) (Agr \ E) hG
  have hsum := avg_sum_choose_le n (((p - 1) * l) ^ d)
  have hmid := avg_middle_sq_le n
  have hsplit : Agr.card ≤ (Agr \ E).card + E.card :=
    (Finset.card_le_card (by
      intro x hx
      by_cases hxE : x ∈ E
      · exact Finset.mem_union_right _ hxE
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxE⟩))).trans
      (Finset.card_union_le _ _)
  -- the numbers
  generalize ((p - 1) * l) ^ d = D at hdeg hcard hsum
  generalize ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i = S at hcard hsum
  generalize n.choose (n / 2) = c at hsum hmid
  generalize (Agr \ E).card = a at hcard hsplit
  generalize E.card = e at hErr hsplit
  generalize Agr.card = g at hsplit
  generalize P.eval n = s at hsz hErr
  generalize (2 : ℕ) ^ n = T at hErr hsum hmid
  have h1 : 2 ^ l * (4 * K * e) ≤ 2 ^ l * T := by
    calc 2 ^ l * (4 * K * e) = 4 * K * (e * 2 ^ l) := by ring
      _ ≤ 4 * K * (s * T) := Nat.mul_le_mul_left _ hErr
      _ = 4 * K * s * T := by ring
      _ ≤ 2 ^ l * T := Nat.mul_le_mul_right _ hsz
  have h2 : 4 * K * e ≤ T := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 : (4 * K * (D + 1) * c) ^ 2 ≤ T ^ 2 := by
    calc (4 * K * (D + 1) * c) ^ 2 = 16 * K ^ 2 * (D + 1) ^ 2 * c ^ 2 := by ring
      _ ≤ (n + 1) * c ^ 2 := Nat.mul_le_mul_right _ hdeg
      _ = c ^ 2 * (n + 1) := by ring
      _ ≤ T ^ 2 := hmid
  have h4 : 4 * K * (D + 1) * c ≤ T := (Nat.pow_le_pow_iff_left (by norm_num)).mp h3
  have h5 : 2 * K * (2 * a) ≤ 2 * K * (T + 2 * (D + 1) * c) :=
    Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ hcard).trans hsum)
  have h6 : 4 * K * g ≤ 4 * K * (a + e) := Nat.mul_le_mul_left _ hsplit
  nlinarith

end PEqualNP.CircuitLowerBounds.Helpers
