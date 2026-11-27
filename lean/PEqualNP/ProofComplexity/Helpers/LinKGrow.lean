import PEqualNP.ProofComplexity.Helpers.LinKWire
import PEqualNP.ProofComplexity.Helpers.LinKSim

/-!
# Res(k, ⊕) with growing k on functional pigeonhole (L-pcx-059)

The assembly of L-pcx-054 with `k` not fixed. With `b`, `s₀` the constants of L-pcx-043,
`w = max b 2` and `B = 16 * s₀ * w ^ 2`, one expander `G` on `n + 1` pigeons and `n` holes serves
every `k ≥ 1` with `B ^ (2 * k) ≤ n` at once:

* `graph_bound`: the bound `exp (ρ ^ k / (32 k s₀ w) * n) ≤ π.length` on a given expander, with
  `ρ = 1 / B` and the threshold on `n` explicit in `k`;
* `root_arith`: when `B ^ (2 * k) ≤ n`, the fourth power of `n / (B ^ k * k)` is at least `n`
  (so the exponent is at least the fourth root of `n` over `32 s₀ w`);
* `grow_k`: the statement of L-pcx-059.
-/

namespace PEqualNP.ProofComplexity.LinKGrow

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.LinKFinal

/-- The size bound of the general theorem on one given expander, with the threshold on `n`
explicit in `k`. -/
theorem graph_bound (hL : StmtLinK) (b s₀ n k w : ℕ) (hw : w = max b 2) (hs₀ : 0 < s₀)
    (hk : 1 ≤ k) (G : BipGraph (n + 1) n) (hLd : LeftDegLe G b)
    (hE : IsBdryExpander G (n / s₀) 2)
    (hn1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n) (hn2 : 4 * (s₀ * w) + s₀ ≤ n)
    (π : List (LinKLine (GEdge G))) (hπ : IsLinKRefutation k (funGraphPHP G) π) :
    Real.exp ((1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n)
      ≤ (π.length : ℝ) := by
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  have hsw : 0 < s₀ * w := Nat.mul_pos hs₀ (by omega)
  have hnpos : 0 < n := by omega
  obtain ⟨hwD, hnD⟩ := degree_facts n s₀ w hs₀ (by omega) (by omega)
  set D := n / s₀ / w with hD
  have hDk : 16 * k + 4 * w ≤ D := by
    have h : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ 2 * (s₀ * w) * D := by
      calc 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n := hn1
        _ ≤ 2 * (s₀ * w * D) := hnD
        _ = 2 * (s₀ * w) * D := by ring
    exact Nat.le_of_mul_le_mul_left h (by omega)
  have hs1 : 1 ≤ n / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr (by omega)
  have hLw : LeftDegLe G w := fun i => le_trans (hLd i) hbw
  have hnr := PEqualNP.ProofComplexity.L049 (n + 1) n G (n / s₀) w D hE hLw hs1 hwD
  have hcard_pos : 0 < Fintype.card (GEdge G) := by
    have h := hE {0} (by rw [Finset.card_singleton]; exact hs1)
    rw [Finset.card_singleton] at h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) h)
    unfold uniqueNbrs at hj
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj).2
    have hi' : i ∈ Finset.filter (fun i => j ∈ G i) {0} := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact Fintype.card_pos_iff.mpr ⟨⟨(i, j), (Finset.mem_filter.mp hi').2⟩⟩
  have hcard : Fintype.card (GEdge G) ≤ 2 * n * w := by
    have := le_trans (PhpFinal.card_gedge_le G b hLd) (Nat.mul_le_mul_left (n + 1) hbw)
    have h2 : (n + 1) * w ≤ 2 * n * w := Nat.mul_le_mul_right _ (by omega)
    omega
  have hsize := hL (GEdge G) (funGraphPHP G) π k w D
    (fun C hC => hw ▸ funGraphPHP_width G b hLd C hC) hk (by omega) (by omega) hnr hπ
  have harith := exp_arith k s₀ w n D (Fintype.card (GEdge G)) hk hs₀ (by omega) hnpos
    hcard_pos hcard hnD
  exact le_trans (Real.exp_le_exp.mpr harith) hsize

/-- A natural number is at most its power of two, so its fourth power is at most `16 ^ k`. -/
theorem pow_four_le_sixteen_pow (k : ℕ) : k ^ 4 ≤ 16 ^ k := by
  have h : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  calc k ^ 4 ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left h 4
    _ = 16 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- When `B ^ (2 * k) ≤ n` and `k ^ 4 ≤ n`, the fourth power of `n / (B ^ k * k)` is at least
`n`. -/
theorem root_arith (B k n : ℕ) (hk : 1 ≤ k) (hB : 1 ≤ B) (hn : B ^ (2 * k) ≤ n)
    (hk4 : k ^ 4 ≤ n) :
    (n : ℝ) ≤ ((n : ℝ) / ((B : ℝ) ^ k * (k : ℝ))) ^ 4 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hM : (0 : ℝ) < (B : ℝ) ^ k := pow_pos hBR k
  have h1 : ((B : ℝ) ^ k) ^ 4 ≤ (n : ℝ) ^ 2 := by
    have h : (B ^ (2 * k)) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    have e : ((B : ℝ) ^ k) ^ 4 = (((B ^ (2 * k)) ^ 2 : ℕ) : ℝ) := by
      push_cast; rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [e]; exact_mod_cast h
  have h2 : (k : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hk4
  have h3 : ((B : ℝ) ^ k * (k : ℝ)) ^ 4 ≤ (n : ℝ) ^ 3 := by
    rw [mul_pow]
    calc ((B : ℝ) ^ k) ^ 4 * (k : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 * (n : ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (n : ℝ) ^ 3 := by ring
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (n : ℝ) * ((B : ℝ) ^ k * (k : ℝ)) ^ 4 ≤ (n : ℝ) * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hnR
    _ = (n : ℝ) ^ 4 := by ring

/-- L-pcx-059: one constant `B`; for every polynomial `p` and every large `n`, one graph `G` on
`n + 1` pigeons and `n` holes such that for every `k ≥ 1` with `B ^ (2 * k) ≤ n`, every
Res(k, ⊕) refutation of the functional pigeonhole formula on `G` has more than `p` of the
number of variables many lines. -/
theorem grow_k : ∃ B : ℕ, 2 ≤ B ∧ ∀ p : Polynomial ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G))), 1 ≤ k → B ^ (2 * k) ≤ n → PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length := by
  have hL : StmtLinK := LinKWire.general LinKSim.simulation_refutation
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = max b 2 := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hsw2 : 4 ≤ s₀ * w ^ 2 := by nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = 16 * s₀ * w ^ 2 := ⟨_, rfl⟩
  have hB64 : 64 ≤ B := by rw [hB, mul_assoc]; omega
  refine ⟨B, by omega, fun p => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) *
      (2 * (b + 1)) ^ d := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℕ, c0 = 32 * s₀ * w := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 4 * (d + 1) := ⟨_, rfl⟩
  refine ⟨max (max n₀ B) (max ((64 * s₀ * w) ^ 2) (C * c0 ^ N * N.factorial + 1)),
    fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnB : B ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hna : (64 * s₀ * w) ^ 2 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnK : C * c0 ^ N * N.factorial + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨G, hLd, -, hE⟩ := hG n hn0
  refine ⟨G, fun k π hk hBk hπ => ?_⟩
  -- `k` is at most the fourth root of `n`
  have hk4 : k ^ 4 ≤ n := by
    calc k ^ 4 ≤ 16 ^ k := pow_four_le_sixteen_pow k
      _ ≤ (B ^ 2) ^ k := Nat.pow_le_pow_left (by nlinarith) k
      _ = B ^ (2 * k) := by rw [pow_mul]
      _ ≤ n := hBk
  -- the thresholds of `graph_bound`
  have hak : 64 * s₀ * w * k ≤ n := by
    have h : (64 * s₀ * w * k) ^ 4 ≤ n ^ 4 := by
      calc (64 * s₀ * w * k) ^ 4 = ((64 * s₀ * w) ^ 2) ^ 2 * k ^ 4 := by ring
        _ ≤ n ^ 2 * n := Nat.mul_le_mul (Nat.pow_le_pow_left hna 2) hk4
        _ = n ^ 3 := by ring
        _ ≤ n ^ 4 := Nat.pow_le_pow_right hn1 (by norm_num)
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h
  have hth1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n := by
    have e : 2 * (2 * (s₀ * w) * (16 * k + 4 * w)) = 64 * s₀ * w * k + 16 * s₀ * w ^ 2 := by
      ring
    rw [← hB] at e
    omega
  have hth2 : 4 * (s₀ * w) + s₀ ≤ n := by
    have h1 : s₀ * w ≤ s₀ * w ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : s₀ ≤ s₀ * w ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have h3 : B = 16 * (s₀ * w ^ 2) := by rw [hB]; ring
    omega
  have h1 := graph_bound hL b s₀ n k w hw hs₀ hk G hLd hE hth1 hth2 π hπ
  set x : ℝ := (1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n with hx
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs₀
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hc0R : (0 : ℝ) < c0 := by rw [hc0]; push_cast; positivity
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  -- the exponent is at least the fourth root of `n` over `c0`
  have hroot : (n : ℝ) ≤ ((c0 : ℝ) * x) ^ 4 := by
    have h := root_arith B k n hk (by omega) hBk hk4
    have e : (c0 : ℝ) * x = (n : ℝ) / ((B : ℝ) ^ k * (k : ℝ)) := by
      rw [hx, hc0, hB]
      push_cast
      rw [one_div, inv_pow]
      field_simp
    rw [e]; exact h
  -- the polynomial at the number of variables
  have hcardG := PhpFinal.card_gedge_le G b hLd
  have hY : Fintype.card (GEdge G) ≤ n * (2 * (b + 1)) := by
    have : (n + 1) * b ≤ n * (2 * (b + 1)) := by nlinarith
    omega
  have hpolyN : p.eval (Fintype.card (GEdge G)) ≤ C * n ^ d := by
    have hm := poly_eval_mono p hY
    have hb2 := Helpers.poly_eval_le_coeffSum_mul_pow p (n * (2 * (b + 1)))
      (Nat.one_le_iff_ne_zero.mpr (by positivity))
    calc p.eval (Fintype.card (GEdge G)) ≤ p.eval (n * (2 * (b + 1))) := hm
      _ ≤ _ := hb2
      _ = C * n ^ d := by rw [hC, hd, mul_pow]; ring
  have hpoly : ((p.eval (Fintype.card (GEdge G)) : ℕ) : ℝ) ≤ (C : ℝ) * (n : ℝ) ^ d := by
    exact_mod_cast hpolyN
  have hfact : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hKn : (C : ℝ) * (c0 : ℝ) ^ N * (N.factorial : ℝ) < n := by
    have : C * c0 ^ N * N.factorial < n := by omega
    exact_mod_cast this
  have hpowN : (n : ℝ) ^ (d + 1) ≤ (c0 : ℝ) ^ N * x ^ N := by
    calc (n : ℝ) ^ (d + 1) ≤ (((c0 : ℝ) * x) ^ 4) ^ (d + 1) :=
          pow_le_pow_left₀ hnR.le hroot (d + 1)
      _ = (c0 : ℝ) ^ N * x ^ N := by rw [← pow_mul, hN, mul_pow]
  have hfac := Real.pow_div_factorial_le_exp (x := x) hx0 N
  have hlt : (C : ℝ) * (n : ℝ) ^ d < x ^ N / (N.factorial : ℝ) := by
    rw [lt_div_iff₀ hfact]
    have h : (C : ℝ) * (n : ℝ) ^ d * (N.factorial : ℝ) * (c0 : ℝ) ^ N < x ^ N * (c0 : ℝ) ^ N := by
      calc (C : ℝ) * (n : ℝ) ^ d * (N.factorial : ℝ) * (c0 : ℝ) ^ N
          = (C : ℝ) * (c0 : ℝ) ^ N * (N.factorial : ℝ) * (n : ℝ) ^ d := by ring
        _ < (n : ℝ) * (n : ℝ) ^ d := mul_lt_mul_of_pos_right hKn (pow_pos hnR d)
        _ = (n : ℝ) ^ (d + 1) := by ring
        _ ≤ (c0 : ℝ) ^ N * x ^ N := hpowN
        _ = x ^ N * (c0 : ℝ) ^ N := by ring
    exact lt_of_mul_lt_mul_right h (pow_pos hc0R N).le
  have hfin : ((p.eval (Fintype.card (GEdge G)) : ℕ) : ℝ) < (π.length : ℝ) := by linarith
  exact_mod_cast hfin

end PEqualNP.ProofComplexity.LinKGrow
