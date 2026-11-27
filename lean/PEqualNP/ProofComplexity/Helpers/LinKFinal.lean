import PEqualNP.ProofComplexity.L049
import PEqualNP.ProofComplexity.Helpers.PhpFinal
import PEqualNP.Defs.ProofComplexityLinK

/-!
# Final assembly of L-pcx-054 (Res(k, ⊕) is not polynomially bounded on functional pigeonhole)

The general degree to size theorem for Res(k, ⊕) (the plan `LinKPlan`) enters as a hypothesis,
`StmtLinK`. From it, the expanders of L-pcx-043 and the degree bound L-pcx-049 on the functional
pigeonhole formula:

* `fun_exp`: for every `k ≥ 1` an explicit bound `exp (c * n) ≤ π.length` for all large `n`;
* `fun_not_poly`: the statement of L-pcx-054.

With `b`, `s₀`, `n₀` the constants of L-pcx-043, `w = max b 2` and the degree
`D = (n / s₀) / w`, the constant is `c = ρ ^ k / (32 k s₀ w)` with `ρ = 1 / (16 s₀ w ^ 2)`.
-/

namespace PEqualNP.ProofComplexity.LinKFinal

open PEqualNP.ProofComplexity PEqualNP.Expanders

/-- The general theorem of the plan: degree to size for Res(k, ⊕). -/
def StmtLinK : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)

/-- The clauses of the functional pigeonhole formula on a graph of left degree at most `b` have
at most `max b 2` literals. -/
theorem funGraphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ funGraphPHP G, C.card ≤ max b 2 := by
  intro C hC
  rcases hC with hC | ⟨e, e', -, -, rfl⟩
  · exact PhpFinal.graphPHP_width G b hb C hC
  · exact le_trans Finset.card_le_two (le_max_right _ _)

/-- Evaluation of a polynomial with natural coefficients is monotone. -/
theorem poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (hxy : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)

/-- The degree: with `s = n / s₀` and `D = s / w`, `w * D ≤ s`, and `n ≤ 2 * s₀ * w * D`
once `4 * s₀ * w ≤ n`. -/
theorem degree_facts (n s₀ w : ℕ) (hs : 0 < s₀) (hw : 0 < w) (hn : 4 * (s₀ * w) ≤ n) :
    w * (n / s₀ / w) ≤ n / s₀ ∧ n ≤ 2 * (s₀ * w * (n / s₀ / w)) := by
  refine ⟨Nat.mul_div_le _ _, ?_⟩
  have h1 : n < s₀ * (n / s₀ + 1) := Nat.lt_mul_div_succ n hs
  have h2 : n / s₀ < w * (n / s₀ / w + 1) := Nat.lt_mul_div_succ _ hw
  have h3 : s₀ * (n / s₀ + 1) ≤ s₀ * (w * (n / s₀ / w + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : s₀ * (w * (n / s₀ / w + 1)) = s₀ * w * (n / s₀ / w) + s₀ * w := by ring
  omega

/-- The arithmetic of the exponent: with at most `2 * n * w` variables and
`n ≤ 2 * s₀ * w * D`, the exponent of the general theorem is at least `c * n`. -/
theorem exp_arith (k s₀ w n D card : ℕ) (hk : 1 ≤ k) (hs : 0 < s₀) (hw : 0 < w) (hn : 0 < n)
    (hcard_pos : 0 < card) (hcard : card ≤ 2 * n * w) (hnD : n ≤ 2 * (s₀ * w * D)) :
    (1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n ≤
      (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < card := by exact_mod_cast hcard_pos
  have hDR : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hnD' : (n : ℝ) ≤ 2 * ((s₀ : ℝ) * w * D) := by exact_mod_cast hnD
  have hcard' : (card : ℝ) ≤ 2 * n * w := by exact_mod_cast hcard
  set ρ : ℝ := 1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have h1 : (n : ℝ) / (32 * (k : ℝ) * s₀ * w) ≤ (D : ℝ) / (16 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnD' (by positivity : (0 : ℝ) ≤ 16 * (k : ℝ))]
  have h2 : ρ ≤ (D : ℝ) / (4 * (card : ℝ)) := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h8 : 4 * (card : ℝ) ≤ 8 * n * w := by linarith
    have h9 : 8 * (n : ℝ) * w ≤ 16 * ((s₀ : ℝ) * w * D) * w := by
      have := mul_le_mul_of_nonneg_right hnD' (by positivity : (0 : ℝ) ≤ 8 * w)
      linarith
    nlinarith
  have h3 : ρ ^ k ≤ ((D : ℝ) / (4 * (card : ℝ))) ^ k := pow_le_pow_left₀ hρ0 h2 k
  calc ρ ^ k / (32 * (k : ℝ) * s₀ * w) * n = (n : ℝ) / (32 * (k : ℝ) * s₀ * w) * ρ ^ k := by
        ring
    _ ≤ (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k :=
        mul_le_mul h1 h3 (pow_nonneg hρ0 k) (by positivity)

/-- The explicit bound on the functional pigeonhole formula of the expanders of L-pcx-043. -/
theorem fun_exp (hL : StmtLinK) :
    ∃ b : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ ∀ n ≥ n₀,
      ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
        Fintype.card (PEqualNP.Expanders.GEdge G) ≤ (n + 1) * b ∧
        ∀ π : List (LinKLine (PEqualNP.Expanders.GEdge G)),
          IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π →
          Real.exp (c * n) ≤ (π.length : ℝ) := by
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  refine ⟨b, fun k hk => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = max b 2 := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs₀
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨(1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w),
    max (max n₀ (2 * (s₀ * w) * (16 * k + 4 * w))) (4 * (s₀ * w) + s₀), by positivity, ?_⟩
  intro n hn
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : 4 * (s₀ * w) + s₀ ≤ n := le_trans (le_max_right _ _) hn
  have hsw : 0 < s₀ * w := Nat.mul_pos hs₀ (by omega)
  have hnpos : 0 < n := by omega
  obtain ⟨G, hLd, -, hE⟩ := hG n hn0
  refine ⟨G, PhpFinal.card_gedge_le G b hLd, ?_⟩
  intro π hπ
  obtain ⟨hwD, hnD⟩ := degree_facts n s₀ w hs₀ (by omega) (by omega)
  set D := n / s₀ / w with hD
  -- the degree is large
  have hDk : 16 * k + 4 * w ≤ D := by
    have h : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ 2 * (s₀ * w) * D := by
      calc 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n := hn1
        _ ≤ 2 * (s₀ * w * D) := hnD
        _ = 2 * (s₀ * w) * D := by ring
    exact Nat.le_of_mul_le_mul_left h (by omega)
  have hs1 : 1 ≤ n / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr (by omega)
  have hLw : LeftDegLe G w := fun i => le_trans (hLd i) hbw
  have hnr := PEqualNP.ProofComplexity.L049 (n + 1) n G (n / s₀) w D hE hLw hs1 hwD
  -- the graph has an edge
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

/-- L-pcx-054 from the general theorem: for every `k ≥ 1`, Res(k, ⊕) is not polynomially
bounded on functional pigeonhole formulas. -/
theorem fun_not_poly (hL : StmtLinK) :
    ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N), N < m ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length := by
  intro k hk p
  obtain ⟨b, hb⟩ := fun_exp hL
  obtain ⟨c, n₀, hc, hexp⟩ := hb k hk
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) *
      (2 * (b + 1)) ^ d := ⟨_, rfl⟩
  have hcpow : (0 : ℝ) < c ^ (d + 1) := pow_pos hc _
  have hfact : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨K, hK⟩ := exists_nat_gt ((C : ℝ) * ((d + 1).factorial : ℝ) / c ^ (d + 1))
  obtain ⟨n, hn0, hnK, hn1⟩ : ∃ n : ℕ, n₀ ≤ n ∧ K ≤ n ∧ 1 ≤ n :=
    ⟨max (max n₀ K) 1, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨G, hcardG, hG⟩ := hexp n hn0
  refine ⟨n + 1, n, G, Nat.lt_succ_self n, ?_⟩
  intro π hπ
  have h1 := hG π hπ
  -- the polynomial at the number of variables
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
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hKn : (C : ℝ) * ((d + 1).factorial : ℝ) / c ^ (d + 1) < n :=
    lt_of_lt_of_le hK (by exact_mod_cast hnK)
  rw [div_lt_iff₀ hcpow] at hKn
  have hfac := Real.pow_div_factorial_le_exp (x := c * n)
    (mul_nonneg hc.le hnR.le) (d + 1)
  have hlt : (C : ℝ) * (n : ℝ) ^ d < (c * n) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
    rw [lt_div_iff₀ hfact]
    calc (C : ℝ) * (n : ℝ) ^ d * ((d + 1).factorial : ℝ)
        = (C : ℝ) * ((d + 1).factorial : ℝ) * (n : ℝ) ^ d := by ring
      _ < (n : ℝ) * c ^ (d + 1) * (n : ℝ) ^ d :=
          mul_lt_mul_of_pos_right hKn (pow_pos hnR d)
      _ = (c * n) ^ (d + 1) := by ring
  have hfin : ((p.eval (Fintype.card (GEdge G)) : ℕ) : ℝ) < (π.length : ℝ) := by linarith
  exact_mod_cast hfin

end PEqualNP.ProofComplexity.LinKFinal
