import PEqualNP.ProofComplexity.L043
import PEqualNP.ProofComplexity.Helpers.DegSizeAssembly
import PEqualNP.ProofComplexity.Helpers.ExpBeatsPoly
import PEqualNP.Defs.Expanders

/-!
# Final assembly of L-pcx-017 (Res(⊕) refutations of the pigeonhole formula are long)

Two links of the chain enter as hypotheses, stated here as propositions:

* `Stmt046`: the pigeonhole formula on a boundary expander has no polynomial calculus
  refutation of low degree;
* `Stmt047`: a Res(⊕) refutation of `PHP m N` restricts to one of `graphPHP G` of at most
  twice the length.

From them, the expanders of L-pcx-043 and the degree to size theorem of L-pcx-042:

* `php_exp`: an explicit bound `exp (c * n) ≤ π.length` for all large `n`;
* `php_not_poly`: no polynomial bounds the length.

With `b`, `s₀`, `n₀` the constants of L-pcx-043 and `w = max b 2`, the constant is
`c = 1 / (16384 * s₀ ^ 2 * w)` and the threshold is
`max (max n₀ (2 * s₀ * (34 + 2 * w))) (16384 * s₀ ^ 2 * w)`.
-/

namespace PEqualNP.ProofComplexity.PhpFinal

open PEqualNP.ProofComplexity PEqualNP.Expanders

/-- The statement of L-pcx-046: no low degree polynomial calculus refutation of the pigeonhole
formula on a boundary expander. -/
def Stmt046 : Prop := ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → 2 * (D + 1) ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.graphPHP G)) D

/-- The statement of L-pcx-047: a Res(⊕) refutation of the pigeonhole formula gives one of the
pigeonhole formula on any graph, of at most twice the length. -/
def Stmt047 : Prop := ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin N))), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP m N) π → ∃ π' : List (PEqualNP.ProofComplexity.LinClause (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.Expanders.graphPHP G) π' ∧ π'.length ≤ 2 * π.length

/-- A graph of left degree at most `b` has at most `m * b` edges. -/
theorem card_gedge_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    Fintype.card (GEdge G) ≤ m * b := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ((Finset.univ.filter (fun e : Fin m × Fin N => e.2 ∈ G e.1)).filter
        (fun e => e.1 = i)).card ≤ b := by
    intro i _
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hb i)
    · intro e he
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have h1 := (Finset.mem_filter.mp he'.1).2
      rw [he'.2] at h1
      exact Finset.mem_coe.mpr h1
    · intro e he e' he' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
      exact Prod.ext (h1.trans h2.symm) h
  calc _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum hfib
    _ = m * b := by simp

/-- The clauses of the pigeonhole formula on a graph of left degree at most `b` have at most
`max b 2` literals. -/
theorem graphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ graphPHP G, C.card ≤ max b 2 := by
  classical
  intro C hC
  rcases hC with ⟨i, rfl⟩ | ⟨e, e', -, -, rfl⟩
  · refine le_trans (le_trans
      (Finset.card_le_card_of_injOn (fun l : Literal (GEdge G) => l.1.1.2) ?_ ?_) (hb i))
      (le_max_left _ _)
    · intro l hl
      have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h1 : l.1.1.2 ∈ G l.1.1.1 := l.1.2
      rw [hl'.1] at h1
      exact Finset.mem_coe.mpr h1
    · intro l hl l' hl' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl')).2
      exact Prod.ext (Subtype.ext (Prod.ext (h1.1.trans h2.1.symm) h)) (h1.2.trans h2.2.symm)
  · exact le_trans Finset.card_le_two (le_max_right _ _)

/-- The arithmetic of the exponent: with at most `(n + 1) * w` variables and degree at least
`n / (4 * s₀)`, the exponent of the degree to size theorem is linear in `n`. -/
theorem exp_arith (s₀ w n D card : ℕ) (hs : 0 < s₀) (hw : 0 < w) (hn : 0 < n)
    (hcard_pos : 0 < card) (hcard : card ≤ (n + 1) * w) (hnD : n ≤ 4 * s₀ * D) :
    (n : ℝ) / (8192 * (s₀ : ℝ) ^ 2 * w) ≤ ((D : ℝ) ^ 2) / (256 * (card : ℝ)) := by
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < card := by exact_mod_cast hcard_pos
  have hDR : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h1 : (card : ℝ) ≤ 2 * n * w := by
    have : card ≤ 2 * n * w :=
      le_trans hcard (Nat.mul_le_mul_right _ (by omega))
    exact_mod_cast this
  have h2 : (n : ℝ) ^ 2 ≤ 16 * (s₀ : ℝ) ^ 2 * (D : ℝ) ^ 2 := by
    have h : (n : ℝ) ≤ 4 * s₀ * D := by exact_mod_cast hnD
    have := pow_le_pow_left₀ hnR.le h 2
    calc (n : ℝ) ^ 2 ≤ (4 * s₀ * D) ^ 2 := this
      _ = 16 * (s₀ : ℝ) ^ 2 * (D : ℝ) ^ 2 := by ring
  have hden1 : (0 : ℝ) < 8192 * (s₀ : ℝ) ^ 2 * w :=
    mul_pos (mul_pos (by norm_num) (pow_pos hsR 2)) hwR
  have hden2 : (0 : ℝ) < 256 * (card : ℝ) := mul_pos (by norm_num) hcR
  rw [div_le_div_iff₀ hden1 hden2]
  have h512 : (0 : ℝ) ≤ 512 * w := by linarith
  calc (n : ℝ) * (256 * (card : ℝ)) ≤ (n : ℝ) * (256 * (2 * n * w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) hnR.le
    _ = 512 * w * (n : ℝ) ^ 2 := by ring
    _ ≤ 512 * w * (16 * (s₀ : ℝ) ^ 2 * (D : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h2 h512
    _ = (D : ℝ) ^ 2 * (8192 * (s₀ : ℝ) ^ 2 * w) := by ring

/-- The explicit bound: from the statements of L-pcx-046 and L-pcx-047, every Res(⊕) refutation
of the pigeonhole formula with `n + 1` pigeons and `n` holes has at least `exp (c * n)` lines,
for a constant `c > 0` and all large `n`. -/
theorem php_exp (h46 : Stmt046) (h47 : Stmt047) :
    ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ ∀ n ≥ n₀, ∀ π : List (LinClause (Fin (n + 1) × Fin n)),
      IsLinRefutation (PHP (n + 1) n) π → Real.exp (c * n) ≤ (π.length : ℝ) := by
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = max b 2 := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs₀
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hden : (0 : ℝ) < 16384 * (s₀ : ℝ) ^ 2 * w :=
    mul_pos (mul_pos (by norm_num) (pow_pos hsR 2)) hwR
  refine ⟨1 / (16384 * (s₀ : ℝ) ^ 2 * w),
    max (max n₀ (2 * s₀ * (34 + 2 * w))) (16384 * s₀ ^ 2 * w), div_pos one_pos hden, ?_⟩
  intro n hn π hπ
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : 2 * s₀ * (34 + 2 * w) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : 16384 * s₀ ^ 2 * w ≤ n := le_trans (le_max_right _ _) hn
  have h2s : 0 < 2 * s₀ := Nat.mul_pos (by norm_num) hs₀
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.mul_pos h2s (by omega)) hn1
  obtain ⟨G, hL, -, hE⟩ := hG n hn0
  obtain ⟨π', hπ', hlen⟩ := h47 (n + 1) n G π hπ
  -- the degree
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = n / (2 * s₀) := ⟨_, rfl⟩
  have hq1 : 34 + 2 * w ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le h2s]
    calc (34 + 2 * w) * (2 * s₀) = 2 * s₀ * (34 + 2 * w) := by ring
      _ ≤ n := hn1
  have hq2 : 2 * q ≤ n / s₀ := by
    rw [Nat.le_div_iff_mul_le hs₀]
    calc 2 * q * s₀ = 2 * s₀ * q := by ring
      _ ≤ n := by rw [hq]; exact Nat.mul_div_le n (2 * s₀)
  have hq3 : n < 2 * s₀ * (q + 1) := by
    rw [hq]; exact Nat.lt_mul_div_succ n h2s
  obtain ⟨D, hD⟩ : ∃ D : ℕ, q = D + 1 := ⟨q - 1, by omega⟩
  rw [hD] at hq1 hq2 hq3
  have hD32 : 32 ≤ D := by omega
  have hDw : 2 * w ≤ D := by omega
  have hnD : n ≤ 4 * s₀ * D := by
    have h : 2 * s₀ * 2 ≤ 2 * s₀ * D := Nat.mul_le_mul_left _ (by omega)
    have e1 : 2 * s₀ * (D + 1 + 1) = 2 * s₀ * D + 2 * s₀ * 2 := by ring
    have e2 : 4 * s₀ * D = 2 * s₀ * D + 2 * s₀ * D := by ring
    rw [e1] at hq3
    rw [e2]
    omega
  have hnr := h46 (n + 1) n G (n / s₀) D hE hq2
  -- the graph has an edge
  have hcard_pos : 0 < Fintype.card (GEdge G) := by
    have h := hE {0} (by rw [Finset.card_singleton]; exact le_trans (by omega) hq2)
    rw [Finset.card_singleton] at h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) h)
    unfold uniqueNbrs at hj
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj).2
    have hi' : i ∈ Finset.filter (fun i => j ∈ G i) {0} := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact Fintype.card_pos_iff.mpr ⟨⟨(i, j), (Finset.mem_filter.mp hi').2⟩⟩
  have hcard : Fintype.card (GEdge G) ≤ (n + 1) * w :=
    le_trans (card_gedge_le G b hL) (Nat.mul_le_mul_left _ hbw)
  have hsize := DegSizeAssembly.degree_to_size_256 (GEdge G) (graphPHP G) π' w D
    (fun C hC => hw ▸ graphPHP_width G b hL C hC) hDw hD32 hπ' hnr
  have harith := exp_arith s₀ w n D (Fintype.card (GEdge G)) hs₀ (by omega) hnpos hcard_pos
    hcard hnD
  -- absorb the factor two
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (16384 * (s₀ : ℝ) ^ 2 * w) * n := ⟨_, rfl⟩
  rw [← hy]
  have hy1 : 1 ≤ y := by
    rw [hy, one_div, inv_mul_eq_div, le_div_iff₀ hden, one_mul]
    exact_mod_cast hn2
  have hx : (n : ℝ) / (8192 * (s₀ : ℝ) ^ 2 * w) = y + y := by rw [hy]; ring
  have h2 : (2 : ℝ) ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have hchain : Real.exp y * Real.exp y ≤ 2 * (π.length : ℝ) := by
    rw [← Real.exp_add, ← hx]
    calc Real.exp ((n : ℝ) / (8192 * (s₀ : ℝ) ^ 2 * w))
        ≤ Real.exp (((D : ℝ) ^ 2) / (256 * (Fintype.card (GEdge G) : ℝ))) :=
          Real.exp_le_exp.mpr harith
      _ ≤ (π'.length : ℝ) := hsize
      _ ≤ 2 * (π.length : ℝ) := by exact_mod_cast hlen
  have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos y).le
  linarith

/-- The target of L-pcx-017 from the statements of L-pcx-046 and L-pcx-047: Res(⊕) refutations
of the pigeonhole formula are not polynomially bounded. -/
theorem php_not_poly (h46 : Stmt046) (h47 : Stmt047) :
    ∀ p : Polynomial ℕ, ∃ n : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin (n + 1) × Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π → p.eval n < π.length := by
  intro p
  obtain ⟨c, n₀, hc, hexp⟩ := php_exp h46 h47
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  have hcpow : (0 : ℝ) < c ^ (d + 1) := pow_pos hc _
  have hfact : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨k, hk⟩ := exists_nat_gt ((C : ℝ) * ((d + 1).factorial : ℝ) / c ^ (d + 1))
  obtain ⟨n, hn0, hnk, hn1⟩ : ∃ n : ℕ, n₀ ≤ n ∧ k ≤ n ∧ 1 ≤ n :=
    ⟨max (max n₀ k) 1, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  refine ⟨n, ?_⟩
  intro π hπ
  have h1 := hexp n hn0 π hπ
  have hpoly : ((p.eval n : ℕ) : ℝ) ≤ (C : ℝ) * (n : ℝ) ^ d := by
    have := Helpers.poly_eval_le_coeffSum_mul_pow p n hn1
    rw [← hC, ← hd] at this
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hkn : (C : ℝ) * ((d + 1).factorial : ℝ) / c ^ (d + 1) < n :=
    lt_of_lt_of_le hk (by exact_mod_cast hnk)
  rw [div_lt_iff₀ hcpow] at hkn
  have hfac := Real.pow_div_factorial_le_exp (x := c * n)
    (mul_nonneg hc.le hnR.le) (d + 1)
  have hlt : (C : ℝ) * (n : ℝ) ^ d < (c * n) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
    rw [lt_div_iff₀ hfact]
    calc (C : ℝ) * (n : ℝ) ^ d * ((d + 1).factorial : ℝ)
        = (C : ℝ) * ((d + 1).factorial : ℝ) * (n : ℝ) ^ d := by ring
      _ < (n : ℝ) * c ^ (d + 1) * (n : ℝ) ^ d :=
          mul_lt_mul_of_pos_right hkn (pow_pos hnR d)
      _ = (c * n) ^ (d + 1) := by ring
  have hfin : ((p.eval n : ℕ) : ℝ) < (π.length : ℝ) := by linarith
  exact_mod_cast hfin

end PEqualNP.ProofComplexity.PhpFinal
