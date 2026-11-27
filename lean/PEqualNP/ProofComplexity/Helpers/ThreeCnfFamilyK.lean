import PEqualNP.ProofComplexity.Helpers.ThreeCnfFamily
import PEqualNP.ProofComplexity.Helpers.LinKFinal

/-!
# Conditional assembly of L-pcx-060 (a 3-CNF family hard for Res(k, ⊕))

The degree `k` twin of `Helpers/ThreeCnfFamily.lean`. Two links enter as hypotheses:
`PhpFinal.Stmt046`, the statement of L-pcx-046, and `LinKFinal.StmtLinK`, the general degree to
size theorem for Res(k, ⊕).

* `backLine_refutation`: a Res(k, ⊕) refutation of a formula renamed along an equivalence of
  the variables pulls back, line by line, to one of the original formula of the same length;
* `to_fin_k`: a finite-variable 3-CNF formula renamed to the variables `Fin n`;
* `graph3_exp_k`: for every `k ≥ 1` and all large `N`, a 3-CNF formula on at most `A * N`
  variables whose Res(k, ⊕) refutations have at least `exp (c * N)` lines;
* `three_cnf_hard_k`: the target statement of L-pcx-060 from the two hypotheses.

With `b`, `s₀`, `n₀` the constants of L-pcx-043, `w = max b 2`, `K = 4 * s₀ * w` and
`A₀ = w + (1 + w * w) * (w + 1)`: the formula is `to3 (graphPHP G) w` for the expander `G` on
`N + 1` pigeons and `N` holes, the degree is `D = N / K`, the number of variables is at most
`2 * A₀ * N`, and `c = ρ ^ k / (32 k K)` with `ρ = 1 / (16 K A₀)`.
-/

namespace PEqualNP.ProofComplexity.ThreeCnfFamilyK

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers.ThreeCnf
open PEqualNP.ProofComplexity.ThreeCnfFamily

/-! ## Renaming the variables along an equivalence -/

section Rename

variable {V W : Type} [DecidableEq V] [DecidableEq W] (e : V ≃ W)

/-- A term over the new variables, pulled back to the old ones. -/
def backTerm (T : LinTerm W) : LinTerm V := T.image (back e)

/-- A line over the new variables, pulled back to the old ones. -/
def backLine (L : LinKLine W) : LinKLine V := L.image (backTerm e)

omit [DecidableEq W] in
theorem backTerm_injective : Function.Injective (backTerm e) :=
  Finset.image_injective (back_injective e)

omit [DecidableEq W] in
theorem backTerm_card (T : LinTerm W) : (backTerm e T).card = T.card :=
  Finset.card_image_of_injective _ (back_injective e)

omit [DecidableEq W] in
theorem backTerm_sat (a : V → Bool) (T : LinTerm W) :
    LinTermSat a (backTerm e T) ↔ LinTermSat (fun x => a (e.symm x)) T := by
  constructor
  · intro h q hq
    exact (back_sat e a q).mp (h _ (Finset.mem_image_of_mem _ hq))
  · intro h q' hq'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    exact (back_sat e a q).mpr (h q hq)

omit [DecidableEq W] in
theorem backTerm_singleton (q : LinEq W) : backTerm e {q} = {back e q} :=
  Finset.image_singleton _ _

omit [DecidableEq V] [DecidableEq W] in
theorem back_neg (q : LinEq W) : back e (negLinEq q) = negLinEq (back e q) := rfl

/-- Pulling back the line of a renamed clause gives the line of the original. -/
theorem backLine_ren (C : Clause V) : backLine e (linKOfClause (ren e C)) = linKOfClause C := by
  unfold backLine linKOfClause
  rw [← backLin_ren e C]
  unfold backLin
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr (fun q _ => ?_)
  exact backTerm_singleton e q

omit [DecidableEq W] in
theorem backLine_card {k : ℕ} {L : LinKLine W} (h : ∀ T ∈ L, T.card ≤ k) :
    ∀ T ∈ backLine e L, T.card ≤ k := by
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hT'
  rw [backTerm_card]
  exact h T hT

/-- A Res(k, ⊕) derivation from the renamed formula pulls back line by line. -/
theorem backLine_derivation (k : ℕ) (F : Set (Clause V)) {π : List (LinKLine W)}
    (h : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' (ren e '' F)) π) :
    IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F)
      (π.map (backLine e)) := by
  induction h with
  | nil => exact IsLinKDerivation.nil
  | @ax π L hπ hL hk ih =>
    obtain ⟨C', ⟨C, hC, rfl⟩, rfl⟩ := hL
    rw [List.map_cons]
    exact IsLinKDerivation.ax ih ⟨C, hC, (backLine_ren e C).symm⟩ (backLine_card e hk)
  | @cut π C D R hπ hC hD hR hk ih =>
    obtain ⟨T, hTC, hTD, rfl⟩ := hR
    rw [List.map_cons]
    refine IsLinKDerivation.cut ih (List.mem_map.mpr ⟨C, hC, rfl⟩)
      (List.mem_map.mpr ⟨D, hD, rfl⟩) ⟨backTerm e T, Finset.mem_image_of_mem _ hTC, ?_, ?_⟩
      (backLine_card e hk)
    · intro q' hq'
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
      rw [← back_neg, ← backTerm_singleton]
      exact Finset.mem_image_of_mem _ (hTD q hq)
    · unfold backLine
      rw [Finset.image_union, Finset.image_erase (backTerm_injective e),
        Finset.image_sdiff _ _ (backTerm_injective e)]
      congr 2
      unfold backTerm
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr (fun q _ => ?_)
      exact backTerm_singleton e (negLinEq q)
  | @andIntro π C D R hπ hC hD hR hk ih =>
    obtain ⟨T₁, T₂, h1, h2, rfl⟩ := hR
    rw [List.map_cons]
    refine IsLinKDerivation.andIntro ih (List.mem_map.mpr ⟨C, hC, rfl⟩)
      (List.mem_map.mpr ⟨D, hD, rfl⟩)
      ⟨backTerm e T₁, backTerm e T₂, Finset.mem_image_of_mem _ h1,
        Finset.mem_image_of_mem _ h2, ?_⟩ (backLine_card e hk)
    unfold backLine
    rw [Finset.image_union, Finset.image_union, Finset.image_erase (backTerm_injective e),
      Finset.image_erase (backTerm_injective e), Finset.image_singleton]
    congr 2
    exact Finset.image_union _ _
  | @weak π C D hπ hC hw hk ih =>
    rw [List.map_cons]
    refine IsLinKDerivation.weak ih (List.mem_map.mpr ⟨C, hC, rfl⟩) ?_ (backLine_card e hk)
    intro T' hT'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hT'
    rcases hw T hT with ⟨S, hS, himp⟩ | himp
    · refine Or.inl ⟨backTerm e S, Finset.mem_image_of_mem _ hS, fun a ha => ?_⟩
      rw [backTerm_sat] at ha ⊢
      exact himp _ ha
    · refine Or.inr (fun a ha => ?_)
      rw [backTerm_sat] at ha
      obtain ⟨q, hq, hs⟩ := himp _ ha
      refine ⟨back e q, ?_, (back_sat e a q).mpr hs⟩
      rw [← backTerm_singleton]
      exact Finset.mem_image_of_mem _ hq

/-- A Res(k, ⊕) refutation of the renamed formula pulls back to one of the original formula,
of the same length. -/
theorem backLine_refutation (k : ℕ) (F : Set (Clause V)) (π : List (LinKLine W))
    (h : IsLinKRefutation k (ren e '' F) π) :
    IsLinKRefutation k F (π.map (backLine e)) :=
  ⟨backLine_derivation e k F h.1, List.mem_map.mpr ⟨∅, h.2, Finset.image_empty _⟩⟩

end Rename

/-- A 3-CNF formula on a finite type of variables, renamed to the variables `Fin n` with `n`
the number of variables, as a finite set of clauses: still a 3-CNF formula, unsatisfiable if
the original is, and each of its Res(k, ⊕) refutations gives one of the original of the same
length. -/
theorem to_fin_k {V : Type} [Fintype V] [DecidableEq V] (k : ℕ) (F : Set (Clause V))
    (hw : ∀ C ∈ F, C.card ≤ 3) (hun : ¬ Satisfiable F) :
    ∃ F' : Finset (Clause (Fin (Fintype.card V))), (∀ C ∈ F', C.card ≤ 3) ∧
      ¬ Satisfiable (↑F' : Set (Clause (Fin (Fintype.card V)))) ∧
      ∀ π : List (LinKLine (Fin (Fintype.card V))),
        IsLinKRefutation k (↑F' : Set (Clause (Fin (Fintype.card V)))) π →
        ∃ π' : List (LinKLine V), IsLinKRefutation k F π' ∧ π'.length = π.length := by
  have hfin : (ren (Fintype.equivFin V) '' F).Finite := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨C0, hC0, rfl⟩ := hfin.mem_toFinset.mp hC
    exact le_trans Finset.card_image_le (hw C0 hC0)
  · rw [Set.Finite.coe_toFinset]
    exact ren_unsat _ F hun
  · intro π hπ
    rw [Set.Finite.coe_toFinset] at hπ
    exact ⟨π.map (backLine (Fintype.equivFin V)), backLine_refutation _ k F π hπ,
      List.length_map _⟩

/-! ## The arithmetic -/

/-- The arithmetic of the exponent: with at most `2 * A₀ * N` variables and degree at least
`N / (2 * K)`, the exponent of the general theorem is linear in `N`. -/
theorem exp_arith_k (k K A₀ N D card : ℕ) (hk : 1 ≤ k) (hK : 0 < K) (hA : 0 < A₀)
    (hcard_pos : 0 < card) (hcard : card ≤ 2 * A₀ * N) (hND : N ≤ 2 * K * D) :
    (1 / (16 * (K : ℝ) * A₀)) ^ k / (32 * (k : ℝ) * K) * N ≤
      (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hAR : (0 : ℝ) < A₀ := by exact_mod_cast hA
  have hcR : (0 : ℝ) < card := by exact_mod_cast hcard_pos
  have hDR : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hND' : (N : ℝ) ≤ 2 * K * D := by exact_mod_cast hND
  have hcard' : (card : ℝ) ≤ 2 * A₀ * N := by exact_mod_cast hcard
  set ρ : ℝ := 1 / (16 * (K : ℝ) * A₀) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have h1 : (N : ℝ) / (32 * (k : ℝ) * K) ≤ (D : ℝ) / (16 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hND' (by positivity : (0 : ℝ) ≤ 16 * (k : ℝ))]
  have h2 : ρ ≤ (D : ℝ) / (4 * (card : ℝ)) := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h8 : 4 * (card : ℝ) ≤ 8 * A₀ * N := by linarith
    have h9 : 8 * (A₀ : ℝ) * N ≤ 8 * A₀ * (2 * K * D) :=
      mul_le_mul_of_nonneg_left hND' (by positivity)
    calc 4 * (card : ℝ) ≤ 8 * A₀ * N := h8
      _ ≤ 8 * A₀ * (2 * K * D) := h9
      _ = (D : ℝ) * (16 * (K : ℝ) * A₀) := by ring
  have h3 : ρ ^ k ≤ ((D : ℝ) / (4 * (card : ℝ))) ^ k := pow_le_pow_left₀ hρ0 h2 k
  calc ρ ^ k / (32 * (k : ℝ) * K) * N = (N : ℝ) / (32 * (k : ℝ) * K) * ρ ^ k := by ring
    _ ≤ (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k :=
        mul_le_mul h1 h3 (pow_nonneg hρ0 k) (by positivity)

/-! ## The family -/

/-- From the statement of L-pcx-046 and the general theorem for Res(k, ⊕): for every `k ≥ 1`
and all large `N` there is an unsatisfiable 3-CNF formula on at most `A * N` variables whose
Res(k, ⊕) refutations have at least `exp (c * N)` lines. -/
theorem graph3_exp_k (h46 : PhpFinal.Stmt046) (hL : LinKFinal.StmtLinK) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (c : ℝ) (A n₀ : ℕ), 0 < c ∧ 0 < A ∧ ∀ N ≥ n₀, 1 ≤ N ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (F : Set (Clause V)),
        (∀ C ∈ F, C.card ≤ 3) ∧ ¬ Satisfiable F ∧ Fintype.card V ≤ A * N ∧
        ∀ π : List (LinKLine V), IsLinKRefutation k F π →
          Real.exp (c * (N : ℝ)) ≤ (π.length : ℝ) := by
  classical
  obtain ⟨b, s₀, n₀, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = max b 2 := ⟨_, rfl⟩
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 4 * s₀ * w := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hs₀) (by omega)
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℕ, A₀ = w + (1 + w * w) * (w + 1) := ⟨_, rfl⟩
  have hApos : 0 < A₀ := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hAR : (0 : ℝ) < A₀ := by exact_mod_cast hApos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨(1 / (16 * (K : ℝ) * A₀)) ^ k / (32 * (k : ℝ) * K), 2 * A₀,
    max (max n₀ ((16 * k + 12) * K)) (2 * ((4 * w + 2) * s₀)), by positivity, by omega, ?_⟩
  intro N hN
  have hn0 : n₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn1 : (16 * k + 12) * K ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hn2 : 2 * ((4 * w + 2) * s₀) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.mul_pos (by omega) hKpos) hn1
  refine ⟨hNpos, ?_⟩
  obtain ⟨G, hLd, hR, hE⟩ := hG N hn0
  -- the degree
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = N / K := ⟨_, rfl⟩
  have hDk : 16 * k + 12 ≤ D := by
    rw [hD, Nat.le_div_iff_mul_le hKpos]
    exact hn1
  have hDK : D * K ≤ N := by
    rw [hD]
    exact Nat.div_mul_le_self N K
  have hND : N ≤ 2 * K * D := by
    have h1 : N < K * (D + 1) := by
      rw [hD]
      exact Nat.lt_mul_div_succ N hKpos
    have h2 : K ≤ K * D := Nat.le_mul_of_pos_right K (by omega)
    have e1 : K * (D + 1) = K * D + K := by ring
    have e2 : 2 * K * D = K * D + K * D := by ring
    rw [e1] at h1
    rw [e2]
    omega
  have hdeg : 2 * (w * D + 2 * w + 1) ≤ N / s₀ := by
    rw [Nat.le_div_iff_mul_le hs₀]
    have h1 : 4 * (s₀ * w * D) ≤ N := by
      calc 4 * (s₀ * w * D) = D * K := by rw [hK]; ring
        _ ≤ N := hDK
    have e : 2 * (w * D + 2 * w + 1) * s₀ = 2 * (s₀ * w * D) + (4 * w + 2) * s₀ := by ring
    rw [e]
    omega
  have hnr := h46 (N + 1) N G (N / s₀) (w * D + 2 * w) hE hdeg
  have hwid : ∀ C ∈ graphPHP G, C.card ≤ w :=
    fun C hC => hw ▸ PhpFinal.graphPHP_width G b hLd C hC
  have hnr3 : ¬ PCRefutable (cnfSystem (to3 (graphPHP G) w)) D :=
    to3_pc_lower (graphPHP G) w D (by omega) hwid hnr
  have instF : Fintype ↥(graphPHP G) := Fintype.ofFinite _
  have hcard : Fintype.card (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))) ≤ 2 * A₀ * N := by
    have hcE : Fintype.card (GEdge G) ≤ (N + 1) * w :=
      le_trans (PhpFinal.card_gedge_le G b hLd) (Nat.mul_le_mul_left _ hbw)
    have hcF : Fintype.card ↥(graphPHP G) ≤ (N + 1) * (1 + w * w) := by
      calc Fintype.card ↥(graphPHP G) ≤ (N + 1) + (N + 1) * b * b :=
            card_graphPHP_le G b hLd hR
        _ ≤ (N + 1) + (N + 1) * w * w :=
          Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ hbw) hbw) _
        _ = (N + 1) * (1 + w * w) := by ring
    calc Fintype.card (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1)))
        = Fintype.card (GEdge G) + Fintype.card ↥(graphPHP G) * (w + 1) :=
          to3_card (graphPHP G) w
      _ ≤ (N + 1) * w + (N + 1) * (1 + w * w) * (w + 1) :=
          Nat.add_le_add hcE (Nat.mul_le_mul_right _ hcF)
      _ = (N + 1) * A₀ := by rw [hA₀]; ring
      _ ≤ (2 * N) * A₀ := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * A₀ * N := by ring
  refine ⟨GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1)), inferInstance, inferInstance,
    to3 (graphPHP G) w, to3_width _ _,
    to3_unsat _ _ (graphPHP_unsat G (Nat.lt_succ_self N)), hcard, ?_⟩
  intro π hπ
  have hcard_pos : 0 < Fintype.card (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))) :=
    Fintype.card_pos_iff.mpr
      ⟨Sum.inr (⟨_, (Or.inl ⟨(0 : Fin (N + 1)), rfl⟩ : _ ∈ graphPHP G)⟩, (0 : Fin (w + 1)))⟩
  have hsize := hL (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))) (to3 (graphPHP G) w) π k 3 D
    (to3_width _ _) hk (by omega) (by omega) hnr3 hπ
  have harith := exp_arith_k k K A₀ N D _ hk hKpos hApos hcard_pos hcard hND
  exact le_trans (Real.exp_le_exp.mpr harith) hsize

/-- The target of L-pcx-060 from the statement of L-pcx-046 and the general theorem for
Res(k, ⊕): for every `k ≥ 1` and polynomial `p` some unsatisfiable 3-CNF formula on `n`
variables has only Res(k, ⊕) refutations longer than `p n`. -/
theorem three_cnf_hard_k (h46 : PhpFinal.Stmt046) (hL : LinKFinal.StmtLinK) :
    ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) ∧ ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (Fin n)), PEqualNP.ProofComplexity.IsLinKRefutation k (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → p.eval n < π.length := by
  intro k hk p
  obtain ⟨c, A, n₀, hc, hA, hmain⟩ := graph3_exp_k h46 hL k hk
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, CA = (C : ℝ) * (A : ℝ) ^ d := ⟨_, rfl⟩
  have hcpow : (0 : ℝ) < c ^ (d + 1) := pow_pos hc _
  have hfact : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨M, hM⟩ := exists_nat_gt (CA * ((d + 1).factorial : ℝ) / c ^ (d + 1))
  obtain ⟨N, hN0, hNM⟩ : ∃ N : ℕ, n₀ ≤ N ∧ M ≤ N := ⟨max n₀ M, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨hN1, V, instV, instD, F, hw, hun, hcard, hlen⟩ := hmain N hN0
  obtain ⟨F', h1, h2, h3⟩ := to_fin_k k F hw hun
  refine ⟨Fintype.card V, F', h1, h2, ?_⟩
  intro π hπ
  obtain ⟨π', hπ', hl⟩ := h3 π hπ
  have hexp := hlen π' hπ'
  rw [hl] at hexp
  have hAN : 1 ≤ A * N := Nat.mul_pos hA hN1
  have hpoly : ((p.eval (Fintype.card V) : ℕ) : ℝ) ≤ CA * (N : ℝ) ^ d := by
    have hnat : p.eval (Fintype.card V) ≤ C * (A * N) ^ d := by
      have := Helpers.poly_eval_le_coeffSum_mul_pow p (A * N) hAN
      rw [← hC, ← hd] at this
      exact le_trans (eval_mono p hcard) this
    have hR : ((p.eval (Fintype.card V) : ℕ) : ℝ) ≤ (C : ℝ) * ((A : ℝ) * (N : ℝ)) ^ d := by
      exact_mod_cast hnat
    rw [hCA]
    calc ((p.eval (Fintype.card V) : ℕ) : ℝ) ≤ (C : ℝ) * ((A : ℝ) * (N : ℝ)) ^ d := hR
      _ = (C : ℝ) * (A : ℝ) ^ d * (N : ℝ) ^ d := by ring
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hkn : CA * ((d + 1).factorial : ℝ) / c ^ (d + 1) < N :=
    lt_of_lt_of_le hM (by exact_mod_cast hNM)
  rw [div_lt_iff₀ hcpow] at hkn
  have hfac := Real.pow_div_factorial_le_exp (x := c * N)
    (mul_nonneg hc.le hNR.le) (d + 1)
  have hlt : CA * (N : ℝ) ^ d < (c * N) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
    rw [lt_div_iff₀ hfact]
    calc CA * (N : ℝ) ^ d * ((d + 1).factorial : ℝ)
        = CA * ((d + 1).factorial : ℝ) * (N : ℝ) ^ d := by ring
      _ < (N : ℝ) * c ^ (d + 1) * (N : ℝ) ^ d :=
          mul_lt_mul_of_pos_right hkn (pow_pos hNR d)
      _ = (c * N) ^ (d + 1) := by ring
  have hfin : ((p.eval (Fintype.card V) : ℕ) : ℝ) < (π.length : ℝ) := by linarith
  exact_mod_cast hfin

end PEqualNP.ProofComplexity.ThreeCnfFamilyK
