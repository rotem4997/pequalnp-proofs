import PEqualNP.ProofComplexity.Helpers.PhpFinal
import PEqualNP.ProofComplexity.Helpers.ThreeCnf

/-!
# Conditional assembly of L-pcx-048 (a 3-CNF family hard for Res(⊕))

One link of the chain enters as a hypothesis: `PhpFinal.Stmt046`, the statement of L-pcx-046
(the pigeonhole formula on a boundary expander has no polynomial calculus refutation of low
degree). From it, the expanders of L-pcx-043, the 3-CNF conversion of `Helpers/ThreeCnf.lean`
and the degree to size theorem of L-pcx-042:

* `graphPHP_unsat`: the pigeonhole formula on a graph with more pigeons than holes is
  unsatisfiable;
* `card_graphPHP_le`: with left and right degrees at most `b`, it has at most `m + m * b * b`
  clauses;
* `back_refutation`: a Res(⊕) refutation of a formula renamed along an equivalence of the
  variables pulls back, line by line, to one of the original formula of the same length;
* `to_fin`: a finite-variable 3-CNF formula renamed to the variables `Fin n`, as a `Finset`;
* `graph3_exp`: for all large `N`, a 3-CNF formula on at most `A * N` variables whose Res(⊕)
  refutations have at least `exp (c * N)` lines;
* `three_cnf_hard`: the target statement of L-pcx-048 from `Stmt046`.

With `b`, `s₀`, `n₀` the constants of L-pcx-043, `w = max b 2`, `K = 4 * s₀ * w` and
`A₀ = w + (1 + w * w) * (w + 1)`: the formula is `to3 (graphPHP G) w` for the expander `G` on
`N + 1` pigeons and `N` holes, the degree is `D = N / K`, the number of variables is at most
`2 * A₀ * N`, and `c = 1 / (2048 * K ^ 2 * A₀)`.
-/

namespace PEqualNP.ProofComplexity.ThreeCnfFamily

open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.ProofComplexity.Helpers.ThreeCnf

/-! ## The pigeonhole formula on a graph -/

/-- With more pigeons than holes, the pigeonhole formula on a graph is unsatisfiable. -/
theorem graphPHP_unsat {m N : ℕ} (G : BipGraph m N) (h : N < m) :
    ¬ Satisfiable (graphPHP G) := by
  classical
  rintro ⟨a, ha⟩
  have hp : ∀ i : Fin m, ∃ e : GEdge G, e.1.1 = i ∧ a e = true := by
    intro i
    obtain ⟨l, hl, hal⟩ := ha _ (Or.inl ⟨i, rfl⟩)
    have h2 := (Finset.mem_filter.mp hl).2
    exact ⟨l.1, h2.1, by rw [hal, h2.2]⟩
  choose g hg1 hg2 using hp
  obtain ⟨i, i', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => (g i).1.2)
    (by simpa using h)
  obtain ⟨l, hl, hal⟩ := ha _ (Or.inr ⟨g i, g i', heq, by rw [hg1, hg1]; exact hne, rfl⟩)
  rcases Finset.mem_insert.mp hl with rfl | hl
  · simp [hg2] at hal
  · rw [Finset.mem_singleton] at hl
    subst hl
    simp [hg2] at hal

/-- With right degree at most `b`, there are at most `b` times the number of edges many pairs
of edges into the same hole. -/
theorem card_pairs_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hR : RightDegLe G b) :
    ((Finset.univ : Finset (GEdge G × GEdge G)).filter (fun p => p.1.1.2 = p.2.1.2)).card
      ≤ Fintype.card (GEdge G) * b := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ e ∈ (Finset.univ : Finset (GEdge G)),
      (((Finset.univ : Finset (GEdge G × GEdge G)).filter
        (fun p => p.1.1.2 = p.2.1.2)).filter (fun p => p.1 = e)).card ≤ b := by
    intro e _
    refine le_trans (Finset.card_le_card_of_injOn (t := rightNbrs G e.1.2)
      (fun p : GEdge G × GEdge G => p.2.1.1) ?_ ?_) (hR e.1.2)
    · intro p hp
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have h1 := (Finset.mem_filter.mp hp'.1).2
      have h2 : p.2.1.2 ∈ G p.2.1.1 := p.2.2
      rw [← h1, hp'.2] at h2
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
    · intro p hp p' hp' h
      have hq := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
      have h1 := (Finset.mem_filter.mp hq.1).2
      have h1' := (Finset.mem_filter.mp hq'.1).2
      have e1 : p.1 = p'.1 := hq.2.trans hq'.2.symm
      have e2 : p.2.1.2 = p'.2.1.2 := by rw [← h1, ← h1', e1]
      exact Prod.ext e1 (Subtype.ext (Prod.ext h e2))
  calc _ ≤ ∑ _e : GEdge G, b := Finset.sum_le_sum hfib
    _ = Fintype.card (GEdge G) * b := by simp

/-- With left and right degrees at most `b`, the pigeonhole formula on a graph has at most
`m + m * b * b` clauses. -/
theorem card_graphPHP_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hL : LeftDegLe G b)
    (hR : RightDegLe G b) [Fintype ↥(graphPHP G)] :
    Fintype.card ↥(graphPHP G) ≤ m + m * b * b := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (GEdge G × GEdge G),
      S = Finset.univ.filter (fun p => p.1.1.2 = p.2.1.2) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Clause (GEdge G)),
      T = (Finset.univ : Finset (Fin m)).image
          (fun i => Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true))
        ∪ S.image (fun p => {(p.1, false), (p.2, false)}) := ⟨_, rfl⟩
  have hsub : ∀ C, C ∈ graphPHP G → C ∈ T := by
    rintro C (⟨i, rfl⟩ | ⟨e, e', h, -, rfl⟩)
    · rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · rw [hT]
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, e'), ?_, rfl⟩)
      rw [hS]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hinj : Function.Injective
      (fun x : ↥(graphPHP G) => (⟨x.1, hsub x.1 x.2⟩ : {C // C ∈ T})) :=
    fun x y h => Subtype.ext (congrArg (fun z : {C // C ∈ T} => z.1) h)
  have hSc : S.card ≤ m * b * b := by
    rw [hS]
    exact le_trans (card_pairs_le G b hR)
      (Nat.mul_le_mul_right _ (PhpFinal.card_gedge_le G b hL))
  have hTc : T.card ≤ m + S.card := by
    rw [hT]
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ Finset.card_image_le)
    refine le_trans Finset.card_image_le ?_
    simp
  calc Fintype.card ↥(graphPHP G) ≤ Fintype.card {C // C ∈ T} :=
        Fintype.card_le_of_injective _ hinj
    _ = T.card := Fintype.card_coe T
    _ ≤ m + S.card := hTc
    _ ≤ m + m * b * b := Nat.add_le_add_left hSc _

/-! ## Renaming the variables along an equivalence -/

section Rename

variable {V W : Type} [DecidableEq V] [DecidableEq W] (e : V ≃ W)

/-- A clause with its variables renamed. -/
def ren (C : Clause V) : Clause W := C.image (fun l => (e l.1, l.2))

/-- A linear equation over the new variables, pulled back to the old ones. -/
def back (q : LinEq W) : LinEq V := (q.1.map e.symm.toEmbedding, q.2)

/-- A linear clause over the new variables, pulled back to the old ones. -/
def backLin (L : LinClause W) : LinClause V := L.image (back e)

omit [DecidableEq V] [DecidableEq W] in
theorem back_injective : Function.Injective (back e) := by
  intro q q' h
  have h' : (q.1.map e.symm.toEmbedding, q.2) = (q'.1.map e.symm.toEmbedding, q'.2) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  exact Prod.ext (Finset.map_injective _ h1) h2

omit [DecidableEq V] [DecidableEq W] in
theorem back_sat (a : V → Bool) (q : LinEq W) :
    LinEqSat a (back e q) ↔ LinEqSat (fun x => a (e.symm x)) q := by
  have hmap : (q.1.map e.symm.toEmbedding).filter (fun v => a v = true)
      = (q.1.filter (fun x => a (e.symm x) = true)).map e.symm.toEmbedding := by
    ext v
    constructor
    · intro hv
      obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv1
      exact Finset.mem_map.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hv2⟩, rfl⟩
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨x, hx1, rfl⟩, hx2⟩
  unfold LinEqSat back
  dsimp only
  rw [hmap, Finset.card_map]

omit [DecidableEq W] in
theorem backLin_sat (a : V → Bool) (L : LinClause W) :
    LinClauseSat a (backLin e L) ↔ LinClauseSat (fun x => a (e.symm x)) L := by
  constructor
  · rintro ⟨q', hq', hs⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    exact ⟨q, hq, (back_sat e a q).mp hs⟩
  · rintro ⟨q, hq, hs⟩
    exact ⟨back e q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, (back_sat e a q).mpr hs⟩

/-- Pulling back the linear clause of a renamed clause gives the linear clause of the
original. -/
theorem backLin_ren (C : Clause V) : backLin e (linOfClause (ren e C)) = linOfClause C := by
  unfold backLin linOfClause ren
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr (fun l _ => ?_)
  simp [back, Function.comp]

/-- A Res(⊕) derivation from the renamed formula pulls back line by line. -/
theorem back_derivation (F : Set (Clause V)) {π : List (LinClause W)}
    (h : IsLinDerivation ((fun C => linOfClause C) '' (ren e '' F)) π) :
    IsLinDerivation ((fun C => linOfClause C) '' F) (π.map (backLin e)) := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | @ax π L hπ hL ih =>
    obtain ⟨C', ⟨C, hC, rfl⟩, rfl⟩ := hL
    rw [List.map_cons]
    exact IsLinDerivation.ax ih ⟨C, hC, (backLin_ren e C).symm⟩
  | @res π C D R hπ hC hD hR ih =>
    obtain ⟨f, hfC, hfD, rfl⟩ := hR
    rw [List.map_cons]
    have h0 : back e (f, false) ∈ backLin e C := Finset.mem_image_of_mem _ hfC
    have h1 : back e (f, true) ∈ backLin e D := Finset.mem_image_of_mem _ hfD
    refine IsLinDerivation.res ih (List.mem_map.mpr ⟨C, hC, rfl⟩)
      (List.mem_map.mpr ⟨D, hD, rfl⟩) ⟨f.map e.symm.toEmbedding, h0, h1, ?_⟩
    unfold backLin
    rw [Finset.image_union, Finset.image_erase (back_injective e),
      Finset.image_erase (back_injective e)]
    rfl
  | @weak π C D hπ hC hw ih =>
    rw [List.map_cons]
    refine IsLinDerivation.weak ih (List.mem_map.mpr ⟨C, hC, rfl⟩) (fun a ha => ?_)
    rw [backLin_sat] at ha ⊢
    exact hw _ ha

/-- A Res(⊕) refutation of the renamed formula pulls back to one of the original formula, of
the same length. -/
theorem back_refutation (F : Set (Clause V)) (π : List (LinClause W))
    (h : IsLinRefutation (ren e '' F) π) :
    IsLinRefutation F (π.map (backLin e)) :=
  ⟨back_derivation e F h.1, List.mem_map.mpr ⟨∅, h.2, Finset.image_empty _⟩⟩

omit [DecidableEq V] in
/-- If the original formula is unsatisfiable, so is the renamed one. -/
theorem ren_unsat (F : Set (Clause V)) (h : ¬ Satisfiable F) : ¬ Satisfiable (ren e '' F) := by
  rintro ⟨a, ha⟩
  refine h ⟨fun v => a (e v), fun C hC => ?_⟩
  obtain ⟨l', hl', hal⟩ := ha _ ⟨C, hC, rfl⟩
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hl'
  exact ⟨l, hl, hal⟩

end Rename

/-- A 3-CNF formula on a finite type of variables, renamed to the variables `Fin n` with `n`
the number of variables, as a finite set of clauses: still a 3-CNF formula, unsatisfiable if
the original is, and each of its Res(⊕) refutations gives one of the original of the same
length. -/
theorem to_fin {V : Type} [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (hw : ∀ C ∈ F, C.card ≤ 3) (hun : ¬ Satisfiable F) :
    ∃ F' : Finset (Clause (Fin (Fintype.card V))), (∀ C ∈ F', C.card ≤ 3) ∧
      ¬ Satisfiable (↑F' : Set (Clause (Fin (Fintype.card V)))) ∧
      ∀ π : List (LinClause (Fin (Fintype.card V))),
        IsLinRefutation (↑F' : Set (Clause (Fin (Fintype.card V)))) π →
        ∃ π' : List (LinClause V), IsLinRefutation F π' ∧ π'.length = π.length := by
  have hfin : (ren (Fintype.equivFin V) '' F).Finite := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨C0, hC0, rfl⟩ := hfin.mem_toFinset.mp hC
    exact le_trans Finset.card_image_le (hw C0 hC0)
  · rw [Set.Finite.coe_toFinset]
    exact ren_unsat _ F hun
  · intro π hπ
    rw [Set.Finite.coe_toFinset] at hπ
    exact ⟨π.map (backLin (Fintype.equivFin V)), back_refutation _ F π hπ, List.length_map _⟩

/-! ## The arithmetic -/

/-- A polynomial with natural coefficients is monotone. -/
theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

/-- The arithmetic of the exponent: with at most `2 * A₀ * N` variables and degree at least
`N / (2 * K)`, the exponent of the degree to size theorem is linear in `N`. -/
theorem exp_arith3 (K A₀ N D card : ℕ) (hK : 0 < K) (hA : 0 < A₀) (hN : 0 < N)
    (hcard_pos : 0 < card) (hcard : card ≤ 2 * A₀ * N) (hND : N ≤ 2 * K * D) :
    (N : ℝ) / (2048 * (K : ℝ) ^ 2 * A₀) ≤ ((D : ℝ) ^ 2) / (256 * (card : ℝ)) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hAR : (0 : ℝ) < A₀ := by exact_mod_cast hA
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcR : (0 : ℝ) < card := by exact_mod_cast hcard_pos
  have h1 : (card : ℝ) ≤ 2 * A₀ * N := by exact_mod_cast hcard
  have h2 : (N : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 2 * (D : ℝ) ^ 2 := by
    have h : (N : ℝ) ≤ 2 * K * D := by exact_mod_cast hND
    have := pow_le_pow_left₀ hNR.le h 2
    calc (N : ℝ) ^ 2 ≤ (2 * K * D) ^ 2 := this
      _ = 4 * (K : ℝ) ^ 2 * (D : ℝ) ^ 2 := by ring
  have hden1 : (0 : ℝ) < 2048 * (K : ℝ) ^ 2 * A₀ :=
    mul_pos (mul_pos (by norm_num) (pow_pos hKR 2)) hAR
  have hden2 : (0 : ℝ) < 256 * (card : ℝ) := mul_pos (by norm_num) hcR
  rw [div_le_div_iff₀ hden1 hden2]
  have h512 : (0 : ℝ) ≤ 512 * A₀ := by linarith
  calc (N : ℝ) * (256 * (card : ℝ)) ≤ (N : ℝ) * (256 * (2 * A₀ * N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) hNR.le
    _ = 512 * A₀ * (N : ℝ) ^ 2 := by ring
    _ ≤ 512 * A₀ * (4 * (K : ℝ) ^ 2 * (D : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h2 h512
    _ = (D : ℝ) ^ 2 * (2048 * (K : ℝ) ^ 2 * A₀) := by ring

/-! ## The family -/

/-- From the statement of L-pcx-046: for all large `N` there is an unsatisfiable 3-CNF formula
on at most `A * N` variables whose Res(⊕) refutations have at least `exp (c * N)` lines. -/
theorem graph3_exp (h46 : PhpFinal.Stmt046) :
    ∃ (c : ℝ) (A n₀ : ℕ), 0 < c ∧ 0 < A ∧ ∀ N ≥ n₀, 1 ≤ N ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (F : Set (Clause V)),
        (∀ C ∈ F, C.card ≤ 3) ∧ ¬ Satisfiable F ∧ Fintype.card V ≤ A * N ∧
        ∀ π : List (LinClause V), IsLinRefutation F π →
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
  have hden : (0 : ℝ) < 2048 * (K : ℝ) ^ 2 * A₀ :=
    mul_pos (mul_pos (by norm_num) (pow_pos hKR 2)) hAR
  refine ⟨1 / (2048 * (K : ℝ) ^ 2 * A₀), 2 * A₀,
    max (max n₀ (32 * K)) (2 * ((4 * w + 2) * s₀)), div_pos one_pos hden, by omega, ?_⟩
  intro N hN
  have hn0 : n₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn1 : 32 * K ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hn2 : 2 * ((4 * w + 2) * s₀) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := by omega
  refine ⟨hNpos, ?_⟩
  obtain ⟨G, hL, hR, hE⟩ := hG N hn0
  -- the degree
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = N / K := ⟨_, rfl⟩
  have hD32 : 32 ≤ D := by
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
  have hwid : ∀ C ∈ graphPHP G, C.card ≤ w := fun C hC => hw ▸ PhpFinal.graphPHP_width G b hL C hC
  have hnr3 : ¬ PCRefutable (cnfSystem (to3 (graphPHP G) w)) D :=
    to3_pc_lower (graphPHP G) w D (by omega) hwid hnr
  have instF : Fintype ↥(graphPHP G) := Fintype.ofFinite _
  refine ⟨GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1)), inferInstance, inferInstance,
    to3 (graphPHP G) w, to3_width _ _,
    to3_unsat _ _ (graphPHP_unsat G (Nat.lt_succ_self N)), ?_, ?_⟩
  · -- the number of variables
    have hcE : Fintype.card (GEdge G) ≤ (N + 1) * w :=
      le_trans (PhpFinal.card_gedge_le G b hL) (Nat.mul_le_mul_left _ hbw)
    have hcF : Fintype.card ↥(graphPHP G) ≤ (N + 1) * (1 + w * w) := by
      calc Fintype.card ↥(graphPHP G) ≤ (N + 1) + (N + 1) * b * b := card_graphPHP_le G b hL hR
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
  · intro π hπ
    have hcard : Fintype.card (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))) ≤ 2 * A₀ * N := by
      have hcE : Fintype.card (GEdge G) ≤ (N + 1) * w :=
        le_trans (PhpFinal.card_gedge_le G b hL) (Nat.mul_le_mul_left _ hbw)
      have hcF : Fintype.card ↥(graphPHP G) ≤ (N + 1) * (1 + w * w) := by
        calc Fintype.card ↥(graphPHP G) ≤ (N + 1) + (N + 1) * b * b :=
              card_graphPHP_le G b hL hR
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
    have hcard_pos : 0 < Fintype.card (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))) :=
      Fintype.card_pos_iff.mpr
        ⟨Sum.inr (⟨_, (Or.inl ⟨(0 : Fin (N + 1)), rfl⟩ : _ ∈ graphPHP G)⟩, (0 : Fin (w + 1)))⟩
    have hsize := DegSizeAssembly.degree_to_size_256
      (GEdge G ⊕ (↥(graphPHP G) × Fin (w + 1))) (to3 (graphPHP G) w) π 3 D
      (to3_width _ _) (by omega) hD32 hπ hnr3
    have harith := exp_arith3 K A₀ N D _ hKpos hApos hNpos hcard_pos hcard hND
    have he : 1 / (2048 * (K : ℝ) ^ 2 * A₀) * (N : ℝ) = (N : ℝ) / (2048 * (K : ℝ) ^ 2 * A₀) := by
      ring
    rw [he]
    exact le_trans (Real.exp_le_exp.mpr harith) hsize

/-- The target of L-pcx-048 from the statement of L-pcx-046: for every polynomial `p` some
unsatisfiable 3-CNF formula on `n` variables has only Res(⊕) refutations longer than `p n`. -/
theorem three_cnf_hard (h46 : PhpFinal.Stmt046) :
    ∀ p : Polynomial ℕ, ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) ∧ ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → p.eval n < π.length := by
  intro p
  obtain ⟨c, A, n₀, hc, hA, hmain⟩ := graph3_exp h46
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, CA = (C : ℝ) * (A : ℝ) ^ d := ⟨_, rfl⟩
  have hcpow : (0 : ℝ) < c ^ (d + 1) := pow_pos hc _
  have hfact : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  obtain ⟨k, hk⟩ := exists_nat_gt (CA * ((d + 1).factorial : ℝ) / c ^ (d + 1))
  obtain ⟨N, hN0, hNk⟩ : ∃ N : ℕ, n₀ ≤ N ∧ k ≤ N := ⟨max n₀ k, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨hN1, V, instV, instD, F, hw, hun, hcard, hlen⟩ := hmain N hN0
  obtain ⟨F', h1, h2, h3⟩ := to_fin F hw hun
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
    lt_of_lt_of_le hk (by exact_mod_cast hNk)
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

end PEqualNP.ProofComplexity.ThreeCnfFamily
