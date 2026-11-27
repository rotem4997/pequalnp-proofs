import PEqualNP.Defs.ProofComplexityGeneral
import PEqualNP.ProofComplexity.Helpers.ChainC2
import PEqualNP.ProofComplexity.Helpers.ChainD

/-!
# Helpers: the general criterion linking Res(⊕) length to polynomial calculus degree

The chain checked for bit pigeonhole, restated for an arbitrary CNF formula `F` of width at
most `w` on finitely many variables.

* `block_ax_cnf`: the axiom rule of the line simulation for `cnfSystem F`. The block of the
  linear clause of a clause `A` has the affine forms of the literals of `A` as inputs, and the
  polynomial of `A` is the product of `1 + (affine form)` over the literals, so telescoping
  over the literals and one multiple of the clause axiom give the block product.
* `chainC_cnf`: a Res(⊕) refutation `π` of `F` gives a polynomial calculus refutation of
  `cnfSystem F` extended by `π.length` blocks, in degree `max (2 * h + w) (4 * h + 1)`. The
  weakening and resolution rules are the formula-independent lemmas of `ChainC1`, `ChainC2`.
* `exists_weight_general`: the counting step for an arbitrary space `U` of polynomials of
  degree at most `k`: if its dimension exceeds the number of blocks times the number of
  monomials of degree at most `k` on a flat of a high-rank consistent block, some nonzero
  member of `U` has cofactors against the inputs of every such block.
* `generalCriterion`: the three combined with block removal (`L038`).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial Module PEqualNP.ProofComplexity

section Axiom

variable {V : Type} [DecidableEq V] {h M W : ℕ} {e : Fin W → LinEq V}
  {cl : Fin M → LinClause V}

omit [DecidableEq V] in
/-- The polynomial of a clause is the product, over its literals, of one plus the affine form
of the equation of the literal. -/
theorem clausePoly_eq_prod (A : Clause V) :
    clausePoly A = ∏ l ∈ A, (1 + eqPoly ((({l.1} : Finset V), l.2) : LinEq V)) := by
  unfold clausePoly
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases l with ⟨v, b⟩
  cases b
  · simp only [eqPoly, Finset.sum_singleton, Bool.false_eq_true, ite_false, C_1]
    linear_combination (-(1 : MvPolynomial V (ZMod 2))) * two_eq_zero_mvPolynomial (σ := V)
  · simp [eqPoly]

/-- An axiom of a CNF formula of width at most `w`: its block product comes from the clause
axiom of the polynomial system, in degree `2 * h + w`. -/
theorem block_ax_cnf {F : Set (Clause V)} {w : ℕ} (hw : ∀ A ∈ F, A.card ≤ w)
    (he : Function.Surjective e) (j : Fin M) {B : ℕ}
    (hB1 : 2 * h + w ≤ B) (hB2 : 2 * h + 1 ≤ B)
    (hax : cl j ∈ (fun A => linOfClause A) '' F) :
    PCDerivable (blockSystem (cnfSystem F) h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) j) := by
  classical
  obtain ⟨A, hAF, hA⟩ := hax
  have hAw := hw A hAF
  have hdP := totalDegree_blockProduct_le (h := h) j (totalDegree_clauseInputs_le e cl j)
  set S := blockSystem (cnfSystem F) h M W (clauseInputs e cl) with hS
  set P := blockProduct h M W (clauseInputs e cl) j with hPdef
  let a : Literal V → MvPolynomial (BlockVar V h M W) (ZMod 2) :=
    fun l => rename Sum.inl (eqPoly ((({l.1} : Finset V), l.2) : LinEq V))
  have hda : ∀ l ∈ A, (a l).totalDegree ≤ 1 := fun l _ =>
    totalDegree_rename_inl_le _ (totalDegree_eqPoly_le _)
  have ha : ∀ l ∈ A, PCDerivable S B (a l * P) := by
    intro l hl
    refine block_companion (F := cnfSystem F) (h := h) he j ?_ (B := B) hB2
    rw [← hA]
    exact Finset.mem_image.2 ⟨l, hl, rfl⟩
  have h1 := pcDerivable_prod_absorb A a P hdP ha hda (by omega)
  have hprod : rename (Sum.inl : V → BlockVar V h M W) (clausePoly A)
      = ∏ l ∈ A, (1 + a l) := by
    rw [clausePoly_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun l _ => by simp [a]
  have hdE : (∏ l ∈ A, (1 + a l)).totalDegree ≤ A.card := by
    have := totalDegree_prod_one_add_le A a hda
    omega
  have hE : PCDerivable S B (∏ l ∈ A, (1 + a l)) := by
    refine .ax (Or.inl ⟨clausePoly A, Or.inr ⟨A, hAF, rfl⟩, hprod.symm⟩) ?_
    omega
  have h2 := pcDerivable_mul_le hE P hdP hdE le_rfl (by omega)
  have h3 := h1.add h2
  have hEq : (∏ l ∈ A, (1 + a l)) * P + P + P * ∏ l ∈ A, (1 + a l) = P := by
    linear_combination char2_add_self ((∏ l ∈ A, (1 + a l)) * P)
  rw [hEq] at h3
  exact h3

end Axiom

/-- The line simulation for an arbitrary CNF formula of width at most `w`: a Res(⊕)
refutation `π` gives a polynomial calculus refutation of `cnfSystem F` extended by one block
per line, with affine inputs, in degree `max (2 * h + w) (4 * h + 1)`. -/
theorem chainC_cnf {V : Type} [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V)) (w h : ℕ) (hh : 1 ≤ h) (hw : ∀ A ∈ F, A.card ≤ w)
    (href : IsLinRefutation F π) :
    ∃ (W : ℕ) (g : Fin π.length → Fin W → MvPolynomial V (ZMod 2)),
      (∀ (j : Fin π.length) (i : Fin W), (g j i).totalDegree ≤ 1) ∧
      PCRefutable (blockSystem (cnfSystem F) h π.length W g)
        (max (2 * h + w) (4 * h + 1)) := by
  obtain ⟨hder, hemp⟩ := href
  classical
  let e : Fin (Fintype.card (LinEq V)) → LinEq V := (Fintype.equivFin _).symm
  have he : Function.Surjective e := (Fintype.equivFin _).symm.surjective
  refine ⟨_, clauseInputs e π.get, totalDegree_clauseInputs_le e π.get, ?_⟩
  have hbool : ∀ v : V, X v * X v + X v ∈ cnfSystem F := fun v => Or.inl ⟨v, rfl⟩
  have inv : ∀ σ, IsLinDerivation ((fun C => linOfClause C) '' F) σ →
      (∀ C ∈ σ, C ∈ π) → ∀ C ∈ σ, ∀ j : Fin π.length, π.get j = C →
      PCDerivable (blockSystem (cnfSystem F) h π.length _ (clauseInputs e π.get))
        (max (2 * h + w) (4 * h + 1))
        (blockProduct h π.length _ (clauseInputs e π.get) j) := by
    intro σ hσ
    induction hσ with
    | nil =>
      intro _ C hC
      simp at hC
    | @ax σ A _ hA ih =>
      intro hsub C hC j hj
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact block_ax_cnf hw he j (le_max_left _ _) (le_max_of_le_right (by omega))
          (by rw [hj]; exact hA)
      · exact ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC)) C hC' j hj
    | @res σ C D R _ hC hD hres ih =>
      intro hsub C' hC' j hj
      have ih' := ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC))
      rcases List.mem_cons.mp hC' with rfl | hC''
      · obtain ⟨jC, hjC⟩ := List.mem_iff_get.mp (hsub C (List.mem_cons_of_mem _ hC))
        obtain ⟨jD, hjD⟩ := List.mem_iff_get.mp (hsub D (List.mem_cons_of_mem _ hD))
        exact block_res he hbool jC jD j (le_max_right _ _) hh
          (by rw [hjC, hjD, hj]; exact hres) (ih' C hC jC hjC) (ih' D hD jD hjD)
      · exact ih' C' hC'' j hj
    | @weak σ C D _ hC himp ih =>
      intro hsub C' hC' j hj
      have ih' := ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC))
      rcases List.mem_cons.mp hC' with rfl | hC''
      · obtain ⟨jC, hjC⟩ := List.mem_iff_get.mp (hsub C (List.mem_cons_of_mem _ hC))
        refine block_weak he jC j (le_max_right _ _) hh ?_ (ih' C hC jC hjC)
        intro q hq
        rw [hjC] at hq
        rw [hj]
        exact lin_alternative q _ fun a ha => himp a ⟨q, hq, ha⟩
      · exact ih' C' hC'' j hj
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hemp
  have hfin := inv π hder (fun C hC => hC) ∅ hemp j hj
  have hone : blockProduct h π.length _ (clauseInputs e π.get) j = 1 := by
    have hj' : π[(j : ℕ)] = ∅ := hj
    simp [blockProduct, clauseInputs, hj']
  rw [hone] at hfin
  exact hfin

/-- The counting step for an arbitrary space of polynomials of degree at most `k`. If the
dimension of `U` exceeds `M` times the number of monomials of degree at most `k` in
`card σ - (r + 1)` variables, then some nonzero `f` of `U` is, for every block whose inputs
span a space of dimension above `r` not containing `1`, a combination of the inputs of the
block with cofactors of degree at most `k - 1`. -/
theorem exists_weight_general {σ : Type} [Fintype σ] [DecidableEq σ] {k r M W : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (hU : ∀ f ∈ U, f.totalDegree ≤ k)
    (g : Fin M → Fin W → MvPolynomial σ (ZMod 2))
    (hg : ∀ j i, (g j i).totalDegree ≤ 1)
    (hcount : M * (Fintype.card σ - (r + 1) + k).choose k < finrank (ZMod 2) U) :
    ∃ f ∈ U, f ≠ 0 ∧
      ∀ j, (1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
        r < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
        ∃ a : Fin W → MvPolynomial σ (ZMod 2),
          (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g j i := by
  classical
  have hall : ∀ j, ∃ (d : ℕ) (φ : σ → MvPolynomial (Fin d) (ZMod 2)) (ι : Fin d → σ),
      d ≤ Fintype.card σ - (r + 1) ∧ (∀ x, (φ x).totalDegree ≤ 1) ∧
      ((1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
        r < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
        ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range (g j))) := by
    intro j
    by_cases hj : (1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range (g j)) ∧
        r < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j)))
    · obtain ⟨d, φ, ι, hd, hφ, hmem⟩ := exists_param (g j) (hg j) hj.1
      exact ⟨d, φ, ι, by omega, hφ, fun _ _ => hmem⟩
    · exact ⟨0, fun _ => 0, Fin.elim0, Nat.zero_le _, fun _ => by simp,
        fun h1 hr => absurd ⟨h1, hr⟩ hj⟩
  choose d φ ι hd hφ hmem using hall
  have hrange : ∀ j, finrank (ZMod 2)
      (LinearMap.range ((aeval (φ j)).toLinearMap ∘ₗ U.subtype))
      ≤ (Fintype.card σ - (r + 1) + k).choose k := by
    intro j
    refine le_trans (le_trans (Submodule.finrank_mono ?_)
      (finrank_restrictTotalDegree_le (ZMod 2) (d j) k))
      (Nat.choose_le_choose k (Nat.add_le_add_right (hd j) k))
    rintro _ ⟨f, rfl⟩
    rw [mem_restrictTotalDegree]
    exact (totalDegree_aeval_le (φ j) (hφ j) f.1).trans (hU f.1 f.2)
  obtain ⟨v, hv, hzero⟩ := exists_ne_zero_forall_eq_zero
    (fun j => (aeval (φ j)).toLinearMap ∘ₗ U.subtype)
    (fun _ => (Fintype.card σ - (r + 1) + k).choose k) hrange
    (by simpa using hcount)
  refine ⟨v.1, v.2, fun h0 => hv (Subtype.ext h0), fun j h1 hr => ?_⟩
  have hcomp : aeval (fun x => rename (ι j) (φ j x))
      = ((rename (ι j)).comp (aeval (φ j)) : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] _) := by
    apply algHom_ext
    intro x
    simp
  have hker : aeval (fun x => rename (ι j) (φ j x)) v.1 = 0 := by
    have hz : aeval (φ j) v.1 = 0 := hzero j
    rw [hcomp, AlgHom.comp_apply, hz, map_zero]
  obtain ⟨a, ha, hdeg⟩ := exists_cofactors (fun x => rename (ι j) (φ j x))
    (fun x => (totalDegree_rename_le _ _).trans (hφ j x)) v.1 k (hU v.1 v.2)
  rw [hker, sub_zero] at ha
  have hc : ∀ x, ∃ c : Fin W → ZMod 2,
      ∑ i, c i • g j i = X x - rename (ι j) (φ j x) := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (hmem j h1 hr x)
  choose c hc using hc
  refine ⟨fun i => ∑ x, C (c x i) * a x, fun i => ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun x _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact hdeg x
  · rw [ha]
    simp_rw [← hc, Finset.mul_sum, Finset.sum_mul, smul_eq_C_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

/-- The general criterion. Let `F` be a CNF formula of width at most `w` on finitely many
variables, `π` a dag-like Res(⊕) refutation of `F`, and `U` a space of polynomials of degree
at most `k` none of whose nonzero members is derivable from `cnfSystem F` in degree
`k * (max (2 * h + w) (4 * h + 1) + 1)`. Then the dimension of `U` is at most the length of
`π` times the number of monomials of degree at most `k` in `card V - (h * (k + 1) + 1)`
variables. -/
theorem generalCriterion : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w h k : ℕ) (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))), 1 ≤ h → 1 ≤ k → (∀ C ∈ F, C.card ≤ w) → PEqualNP.ProofComplexity.IsLinRefutation F π → (∀ f ∈ U, f.totalDegree ≤ k) → (∀ f ∈ U, f ≠ 0 → ¬ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) (k * (max (2 * h + w) (4 * h + 1) + 1)) f) → Module.finrank (ZMod 2) U ≤ π.length * (Fintype.card V - (h * (k + 1) + 1) + k).choose k := by
  intro V _ _ F π w h k U hh hk hw href hU hnot
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨W, g, hg, hrefut⟩ := chainC_cnf F π w h hh hw href
  obtain ⟨f, hfU, hf0, hfw⟩ := exists_weight_general (r := h * (k + 1)) U hU g hg hlt
  refine hnot f hfU hf0 ?_
  refine L038 V (Fin π.length) W h k (max (2 * h + w) (4 * h + 1)) (cnfSystem F) g f
    (fun v => Or.inl ⟨v, rfl⟩) hg hh hk (le_max_of_le_right (by omega)) (hU f hfU)
    (fun b hb => ?_) ?_
  · by_cases h1 : (1 : MvPolynomial V (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (g b))
    · exact Or.inl h1
    · exact Or.inr (hfw b h1 hb)
  · refine pcDerivable_mono hrefut le_rfl ?_
    rintro p (⟨q, hq, rfl⟩ | ⟨r, rfl⟩ | ⟨j, i, rfl⟩)
    · exact Or.inl (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨r, rfl⟩
    · exact Or.inl (Or.inr ⟨j, i, rfl⟩)

end PEqualNP.ProofComplexity.Helpers
