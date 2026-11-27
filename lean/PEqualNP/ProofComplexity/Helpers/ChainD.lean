import PEqualNP.Defs.ProofComplexityChain
import PEqualNP.ProofComplexity.Helpers.PCToolkit
import PEqualNP.ProofComplexity.Helpers.RowLinear
import PEqualNP.ProofComplexity.L038
import Mathlib

/-!
# Helpers: a nonzero row-linear polynomial from a refutation with blocks

This file checks the last step of Section 6 of arXiv:2609.23015 (unrefereed) on our
definitions: a polynomial calculus refutation of degree `D` of the bit pigeonhole system
extended by `M` blocks of accuracy `3 * l` with affine inputs gives a derivation, from the bit
pigeonhole system alone and in degree `k * (D + 1)`, of a nonzero row-linear polynomial of
degree at most `k` (`chainD`).

The removal of the blocks with a multiplier `f` is the checked statement `L038`. This file
supplies the multiplier:

* `exists_param`: a system of affine equations whose span does not contain `1` has an affine
  parametrisation of its zero set by `d` of the variables, with `d` plus the dimension of the
  span at most the number of variables, such that every `X x` minus its parametrisation is a
  constant combination of the equations (Gaussian elimination, done by choosing a largest set
  of free variables);
* `exists_weight`: one nonzero row-linear `f` of degree at most `k` that is, for every block
  whose span has dimension above `3 * l * (k + 1)` and does not contain `1`, a combination of
  the inputs of the block with cofactors of degree at most `k - 1` (the counting lemma
  `exists_rowLinear_eq_sum_mul`).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial Module

theorem two_eq_zero_mvPolynomial {σ : Type} : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  calc (2 : MvPolynomial σ (ZMod 2)) = C (1 + 1) := by rw [C_add, C_1, one_add_one_eq_two]
    _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from rfl, C_0]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

section Param

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The affine polynomial with coefficient vector `c`: the constant term is `c none` and the
coefficient of `X x` is `c (some x)`. -/
noncomputable def affLin (σ : Type) [Fintype σ] :
    (Option σ → ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (fun o : Option σ => o.elim 1 X)

omit [DecidableEq σ] in
theorem affLin_apply (c : Option σ → ZMod 2) :
    affLin σ c = C (c none) + ∑ x, C (c (some x)) * X x := by
  rw [affLin, Fintype.linearCombination_apply, Fintype.sum_option]
  simp [smul_eq_C_mul]

/-- Every polynomial of degree at most one is affine with some coefficient vector. -/
theorem exists_affLin_eq (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ 1) :
    ∃ c, affLin σ c = p := by
  obtain ⟨a, ha, hdeg⟩ := exists_cofactors (fun _ : σ => (0 : MvPolynomial σ (ZMod 2)))
    (fun _ => by simp) p 1 hp
  have ha0 : ∀ x, a x = C ((a x).coeff 0) := fun x =>
    totalDegree_eq_zero_iff_eq_C.1 (by have := hdeg x; omega)
  have h0 : aeval (fun _ : σ => (0 : MvPolynomial σ (ZMod 2))) p = C (constantCoeff p) := by
    simpa using aeval_zero' (S₁ := MvPolynomial σ (ZMod 2)) p
  rw [h0] at ha
  refine ⟨fun o => o.elim (constantCoeff p) (fun x => (a x).coeff 0), ?_⟩
  rw [affLin_apply]
  calc C (constantCoeff p) + ∑ x, C ((a x).coeff 0) * X x
      = C (constantCoeff p) + ∑ x, a x * (X x - 0) := by
        congr 1
        exact Finset.sum_congr rfl fun x _ => by rw [sub_zero, ← ha0 x]
    _ = p := by rw [← ha]; ring

/-- The bridge from equations to a parametrisation (Lemma 6.1 of arXiv:2609.23015). Let `g`
be affine polynomials whose span does not contain `1`. Then there are `d` variables, named by
`ι`, and affine polynomials `φ x` in `d` variables such that every `X x - φ x (read in the
variables ι)` lies in the span of `g`, and `d` plus the dimension of the span is at most the
number of variables. -/
theorem exists_param {W : ℕ} (g : Fin W → MvPolynomial σ (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1)
    (h1 : (1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range g)) :
    ∃ (d : ℕ) (φ : σ → MvPolynomial (Fin d) (ZMod 2)) (ι : Fin d → σ),
      d + finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ Fintype.card σ ∧
      (∀ x, (φ x).totalDegree ≤ 1) ∧
      ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range g) := by
  classical
  set S := Submodule.span (ZMod 2) (Set.range g) with hS
  set S' := S.comap (affLin σ) with hS'
  let P : Finset σ → Prop := fun Fr => ∀ c ∈ S', (∀ x, x ∉ Fr → c (some x) = 0) → c = 0
  have hP0 : P ∅ := by
    intro c hc h0
    have hlin : affLin σ c = C (c none) := by
      rw [affLin_apply]
      simp [h0]
    rcases zmod2_cases (c none) with hn | hn
    · funext o
      cases o with
      | none => exact hn
      | some x => exact h0 x (Finset.notMem_empty x)
    · exfalso
      apply h1
      have : affLin σ c ∈ S := hc
      rwa [hlin, hn, C_1] at this
  obtain ⟨Fr, hFr, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, by simp [hP0]⟩
  have hPFr : P Fr := (Finset.mem_filter.1 hFr).2
  have hstep : ∀ x, ∃ c' : Option σ → ZMod 2,
      (∀ y, y ∉ Fr → c' (some y) = 0) ∧ X x - affLin σ c' ∈ S := by
    intro x
    by_cases hx : x ∈ Fr
    · refine ⟨Pi.single (some x) 1, fun y hy => ?_, ?_⟩
      · have hne : some y ≠ some x := fun h => hy (Option.some.inj h ▸ hx)
        exact Pi.single_eq_of_ne hne 1
      · have : affLin σ (Pi.single (some x) 1) = X x := by
          rw [affLin, Fintype.linearCombination_apply_single]
          simp
        rw [this, sub_self]
        exact S.zero_mem
    · have hnP : ¬ P (insert x Fr) := by
        intro hP
        have := hmax (insert x Fr) (by simp [hP])
        rw [Finset.card_insert_of_notMem hx] at this
        omega
      simp only [P] at hnP
      push Not at hnP
      obtain ⟨c, hcS, hc0, hcne⟩ := hnP
      have hcx : c (some x) = 1 := by
        rcases zmod2_cases (c (some x)) with h0 | h0
        · exfalso
          apply hcne
          refine hPFr c hcS fun y hy => ?_
          by_cases hyx : y = x
          · rw [hyx]; exact h0
          · exact hc0 y (by simp [hyx, hy])
        · exact h0
      refine ⟨Function.update c (some x) 0, fun y hy => ?_, ?_⟩
      · by_cases hyx : y = x
        · subst hyx; simp
        · have hne : some y ≠ some x := fun h => hyx (Option.some.inj h)
          rw [Function.update_of_ne hne]
          exact hc0 y (by simp [hyx, hy])
      · have hsum : c = Function.update c (some x) 0 + Pi.single (some x) 1 := by
          funext o
          by_cases ho : o = some x
          · subst ho; simp [hcx]
          · simp [Function.update_of_ne ho, Pi.single_eq_of_ne ho]
        have hX : affLin σ (Pi.single (some x) 1) = X x := by
          rw [affLin, Fintype.linearCombination_apply_single]
          simp
        have hlin : affLin σ c = affLin σ (Function.update c (some x) 0) + X x := by
          conv_lhs => rw [hsum]
          rw [map_add, hX]
        have hmem : affLin σ c ∈ S := hcS
        have h2 := two_eq_zero_mvPolynomial (σ := σ)
        have : X x - affLin σ (Function.update c (some x) 0) = affLin σ c := by
          rw [hlin]
          linear_combination (-(affLin σ (Function.update c (some x) 0))) * h2
        rw [this]
        exact hmem
  choose c' hc'0 hc'S using hstep
  let e : Fin Fr.card ≃ Fr := Fr.equivFin.symm
  refine ⟨Fr.card, fun x => C (c' x none) + ∑ t, C (c' x (some (e t).1)) * X t,
    fun t => (e t).1, ?_, fun x => ?_, fun x => ?_⟩
  · have hSle : S ≤ LinearMap.range (affLin σ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_range.2 (exists_affLin_eq _ (hg i))
    have hmap : S'.map (affLin σ) = S := Submodule.map_comap_eq_of_le hSle
    have hr1 : finrank (ZMod 2) S ≤ finrank (ZMod 2) S' := by
      rw [← hmap]
      exact Submodule.finrank_map_le _ _
    let π : S' →ₗ[ZMod 2] ({x : σ // x ∉ Fr} → ZMod 2) :=
      LinearMap.pi fun x => (LinearMap.proj (some x.1)) ∘ₗ S'.subtype
    have hπ : Function.Injective π := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      apply Subtype.ext
      exact hPFr c.1 c.2 fun x hx => congrFun hc ⟨x, hx⟩
    have hr2 := LinearMap.finrank_le_finrank_of_injective hπ
    have hcard : Fintype.card {x : σ // x ∉ Fr} = Fintype.card σ - Fr.card := by
      simp [Fintype.card_subtype_compl]
    rw [Module.finrank_fintype_fun_eq_card, hcard] at hr2
    have := Finset.card_le_univ Fr
    omega
  · refine (totalDegree_add _ _).trans (max_le (by simp) (totalDegree_finsetSum_le fun t _ => ?_))
    refine (totalDegree_mul _ _).trans ?_
    simp
  · have hren : rename (fun t => (e t).1) (C (c' x none) + ∑ t, C (c' x (some (e t).1)) * X t)
        = affLin σ (c' x) := by
      rw [affLin_apply]
      simp only [map_add, map_sum, map_mul, rename_C, rename_X]
      congr 1
      calc ∑ t, C (c' x (some (e t).1)) * X (e t).1
          = ∑ y : Fr, C (c' x (some y.1)) * X y.1 :=
            Equiv.sum_comp e
              (fun y : Fr => C (c' x (some y.1)) * (X y.1 : MvPolynomial σ (ZMod 2)))
        _ = ∑ y ∈ Fr, C (c' x (some y)) * X y :=
            Finset.sum_coe_sort Fr
              (fun y => C (c' x (some y)) * (X y : MvPolynomial σ (ZMod 2)))
        _ = ∑ y, C (c' x (some y)) * X y :=
            Finset.sum_subset (Finset.subset_univ Fr)
              (fun y _ hy => by rw [hc'0 x y hy, C_0, zero_mul])
    rw [hren]
    exact hc'S x

end Param

/-- The multiplier. Under the numeric hypotheses of the counting lemma there is one nonzero
row-linear `f` of degree at most `k` that is, for every block `j` whose inputs span a space
of dimension above `3 * l * (k + 1)` not containing `1`, a combination of the inputs of the
block with cofactors of degree at most `k - 1`. -/
theorem exists_weight {m l k M W : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2))
    (hg : ∀ j i, (g j i).totalDegree ≤ 1) :
    ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ f ∈ rowLinear m l k ∧
      ∀ j, (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
          ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
        3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
        ∃ a : Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2),
          (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g j i := by
  classical
  have hpar : ∀ j, (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
        ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
      3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
      ∃ (d : ℕ) (φ : Fin m × Fin l → MvPolynomial (Fin d) (ZMod 2))
        (ι : Fin d → Fin m × Fin l), d + 3 * l * (k + 1) + 1 ≤ m * l ∧
        (∀ x, (φ x).totalDegree ≤ 1) ∧
        ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range (g j)) := by
    intro j h1 hr
    obtain ⟨d, φ, ι, hd, hφ, hmem⟩ := exists_param (g j) (hg j) h1
    refine ⟨d, φ, ι, ?_, hφ, hmem⟩
    simp only [Fintype.card_prod, Fintype.card_fin] at hd
    omega
  by_cases hsmall : 3 * l * (k + 1) + 1 ≤ m * l
  · have hall : ∀ j, ∃ (d : ℕ) (φ : Fin m × Fin l → MvPolynomial (Fin d) (ZMod 2))
        (ι : Fin d → Fin m × Fin l), d + 3 * l * (k + 1) + 1 ≤ m * l ∧
        (∀ x, (φ x).totalDegree ≤ 1) ∧
        ((1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
            ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
          3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
          ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range (g j))) := by
      intro j
      by_cases hj : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
            ∉ Submodule.span (ZMod 2) (Set.range (g j)) ∧
          3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j)))
      · obtain ⟨d, φ, ι, hd, hφ, hmem⟩ := hpar j hj.1 hj.2
        exact ⟨d, φ, ι, hd, hφ, fun _ _ => hmem⟩
      · exact ⟨0, fun _ => 0, Fin.elim0, by omega, fun _ => by simp,
          fun h1 hr => absurd ⟨h1, hr⟩ hj⟩
    choose d φ ι hd hφ hmem using hall
    obtain ⟨f, hf, hf0, hcomb⟩ := exists_rowLinear_eq_sum_mul hl hkm hlog d hd φ hφ ι
    refine ⟨f, hf0, hf, fun j h1 hr => ?_⟩
    obtain ⟨a, ha, hdeg⟩ := hcomb j
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
  · refine ⟨1, one_ne_zero, ?_, fun j h1 hr => ?_⟩
    · intro u hu
      have hu' : u ∈ (1 : MvPolynomial (Fin m × Fin l) (ZMod 2)).support := hu
      have h1 : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2)) = monomial 0 1 := rfl
      rw [h1, support_monomial] at hu'
      have : u = 0 := by simpa using hu'
      subst this
      exact ⟨by simp, fun i => by simp⟩
    · obtain ⟨d, φ, ι, hd, -, -⟩ := hpar j h1 hr
      omega

/-- Chain link D: a refutation of degree `D` of the bit pigeonhole system with `M` blocks of
accuracy `3 * l` gives a nonzero row-linear polynomial of degree at most `k` derivable from
the bit pigeonhole system in degree `k * (D + 1)`. -/
theorem chainD : ∀ (m l k D M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)), 0 < m → 1 ≤ l → 1 ≤ k → 1 ≤ M → k ≤ m → (m : ℝ) * Real.log (4 * (M : ℝ)) ≤ (k : ℝ) ^ 2 → 2 * (3 * l) + 1 ≤ D → (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.blockSystem (PEqualNP.ProofComplexity.bitPHPSystem m l) (3 * l) M W g) D → ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ PEqualNP.ProofComplexity.IsRowLinear m l k f ∧ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) (k * (D + 1)) f := by
  intro m l k D M W g _hm hl hk _hM hkm hlog hD hg href
  classical
  obtain ⟨f, hf0, hfmem, hfw⟩ := exists_weight hl hkm hlog g hg
  refine ⟨f, hf0, fun u hu => hfmem (Finset.mem_coe.2 hu), ?_⟩
  refine L038 (Fin m × Fin l) (Fin M) W (3 * l) k D (bitPHPSystem m l) g f
    (fun v => Or.inl ⟨v, rfl⟩) hg (by omega) hk hD (totalDegree_le_of_mem_rowLinear hfmem)
    (fun b hb => ?_) ?_
  · by_cases h1 : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
        ∈ Submodule.span (ZMod 2) (Set.range (g b))
    · exact Or.inl h1
    · exact Or.inr (hfw b h1 hb)
  · refine pcDerivable_mono href le_rfl ?_
    rintro p (⟨q, hq, rfl⟩ | ⟨r, rfl⟩ | ⟨j, i, rfl⟩)
    · exact Or.inl (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨r, rfl⟩
    · exact Or.inl (Or.inr ⟨j, i, rfl⟩)

end PEqualNP.ProofComplexity.Helpers
