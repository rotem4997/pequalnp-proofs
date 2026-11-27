import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.PCToolkit

/-!
# Helpers: block removal (Lemma 7.7 of arXiv:2609.23015)

From a degree `D` refutation of the system extended by blocks of new variables, the weighted
replay `pcDerivable_replay` with multiplier `f` and a substitution of degree at most `k`
gives a derivation of `f` from the original system in degree `k * (D + 1)`. For each block
the substitution comes from one of three cases: the low-rank substitution (hypothesis `H2`),
constants that make the product of the block vanish (when `1` is in the span), or the
cofactors of `f` (otherwise). The images of the axioms vanish at every Boolean point, so
they are derivable by the Boolean completeness hypothesis `H1`.
-/

namespace PEqualNP.ProofComplexity.Helpers.BlockRemoval

open MvPolynomial

/-- For one block, a substitution of degree at most `k` whose companion images, multiplied by
`f`, are derivable from `F` in degree `k * D + k`. -/
theorem block_exists
    (H1 : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p)
    (H2 : ∀ (σ : Type) (s h k : ℕ) (g : Fin s → MvPolynomial σ (ZMod 2)), (∀ i, (g i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1) → ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧ ∀ i : Fin s, (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')).totalDegree ≤ h * (k + 1) + 1 ∧ ∀ x : σ → ZMod 2, MvPolynomial.eval x (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')) = 0)
    {σ : Type} {s h k D : ℕ} (F : Set (MvPolynomial σ (ZMod 2)))
    (g : Fin s → MvPolynomial σ (ZMod 2)) (f : MvPolynomial σ (ZMod 2))
    (hBool : ∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (hh : 1 ≤ h) (hk : 1 ≤ k) (hD : 2 * h + 1 ≤ D)
    (hf : f.totalDegree ≤ k)
    (hblock : h * (k + 1) < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) →
      (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range g) ∨
        ∃ a : Fin s → MvPolynomial σ (ZMod 2), (∀ i, (a i).totalDegree ≤ k - 1) ∧
          f = ∑ i, a i * g i) :
    ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧
      ∀ i, PCDerivable F (k * D + k)
        (f * (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i'))) := by
  classical
  have hkD : k * (2 * h + 1) ≤ k * D := Nat.mul_le_mul_left _ hD
  let u0 : Fin h := ⟨0, by omega⟩
  by_cases hlow : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1)
  · obtain ⟨c, hc, hP⟩ := H2 σ s h k g hg hh hk hlow
    refine ⟨c, hc, fun i => H1 σ F _ _ hBool ?_ ?_⟩
    · refine (totalDegree_mul _ _).trans ?_
      have := (hP i).1
      have : h * (k + 1) + 1 ≤ k * D := by nlinarith
      omega
    · intro x
      rw [map_mul, (hP i).2 x, mul_zero]
  · rcases hblock (by omega) with hone | ⟨a, ha, hfa⟩
    · obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hone
      refine ⟨fun u i => if u = u0 then C (l i) else 0, ?_, fun i => ?_⟩
      · intro u i
        dsimp only; split_ifs
        · rw [totalDegree_C]; omega
        · rw [totalDegree_zero]; omega
      · have hprod : ∏ u : Fin h, (1 + ∑ i' : Fin s,
            (fun u i => if u = u0 then C (l i) else 0) u i' * g i') = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ u0) ?_
          simp only [ite_true]
          have : ∑ i' : Fin s, C (l i') * g i' = 1 := by
            rw [← hl]
            exact Finset.sum_congr rfl fun i' _ => (smul_eq_C_mul _ _).symm
          rw [this]
          exact CharTwo.add_self_eq_zero 1
        rw [hprod, mul_zero, mul_zero]
        exact .zero
    · refine ⟨fun u i => if u = u0 then a i else 0, ?_, fun i => ?_⟩
      · intro u i
        dsimp only; split_ifs
        · exact (ha i).trans (Nat.sub_le _ _)
        · rw [totalDegree_zero]; omega
      · have hprod : ∏ u : Fin h, (1 + ∑ i' : Fin s,
            (fun u i => if u = u0 then a i else 0) u i' * g i') = 1 + f := by
          rw [Finset.prod_eq_single u0]
          · simp only [ite_true]
            rw [hfa]
          · intro u _ hu
            simp [hu]
          · intro hu
            exact absurd (Finset.mem_univ u0) hu
        rw [hprod]
        refine H1 σ F _ _ hBool ?_ ?_
        · have h1f : (1 + f).totalDegree ≤ k := by
            refine (totalDegree_add _ _).trans ?_
            rw [totalDegree_one]
            exact max_le (Nat.zero_le _) hf
          have h2 : (g i * (1 + f)).totalDegree ≤ 1 + k :=
            (totalDegree_mul _ _).trans (Nat.add_le_add (hg i) h1f)
          have h3 : (f * (g i * (1 + f))).totalDegree ≤ k + (1 + k) :=
            (totalDegree_mul _ _).trans (Nat.add_le_add hf h2)
          refine h3.trans ?_
          nlinarith
        · intro x
          simp only [map_mul, map_add, map_one]
          generalize eval x f = y
          generalize eval x (g i) = z
          revert y z
          decide

theorem of_lemmas : (∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p
) → (∀ (σ : Type) (s h k : ℕ) (g : Fin s → MvPolynomial σ (ZMod 2)), (∀ i, (g i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1) → ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧ ∀ i : Fin s, (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')).totalDegree ≤ h * (k + 1) + 1 ∧ ∀ x : σ → ZMod 2, MvPolynomial.eval x (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')) = 0
) → ∀ (σ β : Type) (s h k D : ℕ) (F : Set (MvPolynomial σ (ZMod 2))) (g : β → Fin s → MvPolynomial σ (ZMod 2)) (f : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → (∀ b i, (g b i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → 2 * h + 1 ≤ D → f.totalDegree ≤ k → (∀ b : β, h * (k + 1) < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g b))) → (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (g b)) ∨ ∃ a : Fin s → MvPolynomial σ (ZMod 2), (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g b i) → PEqualNP.ProofComplexity.PCRefutable ((MvPolynomial.rename (Sum.inl : σ → σ ⊕ (β × Fin h × Fin s))) '' F ∪ {p | ∃ (b : β) (i : Fin s), p = MvPolynomial.rename Sum.inl (g b i) * ∏ u : Fin h, (1 + ∑ i' : Fin s, MvPolynomial.X (Sum.inr (b, u, i')) * MvPolynomial.rename Sum.inl (g b i'))} ∪ {p | ∃ t : β × Fin h × Fin s, p = MvPolynomial.X (Sum.inr t) * MvPolynomial.X (Sum.inr t) + MvPolynomial.X (Sum.inr t)}) D → PEqualNP.ProofComplexity.PCDerivable F (k * (D + 1)) f := by
  intro H1 H2 σ β s h k D F g f hBool hg hh hk hD hf hblock hRef
  classical
  have hex := fun b => block_exists H1 H2 F (g b) f hBool (hg b) hh hk hD hf (hblock b)
  choose c hc hcomp using hex
  let φ : σ ⊕ (β × Fin h × Fin s) → MvPolynomial σ (ZMod 2) :=
    Sum.elim X (fun t => c t.1 t.2.1 t.2.2)
  have hφ : ∀ j, (φ j).totalDegree ≤ k := by
    rintro (v | ⟨b, u, i⟩)
    · simp only [φ, Sum.elim_inl, totalDegree_X]; exact hk
    · exact hc b u i
  have hinl : ∀ q : MvPolynomial σ (ZMod 2), bind₁ φ (rename Sum.inl q) = q := by
    intro q
    rw [bind₁_rename]
    have : φ ∘ Sum.inl = X := rfl
    rw [this, bind₁_X_left]
    rfl
  have hkD : k * (2 * h + 1) ≤ k * D := Nat.mul_le_mul_left _ hD
  have hmain := pcDerivable_replay (G := F) (T := k) (s := k) φ hφ f hf ?_ hRef
  · rw [map_one, mul_one] at hmain
    have : k * (D + 1) = k * D + k := by ring
    rw [this]
    exact hmain
  intro a ha hdeg
  rcases ha with (⟨q, hq, rfl⟩ | ⟨b, i, rfl⟩) | ⟨t, rfl⟩
  · rw [hinl]
    have hq' : q.totalDegree ≤ k * D := by
      have := totalDegree_bind₁_le φ hφ (rename Sum.inl q)
      rw [hinl] at this
      exact this.trans (Nat.mul_le_mul_left _ hdeg)
    have := pcDerivable_mul_left (PCDerivable.ax (B := k * D) hq hq') f
    refine pcDerivable_mono this (max_le (by omega) (by omega)) subset_rfl
  · have himg : bind₁ φ (rename Sum.inl (g b i) * ∏ u : Fin h,
        (1 + ∑ i' : Fin s, X (Sum.inr (b, u, i')) * rename Sum.inl (g b i')))
        = g b i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c b u i' * g b i') := by
      simp only [map_mul, map_prod, map_add, map_one, map_sum, hinl, bind₁_X_right]
      rfl
    rw [himg]
    exact hcomp b i
  · simp only [map_mul, map_add, bind₁_X_right]
    refine H1 σ F _ _ hBool ?_ ?_
    · have h1 := hφ (Sum.inr t)
      have h2 : (φ (Sum.inr t) * φ (Sum.inr t) + φ (Sum.inr t)).totalDegree ≤ k + k :=
        (totalDegree_add _ _).trans (max_le
          ((totalDegree_mul _ _).trans (Nat.add_le_add h1 h1)) (h1.trans (by omega)))
      have h3 : (f * (φ (Sum.inr t) * φ (Sum.inr t) + φ (Sum.inr t))).totalDegree
          ≤ k + (k + k) := (totalDegree_mul _ _).trans (Nat.add_le_add hf h2)
      refine h3.trans ?_
      nlinarith
    · intro x
      simp only [map_mul, map_add]
      generalize eval x f = y
      generalize eval x (φ (Sum.inr t)) = z
      revert y z
      decide

end PEqualNP.ProofComplexity.Helpers.BlockRemoval
