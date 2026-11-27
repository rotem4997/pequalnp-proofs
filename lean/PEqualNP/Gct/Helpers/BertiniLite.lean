import Mathlib
import PEqualNP.Defs

/-!
Bertini-lite: a form whose singular points lie in finitely many subspaces of dimension at most
`q` has a smooth restriction to a general subspace of dimension `d` when `d + q ≤ n`.
The linear algebra (a `d`-dimensional parametrized subspace meeting each of finitely many
small subspaces only at the origin) is proved here; the passage from "no singular point on the
subspace" to "smooth restriction" is taken as a hypothesis (the statement of L-gct-053).
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- Finitely many subspaces of dimension at most `q` in `ℂ^n`, with `d + q ≤ n`: there is a
linear map from `ℂ^d` whose nonzero values avoid all of them. -/
theorem exists_linearMap_avoiding (n q : ℕ) (W : Finset (Submodule ℂ (Fin n → ℂ)))
    (hq : ∀ V ∈ W, Module.finrank ℂ V ≤ q) :
    ∀ d : ℕ, d + q ≤ n → ∃ f : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ),
      ∀ y : Fin d → ℂ, ∀ V ∈ W, f y ∈ V → y = 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨0, fun y _ _ _ => Subsingleton.elim _ _⟩
  | succ d ih =>
    intro hd
    obtain ⟨f, hf⟩ := ih (by omega)
    have hne : ∀ V : W, (V : Submodule ℂ (Fin n → ℂ)) ⊔ LinearMap.range f ≠ ⊤ := by
      intro V htop
      have h1 := Submodule.finrank_add_le_finrank_add_finrank
        (V : Submodule ℂ (Fin n → ℂ)) (LinearMap.range f)
      have h2 := LinearMap.finrank_range_le f
      have h3 := hq V V.2
      rw [htop, finrank_top, Module.finrank_fin_fun] at h1
      rw [Module.finrank_fin_fun] at h2
      omega
    obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
      (fun V : W => (V : Submodule ℂ (Fin n → ℂ)) ⊔ LinearMap.range f) hne
    let g : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
      f ∘ₗ (LinearMap.pi fun i : Fin d => LinearMap.proj (Fin.castSucc i))
        + (LinearMap.proj (Fin.last d)).smulRight c
    have hg : ∀ y : Fin (d + 1) → ℂ, g y = f (fun i => y (Fin.castSucc i)) + y (Fin.last d) • c := by
      intro y; rfl
    refine ⟨g, fun y V hV hy => ?_⟩
    rw [hg] at hy
    have hlast : y (Fin.last d) = 0 := by
      by_contra h0
      apply hc ⟨V, hV⟩
      have hmem : y (Fin.last d) • c ∈ V ⊔ LinearMap.range f := by
        have : y (Fin.last d) • c
            = (f (fun i => y (Fin.castSucc i)) + y (Fin.last d) • c)
              + f (-(fun i => y (Fin.castSucc i))) := by
          rw [map_neg]; abel
        rw [this]
        exact Submodule.add_mem_sup hy (LinearMap.mem_range_self f _)
      exact (Submodule.smul_mem_iff _ h0).mp hmem
    rw [hlast, zero_smul, add_zero] at hy
    have hinit := hf _ V hV hy
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hlast
    · simpa using congrFun hinit j

/-- The same, with the linear map written as a matrix. -/
theorem exists_matrix_avoiding (n d q : ℕ) (W : Finset (Submodule ℂ (Fin n → ℂ)))
    (hq : ∀ V ∈ W, Module.finrank ℂ V ≤ q) (hd : d + q ≤ n) :
    ∃ L : Fin n → Fin d → ℂ, ∀ y : Fin d → ℂ, ∀ V ∈ W,
      (fun k => ∑ s, L k s * y s) ∈ V → y = 0 := by
  obtain ⟨f, hf⟩ := exists_linearMap_avoiding n q W hq d hd
  refine ⟨fun k s => f (fun j => if s = j then 1 else 0) k, fun y V hV hy => hf y V hV ?_⟩
  have : f y = fun k => ∑ s, f (fun j => if s = j then 1 else 0) k * y s := by
    funext k
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp [Finset.sum_apply, mul_comm]
  rw [this]
  exact hy

/-- Relative version: finitely many subspaces of dimension at most `q` in `ℂ^n` and a subspace
`V` with `d + q ≤ dim V`: there is a linear map from `ℂ^d` into `V` whose nonzero values avoid
all of them. -/
theorem exists_linearMap_avoiding_sub (n q : ℕ) (V : Submodule ℂ (Fin n → ℂ))
    (W : Finset (Submodule ℂ (Fin n → ℂ)))
    (hq : ∀ U ∈ W, Module.finrank ℂ U ≤ q) :
    ∀ d : ℕ, d + q ≤ Module.finrank ℂ V → ∃ f : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ),
      (∀ y, f y ∈ V) ∧ ∀ y : Fin d → ℂ, ∀ U ∈ W, f y ∈ U → y = 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨0, fun y => by simp, fun y _ _ _ => Subsingleton.elim _ _⟩
  | succ d ih =>
    intro hd
    obtain ⟨f, hfV, hf⟩ := ih (by omega)
    have hne : ∀ U : W, Submodule.comap V.subtype
        ((U : Submodule ℂ (Fin n → ℂ)) ⊔ LinearMap.range f) ≠ ⊤ := by
      intro U htop
      rw [Submodule.comap_subtype_eq_top] at htop
      have h0 := Submodule.finrank_mono htop
      have h1 := Submodule.finrank_add_le_finrank_add_finrank
        (U : Submodule ℂ (Fin n → ℂ)) (LinearMap.range f)
      have h2 := LinearMap.finrank_range_le f
      have h3 := hq U U.2
      rw [Module.finrank_fin_fun] at h2
      omega
    obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
      (fun U : W => Submodule.comap V.subtype
        ((U : Submodule ℂ (Fin n → ℂ)) ⊔ LinearMap.range f)) hne
    let g : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
      f ∘ₗ (LinearMap.pi fun i : Fin d => LinearMap.proj (Fin.castSucc i))
        + (LinearMap.proj (Fin.last d)).smulRight (c : Fin n → ℂ)
    have hg : ∀ y : Fin (d + 1) → ℂ,
        g y = f (fun i => y (Fin.castSucc i)) + y (Fin.last d) • (c : Fin n → ℂ) := by
      intro y; rfl
    refine ⟨g, fun y => ?_, fun y U hU hy => ?_⟩
    · rw [hg]
      exact V.add_mem (hfV _) (V.smul_mem _ c.2)
    rw [hg] at hy
    have hlast : y (Fin.last d) = 0 := by
      by_contra h0
      apply hc ⟨U, hU⟩
      have hmem : y (Fin.last d) • (c : Fin n → ℂ) ∈ U ⊔ LinearMap.range f := by
        have : y (Fin.last d) • (c : Fin n → ℂ)
            = (f (fun i => y (Fin.castSucc i)) + y (Fin.last d) • (c : Fin n → ℂ))
              + f (-(fun i => y (Fin.castSucc i))) := by
          rw [map_neg]; abel
        rw [this]
        exact Submodule.add_mem_sup hy (LinearMap.mem_range_self f _)
      rw [Submodule.mem_comap]
      exact (Submodule.smul_mem_iff _ h0).mp hmem
    rw [hlast, zero_smul, add_zero] at hy
    have hinit := hf _ U hU hy
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hlast
    · simpa using congrFun hinit j

/-- The relative version with the linear map written as a matrix: every value lies in `V`, and
no nonzero value lies in a member of `W`. -/
theorem exists_matrix_avoiding_sub (n d q : ℕ) (V : Submodule ℂ (Fin n → ℂ))
    (W : Finset (Submodule ℂ (Fin n → ℂ)))
    (hq : ∀ U ∈ W, Module.finrank ℂ U ≤ q) (hd : d + q ≤ Module.finrank ℂ V) :
    ∃ L : Fin n → Fin d → ℂ, (∀ y : Fin d → ℂ, (fun k => ∑ s, L k s * y s) ∈ V) ∧
      ∀ y : Fin d → ℂ, ∀ U ∈ W, (fun k => ∑ s, L k s * y s) ∈ U → y = 0 := by
  obtain ⟨f, hfV, hf⟩ := exists_linearMap_avoiding_sub n q V W hq d hd
  have key : ∀ y : Fin d → ℂ,
      f y = fun k => ∑ s, f (fun j => if s = j then 1 else 0) k * y s := by
    intro y
    funext k
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp [Finset.sum_apply, mul_comm]
  refine ⟨fun k s => f (fun j => if s = j then 1 else 0) k, fun y => ?_, fun y U hU hy => ?_⟩
  · have := hfV y
    rw [key] at this
    exact this
  · refine hf y U hU ?_
    rw [key]
    exact hy

/-- Bertini-lite relative to a subspace, from the statement of L-gct-053. -/
theorem bertini_lite_sub_of
    (hTS : ∀ (N d r : ℕ) (G : MvPolynomial (Fin N) ℂ) (L : Fin N → Fin d → ℂ), G.IsHomogeneous r → (∀ y : Fin d → ℂ, (∀ i, MvPolynomial.eval (fun n => ∑ s, L n s * y s) (MvPolynomial.pderiv i G) = 0) → y = 0) → ∃ M : Fin N → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun n => ∑ t, MvPolynomial.C (M n t) * MvPolynomial.X t) G)) = 0) → y = 0) :
    ∀ (n d q r : ℕ) (F : MvPolynomial (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) (W : Finset (Submodule ℂ (Fin n → ℂ))), F.IsHomogeneous r → (∀ U ∈ W, Module.finrank ℂ U ≤ q) → (∀ x ∈ V, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → ∃ U ∈ W, x ∈ U) → d + q ≤ Module.finrank ℂ V → ∃ M : Fin n → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun k => ∑ t, MvPolynomial.C (M k t) * MvPolynomial.X t) F)) = 0) → y = 0 := by
  intro n d q r F V W hF hq hsing hd
  obtain ⟨L, hLV, hL⟩ := exists_matrix_avoiding_sub n d q V W hq hd
  refine hTS n d r F L hF (fun y hy => ?_)
  obtain ⟨U, hU, hmem⟩ := hsing _ (hLV y) hy
  exact hL y U hU hmem

/-- Bertini-lite, from the statement of L-gct-053: the case `V = ⊤` of the relative version. -/
theorem bertini_lite_of
    (hTS : ∀ (N d r : ℕ) (G : MvPolynomial (Fin N) ℂ) (L : Fin N → Fin d → ℂ), G.IsHomogeneous r → (∀ y : Fin d → ℂ, (∀ i, MvPolynomial.eval (fun n => ∑ s, L n s * y s) (MvPolynomial.pderiv i G) = 0) → y = 0) → ∃ M : Fin N → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun n => ∑ t, MvPolynomial.C (M n t) * MvPolynomial.X t) G)) = 0) → y = 0) :
    ∀ (n d q r : ℕ) (F : MvPolynomial (Fin n) ℂ) (W : Finset (Submodule ℂ (Fin n → ℂ))), F.IsHomogeneous r → (∀ V ∈ W, Module.finrank ℂ V ≤ q) → (∀ x : Fin n → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → ∃ V ∈ W, x ∈ V) → d + q ≤ n → ∃ M : Fin n → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun k => ∑ t, MvPolynomial.C (M k t) * MvPolynomial.X t) F)) = 0) → y = 0 := by
  intro n d q r F W hF hq hsing hd
  refine bertini_lite_sub_of hTS n d q r F ⊤ W hF hq (fun x _ hx => hsing x hx) ?_
  rw [finrank_top, Module.finrank_fin_fun]
  exact hd

end PEqualNP.Gct.Helpers
