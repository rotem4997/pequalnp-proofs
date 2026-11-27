import Mathlib
import PEqualNP.Gct.Helpers.Rung.Statements
import PEqualNP.Gct.Helpers.BertiniLite

/-!
# The good subspace

`goodSubspace : GoodSubspace`. Singular points of the gadget with rows in a good row space have
at most `M` distinct rows, so their parameters lie in finitely many subspaces (rows constant on
the classes of a colouring of the rows with `M` colours) of dimension at most `M l` of the
`a l`-dimensional parameter space. A subspace of dimension `(a - M) l` misses them all
(`exists_matrix_avoiding`), and the product over the `N` blocks does the same for the block sum,
whose gradient splits block by block.
-/

namespace PEqualNP.Gct.Rung

open MvPolynomial

/-- The elementary symmetric polynomial of degree `r` is homogeneous of degree `r`. -/
theorem goodSub_esymm_isHomogeneous (b r : ℕ) : (esymm (Fin b) ℂ r).IsHomogeneous r := by
  rw [esymm_eq_sum_subtype]
  refine IsHomogeneous.sum _ _ _ (fun t _ => ?_)
  have h := IsHomogeneous.prod t.1 (fun i : Fin b => (X i : MvPolynomial (Fin b) ℂ))
    (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)
  simpa [t.2] using h

/-- For `r ≥ 2` the gradient of `e_r` vanishes at the origin. -/
theorem gradZero_esymm_zero (b r : ℕ) (hr : 2 ≤ r) :
    GradZero (esymm (Fin b) ℂ r) (fun _ => 0) := by
  intro i
  rw [eval_zero', constantCoeff_eq]
  refine ((goodSub_esymm_isHomogeneous b r).pderiv (i := i)).coeff_eq_zero ?_
  simp
  omega

/-- A good row space for `r ≥ 2` is parametrized injectively. -/
theorem rowSpace_inj {b r l : ℕ} {P : Fin b → Fin l → ℂ} (hr : 2 ≤ r)
    (hP : RowSpaceGood b r l P) (y y' : Fin l → ℂ)
    (h : ∀ j, ∑ s, P j s * y s = ∑ s, P j s * y' s) : y = y' := by
  have h0 : (fun n => ∑ s, P n s * (y - y') s) = fun _ => 0 := by
    funext n
    simp [mul_sub, Finset.sum_sub_distrib, h n]
  have := hP (y - y') (by rw [h0]; exact gradZero_esymm_zero b r hr)
  exact sub_eq_zero.mp this

/-- One block: a parametrized subspace of dimension `(a - M) l` of the matrices with rows in the
row space on which the gradient of the gadget has no nonzero zero. -/
theorem goodSubspace_block {b r l : ℕ} {P : Fin b → Fin l → ℂ} {M : ℕ} (hr : 2 ≤ r)
    (hP : RowSpaceGood b r l P) (hM : RowsBounded b r l P M) (a : ℕ) :
    ∃ L1 : Fin a × Fin b → Fin ((a - M) * l) → ℂ, ∀ y : Fin ((a - M) * l) → ℂ,
      GradZero (gadgetPoly a b r) (fun p => ∑ s, L1 p s * y s) → y = 0 := by
  classical
  by_cases hMa : M ≤ a
  swap
  · refine ⟨fun _ _ => 0, fun y _ => ?_⟩
    have h0 : (a - M) * l = 0 := by
      rw [Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul]
    funext i
    exact absurd i.2 (by omega)
  let e : Fin a × Fin l ≃ Fin (a * l) := finProdFinEquiv
  let φ : (Fin a → Fin M) → (Fin M → Fin l → ℂ) →ₗ[ℂ] (Fin (a * l) → ℂ) := fun c =>
    { toFun := fun T k => T (c (e.symm k).1) (e.symm k).2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Finset (Submodule ℂ (Fin (a * l) → ℂ)) :=
    Finset.univ.image fun c : Fin a → Fin M => LinearMap.range (φ c)
  have hq : ∀ V ∈ W, Module.finrank ℂ V ≤ M * l := by
    intro V hV
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hV
    refine (LinearMap.finrank_range_le (φ c)).trans ?_
    simp [Module.finrank_pi_fintype]
  have hd : (a - M) * l + M * l ≤ a * l := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hMa]
  obtain ⟨L0, hL0⟩ :=
    PEqualNP.Gct.Helpers.exists_matrix_avoiding (a * l) ((a - M) * l) (M * l) W hq hd
  refine ⟨fun p s => ∑ t, P p.2 t * L0 (e (p.1, t)) s, fun y hy => ?_⟩
  let Y : Fin a → Fin l → ℂ := fun i t => ∑ s, L0 (e (i, t)) s * y s
  have hX : ∀ i j, (∑ s, (∑ t, P j t * L0 (e (i, t)) s) * y s) = ∑ t, P j t * Y i t := by
    intro i j
    simp only [Y, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  have hcard := hM a _ (fun i => ⟨Y i, fun j => hX i j⟩) hy
  let X : Fin a × Fin b → ℂ := fun p => ∑ s, (∑ t, P p.2 t * L0 (e (p.1, t)) s) * y s
  let S : Finset (Fin b → ℂ) := Finset.univ.image fun i : Fin a => fun j : Fin b => X (i, j)
  have hmem : ∀ i : Fin a, (fun j : Fin b => X (i, j)) ∈ S := fun i =>
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hcard' : S.card ≤ M := hcard
  let c : Fin a → Fin M := fun i => Fin.castLE hcard' (S.equivFin ⟨_, hmem i⟩)
  have hc : ∀ i i', c i = c i' → Y i = Y i' := by
    intro i i' h
    have h1 := S.equivFin.injective ((Fin.castLE_injective hcard') h)
    have h2 : (fun j : Fin b => X (i, j)) = fun j : Fin b => X (i', j) :=
      congrArg Subtype.val h1
    refine rowSpace_inj hr hP _ _ (fun j => ?_)
    rw [← hX i j, ← hX i' j]
    exact congrFun h2 j
  let T : Fin M → Fin l → ℂ := fun m t =>
    if h : ∃ i, c i = m then Y h.choose t else 0
  refine hL0 y (LinearMap.range (φ c)) (Finset.mem_image_of_mem _ (Finset.mem_univ c)) ⟨T, ?_⟩
  funext k
  have hex : ∃ i, c i = c (e.symm k).1 := ⟨_, rfl⟩
  show T (c (e.symm k).1) (e.symm k).2 = _
  simp only [T, dif_pos hex]
  rw [hc _ _ hex.choose_spec]
  show ∑ s, L0 (e ((e.symm k).1, (e.symm k).2)) s * y s = _
  simp

/-- The gradient of the block sum splits: a zero of it restricts to a zero of the gradient of
the gadget on every block. -/
theorem gradZero_block {N a b r : ℕ} (x : Fin N × Fin a × Fin b → ℂ)
    (hx : GradZero (blockPoly N a b r) x) (h : Fin N) :
    GradZero (gadgetPoly a b r) (fun p => x (h, p)) := by
  intro p
  have hinj : Function.Injective (fun p : Fin a × Fin b => (h, p)) := fun p q hpq =>
    congrArg Prod.snd hpq
  have := hx (h, p)
  unfold blockPoly at this
  rw [map_sum, map_sum, Finset.sum_eq_single h] at this
  · rw [pderiv_rename hinj, eval_rename] at this
    exact this
  · intro h' _ hne
    rw [pderiv_eq_zero_of_notMem_vars, map_zero]
    intro hmem
    obtain ⟨i, -, hi⟩ := mem_vars_rename _ _ hmem
    exact hne (congrArg Prod.fst hi)
  · intro hn
    exact absurd (Finset.mem_univ h) hn

/-- The good subspace. -/
theorem goodSubspace : GoodSubspace := by
  intro b r l P M hr hP hM a N
  obtain ⟨L1, hL1⟩ := goodSubspace_block hr hP hM a
  let e : Fin N × Fin ((a - M) * l) ≃ Fin (N * ((a - M) * l)) := finProdFinEquiv
  refine ⟨fun v s => if (e.symm s).1 = v.1 then L1 v.2 (e.symm s).2 else 0, fun y hy => ?_⟩
  have hsum : ∀ (h : Fin N) (p : Fin a × Fin b),
      (∑ s, (if (e.symm s).1 = h then L1 p (e.symm s).2 else 0) * y s)
        = ∑ t, L1 p t * y (e (h, t)) := by
    intro h p
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single h]
    · simp
    · intro h' _ hne
      simp [hne]
    · intro hn
      exact absurd (Finset.mem_univ h) hn
  have key : ∀ h : Fin N, (fun t => y (e (h, t))) = 0 := by
    intro h
    refine hL1 _ ?_
    have h1 := gradZero_block _ hy h
    have h2 : (fun p : Fin a × Fin b => ∑ t, L1 p t * y (e (h, t)))
        = fun p => ∑ s, (if (e.symm s).1 = h then L1 p (e.symm s).2 else 0) * y s :=
      funext fun p => (hsum h p).symm
    rw [h2]
    exact h1
  funext s
  have := congrFun (key (e.symm s).1) (e.symm s).2
  simpa using this

end PEqualNP.Gct.Rung
