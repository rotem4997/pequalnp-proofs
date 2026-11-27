import PEqualNP.ProofComplexity.Helpers.ChainC1

/-!
# Helpers: the linear algebra behind semantic weakening

If every Boolean point that satisfies the linear equation `q` satisfies some equation of the
linear clause `D`, then the affine system "`q` holds and every equation of `D` fails" has no
solution, so a combination of its equations is the contradiction `1 = 0`. In terms of the
affine forms `eqPoly`: some equations of `D` have affine forms that sum to `1` or to the
affine form of `q` (`lin_alternative`).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The coefficient vector of the affine form of a linear equation. -/
def eqVec (q : LinEq V) : (V → ZMod 2) × ZMod 2 :=
  (fun v => if v ∈ q.1 then 1 else 0, if q.2 = true then 0 else 1)

/-- The affine form with a given coefficient vector, as a linear map. -/
noncomputable def affPoly : ((V → ZMod 2) × ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) :=
  (Fintype.linearCombination (ZMod 2) (fun v : V => (X v : MvPolynomial V (ZMod 2)))).coprod
    (Algebra.linearMap (ZMod 2) (MvPolynomial V (ZMod 2)))

theorem affPoly_eqVec (q : LinEq V) : affPoly (eqVec q) = eqPoly q := by
  simp [affPoly, eqVec, eqPoly, Fintype.linearCombination_apply, MvPolynomial.algebraMap_eq,
    Finset.sum_ite_mem]

omit [DecidableEq V] in
theorem affPoly_one : affPoly ((0, 1) : (V → ZMod 2) × ZMod 2) = 1 := by
  simp [affPoly, Fintype.linearCombination_apply]

omit [Fintype V] [DecidableEq V] in
/-- A linear equation holds at the Boolean point of `a` exactly when its affine form is `1`
at `a`. -/
theorem linEqSat_iff_sum (a : V → ZMod 2) (q : LinEq V) :
    LinEqSat (fun v => decide (a v = 1)) q ↔
      ∑ v ∈ q.1, a v + (if q.2 = true then 0 else 1) = 1 := by
  unfold LinEqSat
  have hs : ∑ v ∈ q.1, a v
      = ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    generalize a v = x
    revert x
    decide
  rw [hs, ← ZMod.natCast_eq_one_iff_odd]
  generalize ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) = x
  rcases q with ⟨f, b⟩
  cases b
  · simp only [Bool.false_eq_true, iff_false, ite_false]
    revert x
    decide
  · simp

/-- The value of a linear functional on a coefficient vector. -/
theorem dual_apply (φ : Module.Dual (ZMod 2) ((V → ZMod 2) × ZMod 2))
    (h1 : φ (0, 1) = 1) (q : LinEq V) :
    φ (eqVec q) = ∑ v ∈ q.1, φ (fun j => if v = j then 1 else 0, 0) + (if q.2 = true then 0 else 1) := by
  have hsplit : eqVec q = LinearMap.inl (ZMod 2) (V → ZMod 2) (ZMod 2)
      (fun v => if v ∈ q.1 then 1 else 0)
      + (if q.2 = true then (0 : ZMod 2) else 1) • ((0, 1) : (V → ZMod 2) × ZMod 2) := by
    rcases q with ⟨f, b⟩
    cases b <;> simp [eqVec]
  rw [hsplit, map_add, map_smul, h1, ← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ]
  simp [Finset.sum_ite_mem]

/-- The alternative behind semantic weakening. -/
theorem lin_alternative (q : LinEq V) (D : LinClause V)
    (himp : ∀ a : V → Bool, LinEqSat a q → LinClauseSat a D) :
    ∃ J : Finset (LinEq V), J ⊆ D ∧
      (∑ d ∈ J, eqPoly d = 1 ∨ ∑ d ∈ J, eqPoly d = eqPoly q) := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hq : LinEqSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) q := by
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Set.mem_insert _ _))
      rw [map_add, h1] at this
      generalize φ (eqVec q) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hq
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨d, hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.mem_span_insert] at hmem
  obtain ⟨c, z, hz, hEq⟩ := hmem
  rw [Finsupp.mem_span_image_iff_linearCombination] at hz
  obtain ⟨lc, hlc, rfl⟩ := hz
  have hJ : lc.support ⊆ D := by
    intro d hd
    exact Finsupp.mem_supported _ _ |>.mp hlc hd
  have hsum : affPoly (Finsupp.linearCombination (ZMod 2) eqVec lc)
      = ∑ d ∈ lc.support, eqPoly d := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
    have h1 : lc d = 1 := by
      generalize lc d = x at h0
      revert x
      decide
    rw [h1, one_smul, affPoly_eqVec]
  have hP := congrArg affPoly hEq
  rw [map_add, map_smul, map_add, affPoly_one, affPoly_eqVec, hsum] at hP
  refine ⟨lc.support, hJ, ?_⟩
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc c with rfl | rfl
  · left
    rw [zero_smul, zero_add] at hP
    exact hP.symm
  · right
    rw [one_smul] at hP
    linear_combination hP + char2_add_self (∑ d ∈ lc.support, eqPoly d)
