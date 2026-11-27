import PEqualNP.ProofComplexity.Helpers.ChainC2

/-!
# Helpers: from a Res(⊕) refutation of bit pigeonhole to a polynomial calculus refutation of
a block extension

`chainC`: a Res(⊕) refutation `π` of `BPHP m l` gives, for every `h ≥ 1`, a family of
`π.length` blocks with affine inputs and a polynomial calculus refutation of the block
extension of `bitPHPSystem m l`, of degree `max (2 * h + l) (4 * h + 1)`.

Block `j` belongs to line `j` of `π`. All blocks have one input slot for every linear
equation on the variables; the slot of an equation that is not in the line holds the zero
input. The invariant: the block product of every line is derivable. The rule lemmas are in
`ChainC1`, the linear algebra behind semantic weakening is in `ChainC2`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial PEqualNP.ProofComplexity

theorem chainC : ∀ (m l h : ℕ) (π : List (LinClause (Fin m × Fin l))), 1 ≤ h →
    IsLinRefutation (BPHP m l) π →
    ∃ (M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)),
      M ≤ 3 * π.length + m.choose 2 ∧
      (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) ∧
      PCRefutable (blockSystem (bitPHPSystem m l) h M W g)
        (max (2 * h + l) (4 * h + 1)) := by
  intro m l h π hh ⟨hder, hemp⟩
  classical
  let e : Fin (Fintype.card (LinEq (Fin m × Fin l))) → LinEq (Fin m × Fin l) :=
    (Fintype.equivFin _).symm
  have he : Function.Surjective e := (Fintype.equivFin _).symm.surjective
  refine ⟨π.length, _, clauseInputs e π.get, by omega,
    totalDegree_clauseInputs_le e π.get, ?_⟩
  have hbool : ∀ v : Fin m × Fin l, X v * X v + X v ∈ bitPHPSystem m l :=
    fun v => Or.inl ⟨v, rfl⟩
  have inv : ∀ σ, IsLinDerivation ((fun C => linOfClause C) '' BPHP m l) σ →
      (∀ C ∈ σ, C ∈ π) → ∀ C ∈ σ, ∀ j : Fin π.length, π.get j = C →
      PCDerivable (blockSystem (bitPHPSystem m l) h π.length _ (clauseInputs e π.get))
        (max (2 * h + l) (4 * h + 1))
        (blockProduct h π.length _ (clauseInputs e π.get) j) := by
    intro σ hσ
    induction hσ with
    | nil =>
      intro _ C hC
      simp at hC
    | @ax σ A _ hA ih =>
      intro hsub C hC j hj
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact block_ax he j (le_max_left _ _) (le_max_of_le_right (by omega))
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

end PEqualNP.ProofComplexity.Helpers
