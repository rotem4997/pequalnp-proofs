import PEqualNP.Defs
import Mathlib.Tactic

open PEqualNP.ProofComplexity MvPolynomial in
/-- Two pigeons and one hole: a polynomial calculus refutation of degree 2. -/
theorem PEqualNP.ProofComplexity.L040 : PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.funPHPSystem 2 1) 2 := by
  have h2 : (2 : MvPolynomial (Fin 2 × Fin 1) (ZMod 2)) = 0 := by
    have h : (C (2 : ZMod 2) : MvPolynomial (Fin 2 × Fin 1) (ZMod 2)) = 0 := by
      rw [show (2 : ZMod 2) = 0 by decide, C_0]
    rwa [show (C (2 : ZMod 2) : MvPolynomial (Fin 2 × Fin 1) (ZMod 2)) = 2 from map_ofNat C 2] at h
  have dX : ∀ v : Fin 2 × Fin 1, (X v : MvPolynomial (Fin 2 × Fin 1) (ZMod 2)).totalDegree ≤ 1 := by
    intro v; simp [totalDegree_X]
  have dA : ∀ v : Fin 2 × Fin 1, ((X v : MvPolynomial (Fin 2 × Fin 1) (ZMod 2)) + 1).totalDegree ≤ 1 := by
    intro v
    refine (totalDegree_add _ _).trans ?_
    simp [totalDegree_X]
  have a1 : PCDerivable (funPHPSystem 2 1) 2 (X ((0 : Fin 2), (0 : Fin 1)) + 1) :=
    PCDerivable.ax (Or.inr (Or.inr (Or.inr ⟨0, by simp⟩))) ((dA _).trans (by norm_num))
  have a2 : PCDerivable (funPHPSystem 2 1) 2 (X ((1 : Fin 2), (0 : Fin 1)) + 1) :=
    PCDerivable.ax (Or.inr (Or.inr (Or.inr ⟨1, by simp⟩))) ((dA _).trans (by norm_num))
  have a3 : PCDerivable (funPHPSystem 2 1) 2
      (X ((0 : Fin 2), (0 : Fin 1)) * X ((1 : Fin 2), (0 : Fin 1))) :=
    PCDerivable.ax (Or.inr (Or.inr (Or.inl ⟨0, 1, 0, by decide, rfl⟩)))
      ((totalDegree_mul _ _).trans (by have := dX (0, 0); have := dX (1, 0); omega))
  have m1 := PCDerivable.mulX ((1 : Fin 2), (0 : Fin 1)) a1
    ((totalDegree_mul _ _).trans (by have := dX (1, 0); have := dA (0, 0); omega))
  have s := PCDerivable.add (PCDerivable.add m1 a3) a2
  have e : X ((1 : Fin 2), (0 : Fin 1)) * (X ((0 : Fin 2), (0 : Fin 1)) + 1)
      + X ((0 : Fin 2), (0 : Fin 1)) * X ((1 : Fin 2), (0 : Fin 1))
      + (X ((1 : Fin 2), (0 : Fin 1)) + 1) = (1 : MvPolynomial (Fin 2 × Fin 1) (ZMod 2)) := by
    linear_combination (X ((0 : Fin 2), (0 : Fin 1)) * X ((1 : Fin 2), (0 : Fin 1))
      + X ((1 : Fin 2), (0 : Fin 1))) * h2
  unfold PCRefutable
  rw [← e]; exact s
