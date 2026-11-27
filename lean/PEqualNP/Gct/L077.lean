import PEqualNP.Defs
import PEqualNP.Gct.L069
import PEqualNP.Gct.Helpers.GReduction

/-! L-gct-077, reduction of L-gct-037 to the level-space problem: if every subspace on which
`perm_n (J + ·)` is constant `n!` has dimension at most `G`, then every border determinantal
expression of `perm_(n+1)` has size at least `(n+1)^2 + 1 - G - 2(n+1)`. Proof: L-gct-069 at
`y = Sigma_(n+1)` with `k = G + 2n + 1`. A subspace on which `perm_(n+1) (Sigma + ·)` vanishes
meets the matrices supported off row and column `0` in a subspace of codimension at most
`2n + 1`, and on those matrices `perm_(n+1) (Sigma + c t) = - c * d/dc perm_n (J + c s)`
(`Helpers/GReduction.lean`), so by scaling `perm_n (J + s) = perm_n (J) = n!` there. -/

theorem PEqualNP.Gct.L077 : ∀ (n G : ℕ), (∀ L : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ L ≤ G) → ∀ N : ℕ, PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ (n + 1)) N → (n + 1) ^ 2 + 1 ≤ G + 2 * (n + 1) + N := by
  intro n G hG N hB
  have hy : MvPolynomial.eval (PEqualNP.Gct.GReduction.sig n)
      (PEqualNP.Gct.permPoly ℂ (n + 1)) = 0 := by
    have := PEqualNP.Gct.GReduction.key n 0 0
    simpa using this
  have := PEqualNP.Gct.L069 (n + 1) N (G + 2 * n + 1) (PEqualNP.Gct.GReduction.sig n) hy
    (PEqualNP.Gct.GReduction.bound n G hG) hB
  linarith
