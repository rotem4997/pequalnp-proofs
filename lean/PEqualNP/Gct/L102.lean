import PEqualNP.Defs
import PEqualNP.Gct.Helpers.SProduct

/-! L-gct-102: `p + 1` row subspaces `W_1, ..., W_p, X` of `ℂ^q` all of whose level sums (over
`k`-sets of rows, `k ≥ 1`, of the injective sums) vanish, and a subspace `Y` of the zero-sum
hyperplane of `ℂ^p`, have total dimension at most `p + q - 2`. Proof (helper `SProduct`): zero
rows isolate each injective sum; `InvisibleBlock.diag_of_inj` and `ProdSigmaChain.chain` give
`∑ dim W_i + dim X + 1 ≤ q`; the sum functional gives `dim Y + 1 ≤ p`. -/

theorem PEqualNP.Gct.L102 : ∀ (p q : ℕ) (W : Fin p → Submodule ℂ (Fin q → ℂ)) (X : Submodule ℂ (Fin q → ℂ)) (Y : Submodule ℂ (Fin p → ℂ)), 1 ≤ p → 1 ≤ q → (∀ t : Option (Fin p) → (Fin q → ℂ), (∀ i, t (some i) ∈ W i) → t none ∈ X → ∀ k : ℕ, 1 ≤ k → ∑ R ∈ (Finset.univ : Finset (Option (Fin p))).powersetCard k, ∑ f : ↥R ↪ Fin q, ∏ r : ↥R, t (r : Option (Fin p)) (f r) = 0) → (∀ y ∈ Y, ∑ i, y i = 0) → ∑ i, Module.finrank ℂ (W i) + Module.finrank ℂ X + Module.finrank ℂ Y + 2 ≤ p + q := by
  exact PEqualNP.Gct.Helpers.SProduct.main
