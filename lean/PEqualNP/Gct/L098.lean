import PEqualNP.Defs
import PEqualNP.Gct.Helpers.InvisibleBlock

/-! L-gct-098 (Lemma I): a space `W` of `P × m` matrices on which, for every nonempty set `Y` of
columns, the injective sum `∑_(f : Y ↪ P) ∏_y t (f y, y)` vanishes has dimension at most `P - 1`.
Proof (helper `InvisibleBlock`): echelon `W` by last nonzero column into spaces `S_j ⊆ ℂ^P` with
`∑ dim S_j = dim W`; the injective sums vanish on families with column `y` from `S_y` (column
replacement through lifts); Moebius turns them into vanishing diagonal sums (char 0); the chain
bound `ProdSigmaChain.chain` (q = m, n = P) gives `∑ dim S_j + 1 ≤ P`. -/

theorem PEqualNP.Gct.L098 : ∀ (P m : ℕ) (W : Submodule ℂ (Fin P × Fin m → ℂ)), (∀ t ∈ W, ∀ Y : Finset (Fin m), Y.Nonempty → ∑ f : ↥Y ↪ Fin P, ∏ y : ↥Y, t (f y, (y : Fin m)) = 0) → Module.finrank ℂ W ≤ P - 1 := by
  intro P m W hW
  exact PEqualNP.Gct.Helpers.InvisibleBlock.lemmaI W hW
