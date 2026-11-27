import PEqualNP.Defs
import PEqualNP.Gct.Helpers.SigmaReduction

/-! L-gct-062, reduction at Sigma_m = all ones except `1 - m` at `(0, 0)`, with `m = n + 1`. If
the permanent vanishes on `Sigma_m + L`, then `dim L <= 4 n + F`, where `F` bounds the dimension
of every space of `n × n` matrices on which the second and third power sums vanish. Proof: the
directions of `L` vanishing on the first row and column with vanishing row and column sums have
codimension at most `4 n`; along them the second and third Taylor terms of the permanent at
Sigma_m are nonzero multiples of the second and third power sums of the block. -/

open MvPolynomial in
theorem PEqualNP.Gct.L062 : ∀ (n k : ℕ), 2 ≤ n → (∀ W : Submodule ℂ (Fin n × Fin n → ℂ), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) → (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → Module.finrank ℂ W ≤ k) → ∀ L : Submodule ℂ (Fin (n + 1) × Fin (n + 1) → ℂ), (∀ t ∈ L, MvPolynomial.eval ((fun p : Fin (n + 1) × Fin (n + 1) => if p.1.val = 0 ∧ p.2.val = 0 then 1 - ((n : ℂ) + 1) else 1) + t) (PEqualNP.Gct.permPoly ℂ (n + 1)) = 0) → Module.finrank ℂ L ≤ 4 * n + k := by
  intro n k hn hW L hL
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hpt : (fun q : Fin (p + 1 + 1) × Fin (p + 1 + 1) =>
      if q.1.val = 0 ∧ q.2.val = 0 then 1 - (((p + 1 : ℕ) : ℂ) + 1) else 1) =
      PEqualNP.Gct.Helpers.mrPoint p := by
    funext q
    simp only [PEqualNP.Gct.Helpers.mrPoint, Prod.ext_iff, Fin.ext_iff, Fin.val_zero]
    push_cast
    ring_nf
  rw [hpt] at hL
  exact PEqualNP.Gct.SigmaRed.core p k (by omega) hW L hL
