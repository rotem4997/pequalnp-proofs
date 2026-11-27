import PEqualNP.Defs
import PEqualNP.Gct.Helpers.ProdSigmaChain

/-! L-gct-090 (Conjecture C): subspaces `S_1, ..., S_n` of `ℂ^n` all of whose nonempty column
product sums vanish have total dimension at most `n - 1`. It is a corollary of the chain bound
`ProdSigmaChain.chain` (proved under seat-gct-2's checked L-gct-079): the dimensions plus one are
at most the dimension of the span of all subset products, a subspace of `ℂ^n`. Paper proofs on
record: Lovitz-Petrov splitting theorem; good partition plus Rado (seat-barrier-1). -/

theorem PEqualNP.Gct.L090 :
    ∀ (n : ℕ) (S : Fin n → Submodule ℂ (Fin n → ℂ)), (∀ A : Finset (Fin n), A.Nonempty → ∀ s : Fin n → (Fin n → ℂ), (∀ j ∈ A, s j ∈ S j) → ∑ i, ∏ j ∈ A, s j i = 0) → ∑ j, Module.finrank ℂ (S j) ≤ n - 1 := by
  intro n S h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hc := PEqualNP.Gct.Helpers.ProdSigmaChain.chain n n hn S h
    have hle := Submodule.finrank_le (Submodule.span ℂ
        {v : Fin n → ℂ | ∃ (A : Finset (Fin n)) (t : Fin n → (Fin n → ℂ)),
          (∀ i ∈ A, t i ∈ S i) ∧ v = ∏ i ∈ A, t i})
    rw [Module.finrank_fin_fun] at hle
    omega
