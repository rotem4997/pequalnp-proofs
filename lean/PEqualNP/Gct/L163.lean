import PEqualNP.Defs
import PEqualNP.Gct.Helpers.T3Assembly

/-! L-gct-163 (T3): if `A + B` is totally isotropic, `C` is orthogonal to `A`, to `B` and to
`A * B`, and `∑ a_i^4` vanishes on `A`, then `dim A + dim B + dim C ≤ m`. Proof
(notes/gct-086-core/t3/notes.md, F2): with `X = (C1 + A)(C1 + B)` and `H = stab X`, Kneser
(L-gct-065) for `H(C1 + A)` and `H(C1 + B)`, whose product is `X` with stabilizer `H`, gives
`a + b + h ≤ dim X + dim (H ⊓ A) + dim (H ⊓ B)`; the half bound for isotropic subspaces of `H`
and Lemma P (helper `T3LemmaP`) give `dim (H ⊓ A) + dim (H ⊓ B) + 1 ≤ h`; so
`a + b ≤ dim (A + B + AB)`, and `C` lies in its orthogonal (assembly in helper `T3Assembly`). -/

theorem PEqualNP.Gct.L163 : ∀ (m : ℕ) (A B C : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, ∑ i, x i * y i = 0) → (∀ c ∈ C, (∀ a ∈ A, ∑ i, c i * a i = 0) ∧ (∀ b ∈ B, ∑ i, c i * b i = 0) ∧ ∀ a ∈ A, ∀ b ∈ B, ∑ i, c i * (a i * b i) = 0) → (∀ a ∈ A, ∑ i, a i ^ 4 = 0) → Module.finrank ℂ A + Module.finrank ℂ B + Module.finrank ℂ C ≤ m :=
  PEqualNP.Gct.Helpers.T3.t3
