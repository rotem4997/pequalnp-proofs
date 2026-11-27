import PEqualNP.Defs

/-! L-gct-092, reduction to doubly centred level spaces: if every level space of doubly centred
matrices has dimension at most `G`, then every level space has dimension at most `G + 2n`.
Proof: let `phi` send a matrix to its row sums and column sums. For a level space `L`, the
subspace `L ⊓ ker phi` is level and doubly centred, so it has dimension at most `G`, and by
rank-nullity `dim L = dim phi(L) + dim (L ⊓ ker phi) ≤ 2n + G`. -/

theorem PEqualNP.Gct.L092 : ∀ (n G : ℕ), (∀ K : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ K, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0)) → (∀ t ∈ K, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ K ≤ G) → ∀ L : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ L ≤ G + 2 * n := by
  intro n G hG L hL
  let phi : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin n → ℂ) :=
    LinearMap.prod (LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j))
      (LinearMap.pi fun j => ∑ i, LinearMap.proj (i, j))
  have hK : Module.finrank ℂ (L ⊓ LinearMap.ker phi : Submodule ℂ _) ≤ G := by
    apply hG
    · intro t ht
      have h0 : phi t = 0 := ht.2
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have := congrFun (congrArg Prod.fst h0) i
        simpa [phi, LinearMap.sum_apply] using this
      · have := congrFun (congrArg Prod.snd h0) j
        simpa [phi, LinearMap.sum_apply] using this
    · intro t ht
      exact hL t ht.1
  have hrn : Module.finrank ℂ (L.map phi) + Module.finrank ℂ (L ⊓ LinearMap.ker phi : Submodule ℂ _)
      = Module.finrank ℂ L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (phi.submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  have hmap : Module.finrank ℂ (L.map phi) ≤ 2 * n := by
    have := Submodule.finrank_le (L.map phi)
    simpa [Module.finrank_prod, two_mul] using this
  omega
