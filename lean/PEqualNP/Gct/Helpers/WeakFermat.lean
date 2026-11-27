import PEqualNP.Defs
import PEqualNP.Gct.L061

/-! Helper for L-gct-063: L-gct-061 (Fermat bound) transferred to the index `Fin n × Fin n`,
by the same reindexing as in `MainAssembly.bound_of_fermat`. Helper, not a recorded lemma. -/

namespace PEqualNP.Gct.Helpers

theorem fermat_prod (n : ℕ) (W : Submodule ℂ (Fin n × Fin n → ℂ))
    (h2 : ∀ x ∈ W, ∑ i, x i ^ 2 = 0) (h3 : ∀ x ∈ W, ∑ i, x i ^ 3 = 0) :
    3 * Module.finrank ℂ W ≤ n * n := by
  let e : (Fin n × Fin n → ℂ) ≃ₗ[ℂ] (Fin (n * n) → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ finProdFinEquiv.symm
  have hs : ∀ (r : ℕ) (x : Fin n × Fin n → ℂ), ∑ i, (e x) i ^ r = ∑ j, x j ^ r := fun r x =>
    Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
  have key := PEqualNP.Gct.L061 (n * n) (W.map (e : _ →ₗ[ℂ] _))
    (by
      rintro y ⟨x, hx, rfl⟩
      exact (hs 2 x).trans (h2 x hx))
    (by
      rintro y ⟨x, hx, rfl⟩
      exact (hs 3 x).trans (h3 x hx))
  rwa [LinearEquiv.finrank_map_eq] at key

end PEqualNP.Gct.Helpers
