import PEqualNP.ProofComplexity.L018

/-!
# Helpers: a Res(+) size lower bound for 3-CNFs refutes the candidate 3 premise L-alg-003

If for every polynomial some unsatisfiable 3-CNF needs more Res(+) lines than the polynomial
allows, then no polynomial bounds Res(lin) refutations of unsatisfiable 3-CNFs: the bridge
L-pcx-018 turns a Res(lin) refutation into a Res(+) refutation at most twice as long.
-/

namespace PEqualNP.Search.Helpers

open Polynomial

/-- The shape of the family lemma of seat-pcx-1 refutes the statement of L-alg-003. -/
theorem family_refutes_L003
    (hfam : ∀ p : Polynomial ℕ, ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))),
      (∀ C ∈ F, C.card ≤ 3) ∧
      ¬ PEqualNP.ProofComplexity.Satisfiable
          (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
      ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)),
        PEqualNP.ProofComplexity.IsLinRefutation
          (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → p.eval n < π.length) :
    ¬ (∃ p : Polynomial ℕ, ∀ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))),
      (∀ C ∈ F, C.card ≤ 3) →
      ¬ PEqualNP.ProofComplexity.Satisfiable
          (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) →
      ∃ π : List (PEqualNP.Search.LinClause n),
        PEqualNP.Search.IsResLinRefutation
          (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π ∧ π.length ≤ p.eval n) := by
  rintro ⟨p, hp⟩
  obtain ⟨n, F, h3, hunsat, hlong⟩ := hfam (2 * p + 1)
  obtain ⟨π, hπ, hlen⟩ := hp n F h3 hunsat
  obtain ⟨π', hπ', hlen'⟩ := PEqualNP.ProofComplexity.L018 n _ π hπ
  have h := hlong π' hπ'
  simp only [eval_add, eval_mul, eval_one, eval_ofNat] at h
  omega

end PEqualNP.Search.Helpers
