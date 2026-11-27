import Mathlib
import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.RefIndex

/-- Pointwise form behind L-pcx-062: the rule-by-rule description and `IsLinRefutation` pick
out the same lists. -/
theorem PEqualNP.ProofComplexity.L070 : ∀ (n : ℕ) (π : List (Finset (Finset (Fin (n + 1) × Fin n) × Bool))), ((∀ i : ℕ, i < π.length → ((∃ C : Finset ((Fin (n + 1) × Fin n) × Bool), ((∃ g : Fin (n + 1), C = Finset.univ.image (fun h : Fin n => ((g, h), true))) ∨ (∃ (g g' : Fin (n + 1)) (h : Fin n), g ≠ g' ∧ C = {((g, h), false), ((g', h), false)})) ∧ π.getD i ∅ = C.image (fun l => (({l.1} : Finset (Fin (n + 1) × Fin n)), l.2))) ∨ (∃ (j k : ℕ) (f : Finset (Fin (n + 1) × Fin n)), i < j ∧ j < π.length ∧ i < k ∧ k < π.length ∧ (f, false) ∈ π.getD j ∅ ∧ (f, true) ∈ π.getD k ∅ ∧ π.getD i ∅ = (π.getD j ∅).erase (f, false) ∪ (π.getD k ∅).erase (f, true)) ∨ (∃ j : ℕ, i < j ∧ j < π.length ∧ ∀ a : Fin (n + 1) × Fin n → Bool, (∃ q ∈ π.getD j ∅, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true)) → ∃ q ∈ π.getD i ∅, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true)))) ∧ (∅ : Finset (Finset (Fin (n + 1) × Fin n) × Bool)) ∈ π) ↔ PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π :=
  fun n π => (PEqualNP.ProofComplexity.RefIndex.refutation_php_iff n π).symm
