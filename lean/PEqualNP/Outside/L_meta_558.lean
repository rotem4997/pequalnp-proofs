import PEqualNP.Outside.L_meta_522
import PEqualNP.MetaComplexity.L559

/-- Exact additivity: on graphs with every cycle and every walk between distinct vertices of
degree at least 3 of length at least 7, the least size of the edge function with extra
OR-variables OR a non-constant function on fresh inputs is the sum of the two least sizes plus
one gate. Closing file: the checked conditional L-meta-559 applied to the outside proof of
L-meta-522. -/
theorem PEqualNP.Outside.L_meta_558 : ∀ (n k c d s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) r ↔ d ≤ r) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ d + c + 1 ≤ s) :=
  PEqualNP.MetaComplexity.L559 PEqualNP.Outside.L_meta_522
