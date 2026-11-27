import PEqualNP.MetaComplexity.Helpers.Deg2Assembly
import PEqualNP.MetaComplexity.Helpers.Deg2E0
import PEqualNP.MetaComplexity.Helpers.Deg2Alpha
import PEqualNP.MetaComplexity.Helpers.Deg2Beta
import PEqualNP.MetaComplexity.Helpers.Deg2Transp2
import PEqualNP.MetaComplexity.Helpers.Deg2Transp4
import PEqualNP.MetaComplexity.Helpers.Deg2Cover2

/-- Line-degree at most 2: on an incidence between N points and N lines with no two points on two
common lines, a circuit of AND and OR gates of fan-in at most two and line-degree at most 2 that
computes the edge function has at most 48 times its size plus 2 N incident pairs. Assembled from
the cards D2-03 to D2-17 of the degree-two chain. -/
theorem PEqualNP.MetaComplexity.L649 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  PEqualNP.MetaComplexity.Deg2.assembly_of
    PEqualNP.MetaComplexity.Deg2.card10_e0 PEqualNP.MetaComplexity.Deg2.card12_alpha
    PEqualNP.MetaComplexity.Deg2.card13_beta PEqualNP.MetaComplexity.Deg2.card15_identity
    PEqualNP.MetaComplexity.Deg2.card15c_contexts PEqualNP.MetaComplexity.Deg2.card16_form
    PEqualNP.MetaComplexity.Deg2.card17_cover
