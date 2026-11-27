import Mathlib
import PEqualNP.Defs.Expanders
import PEqualNP.ProofComplexity.L005
import PEqualNP.ProofComplexity.L013
import PEqualNP.ProofComplexity.L052
import PEqualNP.ProofComplexity.Helpers.ThreeCnfFamily

/-!
# Helpers for L-pcx-055: a Res(k, ⊕) refutation of the functional pigeonhole formula exists

Monotonicity of Res(k, ⊕) derivations in `k`, and the chain: unsatisfiable, so resolution
refutes it (L-pcx-005), so Res(⊕) does (L-pcx-013), so Res(1, ⊕) does (L-pcx-052), so
Res(k, ⊕) does for every `k ≥ 1`.
-/

namespace PEqualNP.ProofComplexity.Helpers.LinKWitness

open PEqualNP.ProofComplexity PEqualNP.Expanders

/-- A derivation with terms of at most `k` equations is one with terms of at most `k'`
equations, for `k ≤ k'`. -/
theorem derivation_mono {V : Type} [DecidableEq V] {k k' : ℕ} (hk : k ≤ k')
    {W : LinKLine V → LinKLine V → Prop} {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k W F π) : IsLinKDerivation k' W F π := by
  induction h with
  | nil => exact .nil
  | ax _ hF hc ih => exact .ax ih hF (fun T hT => le_trans (hc T hT) hk)
  | cut _ hC hD hcut hc ih => exact .cut ih hC hD hcut (fun T hT => le_trans (hc T hT) hk)
  | andIntro _ hC hD hand hc ih =>
      exact .andIntro ih hC hD hand (fun T hT => le_trans (hc T hT) hk)
  | weak _ hC hW hc ih => exact .weak ih hC hW (fun T hT => le_trans (hc T hT) hk)

/-- Every unsatisfiable formula over finitely many variables has a Res(k, ⊕) refutation, for
every `k ≥ 1`. -/
theorem refutation_of_unsat {V : Type} [DecidableEq V] [Fintype V] {k : ℕ} (hk : 1 ≤ k)
    (F : Set (Clause V)) (h : ¬ Satisfiable F) :
    ∃ π : List (LinKLine V), IsLinKRefutation k F π := by
  obtain ⟨π, hπ⟩ := L005 V F h
  obtain ⟨π', hπ', hlen⟩ := L013 V F π hπ
  obtain ⟨π'', hπ'', -⟩ := (L052 V F π.length).mp ⟨π', hπ', hlen⟩
  exact ⟨π'', derivation_mono hk hπ''.1, hπ''.2⟩

/-- The functional pigeonhole formula on a graph with more pigeons than holes is
unsatisfiable. -/
theorem funGraphPHP_unsat {m N : ℕ} (G : BipGraph m N) (h : N < m) :
    ¬ Satisfiable (funGraphPHP G) := by
  rintro ⟨a, ha⟩
  exact ThreeCnfFamily.graphPHP_unsat G h ⟨a, fun C hC => ha C (Or.inl hC)⟩

end PEqualNP.ProofComplexity.Helpers.LinKWitness
