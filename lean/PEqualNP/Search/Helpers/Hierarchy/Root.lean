import PEqualNP.Defs.SearchSoS
import PEqualNP.Search.Helpers.Hierarchy.Wall
import PEqualNP.Search.Helpers.Hierarchy.Kernel

/-!
# The sum-of-squares wall on the definitions of the root

Helper module (proofs only, no statement may use it). The wall proved on the draft definitions
(`Draft.lean`, `Wall.lean`, with the kernel lemma of `Kernel.lean`), transported to the same
definitions under the definitions root (`Defs/SearchSoS.lean`).
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft

/-- A derivation on the root's definition is one on the draft's. -/
theorem xorDerivable_of_root {V : Type} [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {e : PEqualNP.ProofComplexity.LinEq V}
    (h : PEqualNP.Search.XorDerivable F d e) : XorDerivable F d e := by
  induction h with
  | ax he hw => exact XorDerivable.ax he hw
  | zero => exact XorDerivable.zero
  | add _ _ hw ih ih' => exact XorDerivable.add ih ih' hw

/-- A derivation on the draft's definition is one on the root's. -/
theorem root_of_xorDerivable {V : Type} [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ} {e : PEqualNP.ProofComplexity.LinEq V}
    (h : XorDerivable F d e) : PEqualNP.Search.XorDerivable F d e := by
  induction h with
  | ax he hw => exact PEqualNP.Search.XorDerivable.ax he hw
  | zero => exact PEqualNP.Search.XorDerivable.zero
  | add _ _ hw ih ih' => exact PEqualNP.Search.XorDerivable.add ih ih' hw

/-- The wall on the root's definitions. -/
theorem sosWall_root : ∀ (V : Type) [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d D : ℕ), 2 * D ≤ d →
    ¬ PEqualNP.Search.XorRefutable F d →
    ¬ PEqualNP.Search.SoSRefutable (PEqualNP.Search.xorSystem F) D := by
  intro V _ F d D hD hno hsos
  refine sosWall_of Kernel.kernelPSD V F d D hD (fun h => hno (root_of_xorDerivable h)) ?_
  exact hsos

end PEqualNP.Search.Helpers.HierarchyDraft
