import PEqualNP.Library.Helpers.OracleCompose

/-!
# L-lib-068: P^A is closed under polynomial-time many-one preimages

If `f` is computable in polynomial time and `S ∈ OracleP A`, then `f ⁻¹' S ∈ OracleP A`: run the
machine for `f`, then the oracle machine for `S` on its output (`Helpers/OracleCompose.lean`).
-/

namespace PEqualNP.Library

open Turing

theorem L068 : ∀ (A : Language Bool) (f : List Bool → List Bool) (S : Language Bool), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f → S ∈ PEqualNP.Library.OracleP A → ((f ⁻¹' S : Set (List Bool)) : Language Bool) ∈ PEqualNP.Library.OracleP A := by
  intro A f S ⟨c1⟩ hS
  refine Helpers.OracleCompose.ocomp_decides A (fun x : List Bool => x) _ S f (fun _ => Iff.rfl)
    c1.tm c1.inputAlphabet c1.outputAlphabet c1.time (fun a => ?_) hS
  obtain ⟨⟨s, hs⟩, hle⟩ := c1.outputsFun a
  exact ⟨s, hle, hs⟩

end PEqualNP.Library
