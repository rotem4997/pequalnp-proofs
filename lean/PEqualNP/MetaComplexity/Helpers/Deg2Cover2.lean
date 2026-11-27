import PEqualNP.MetaComplexity.Helpers.Deg2Cover
import PEqualNP.MetaComplexity.Helpers.Deg2Transp

/-!
# D2-17 (cover), with the identity supplied

The cover card of the degree-two build, in the statement of the plan: `cv_cover_of_identity`
applied to `card15_identity`.
-/

namespace PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

/-- D2-17 (cover). On the cleaned circuit every incident pair is pinned, served, in `F_2` or a
marker edge. -/
theorem card17_cover (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone) :
    ∀ p w : Fin N, I p w →
      (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I :=
  cv_cover_of_identity (fun I D hwf hc hd x => card15_identity I D hwf hc hd x) I D hwf hc hd hcl

end PEqualNP.MetaComplexity.Deg2
