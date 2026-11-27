import PEqualNP.Outside.L_meta_307
import PEqualNP.Outside.L_meta_473
import PEqualNP.Outside.L_meta_474
import PEqualNP.Outside.L_meta_475
import PEqualNP.Outside.L_meta_478
import PEqualNP.Outside.L_meta_479
import PEqualNP.Outside.L_meta_489
import PEqualNP.Outside.L_meta_622
import PEqualNP.Outside.L_meta_501
import PEqualNP.Outside.L_meta_285
import PEqualNP.Outside.L_meta_286
import PEqualNP.Outside.L_meta_290
import PEqualNP.Outside.L_meta_492
import PEqualNP.MetaComplexity.L554

theorem PEqualNP.Outside.L_meta_444 :
    ∃ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) PEqualNP.MetaComplexity.encodeLgp r ∧ ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2) :=
  PEqualNP.MetaComplexity.L554
    PEqualNP.Outside.L_meta_307
    PEqualNP.Outside.L_meta_473
    PEqualNP.Outside.L_meta_474
    PEqualNP.Outside.L_meta_475
    PEqualNP.Outside.L_meta_478
    PEqualNP.Outside.L_meta_479
    PEqualNP.Outside.L_meta_489
    PEqualNP.Outside.L_meta_622
    PEqualNP.Outside.L_meta_501
    PEqualNP.Outside.L_meta_285
    PEqualNP.Outside.L_meta_286
    PEqualNP.Outside.L_meta_290
    PEqualNP.Outside.L_meta_492
