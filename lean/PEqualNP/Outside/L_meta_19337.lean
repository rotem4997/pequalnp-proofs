import PEqualNP.Library.LRAT.Floor301Cert

/-!
# L-meta-19337: no circuit with NOT gates of at most 5 gates represents the 4 by 4 graph with mask 301

The certificate and its check are in `PEqualNP.Library.LRAT.Floor301Cert` (seat-gct-2).
-/

theorem PEqualNP.Outside.L_meta_19337 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) C :=
  PEqualNP.Library.LRAT.Floor301Cert.floor301
