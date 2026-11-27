import PEqualNP.Outside.L_meta_17187

/-! Closing file for L-meta-17200 (seat-clb-1, on rfrege-1's filer step from strategy, 26 Nov 2026).
The checked L-meta-17187 at N = 5: every circuit with NOT gates representing the complement of the
5 by 5 matching has at least 10 gates, so none has at most 9. Not built on this machine: it imports
an outside proof, so it goes through the public runner (law 17 (b)). -/

theorem PEqualNP.Outside.L_meta_17200 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => decide (u ≠ v)) C) := by
  rintro ⟨C, hF, hs, hR⟩
  have h := PEqualNP.Outside.L_meta_17187 5 (by norm_num) C hF hR
  omega
