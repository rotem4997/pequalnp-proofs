import PEqualNP.Library.L007
import PEqualNP.Library.Machines.FilterMap

/-- P is contained in NP: the verifier ignores the witness. It keeps the first component of the
pair and runs the decider on it; the empty witness always works. -/
theorem PEqualNP.Library.L010 : PEqualNP.Library.P ⊆ PEqualNP.Library.NP := by
  rintro L ⟨f, hf, hc⟩
  refine ⟨{p | p.1 ∈ L}, 0, ⟨fun p => f p.1, fun p => hf p.1, ?_⟩, fun x => ?_⟩
  · refine PEqualNP.Library.L007 _ _ _ _ _ _ _ _ _ (fun p : List Bool × List Bool => p.1) f ?_ hc
    refine PEqualNP.Library.Machines.filterMap_polyTime _ _ _
      (fun s : Bool ⊕ Bool => Sum.elim some (fun _ => none) s) ?_
    rintro ⟨x, w⟩
    simp [PEqualNP.Library.encodePair, List.filterMap_append, List.filterMap_map]
  · exact ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩
