import PEqualNP.Library.L007
import PEqualNP.Library.Machines.FilterMap

/-- P is closed under complement: run the decider, then negate the answer bit. -/
theorem PEqualNP.Library.L008 : ∀ L : Language Bool,
    L ∈ PEqualNP.Library.P → Lᶜ ∈ PEqualNP.Library.P := by
  rintro L ⟨f, hf, hc⟩
  refine ⟨fun x => !f x, fun x => ?_, ?_⟩
  · have h : x ∉ L ↔ (!f x) = true := (not_congr (hf x)).trans (by cases f x <;> simp)
    exact h
  · exact PEqualNP.Library.L007 _ _ _ _ _ _ _ _ _ f (fun b => !b) hc
      (PEqualNP.Library.Machines.filterMap_polyTime _ _ _ (fun b => some (!b))
        (fun b => by cases b <;> rfl))
