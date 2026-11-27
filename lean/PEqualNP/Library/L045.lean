import PEqualNP.Library.Machines.NormalForm

/-- NP verifiers in normal form: the witness length bound can be built into the relation. -/
theorem PEqualNP.Library.L045 : ∀ L ∈ PEqualNP.Library.NP, ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair R ∧ (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) ∧ ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x, w) ∈ R := by
  rintro L ⟨R, p, ⟨fR, hfR, cR⟩, hL⟩
  refine ⟨{q | q.2.length ≤ p.eval q.1.length ∧ q ∈ R}, p,
    ⟨fun q => decide (q.2.length ≤ p.eval q.1.length) && fR q, fun q => ?_,
      PEqualNP.Library.Machines.nf_decider fR p cR⟩, fun x w h => h.1, fun x => hL x⟩
  exact (and_congr decide_eq_true_iff.symm (hfR q)).trans Bool.and_eq_true_iff.symm
