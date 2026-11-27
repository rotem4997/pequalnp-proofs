import PEqualNP.ProofComplexity.Helpers.LiftClassPlan

namespace PEqualNP.ProofComplexity.LiftClass

open PEqualNP.ProofComplexity

theorem stmtSem : StmtSem := by
  intro V _ F G π c hLift hπ
  induction hπ with
  | nil => exact SemDer.nil
  | @ax σ C _ hC ih =>
    obtain ⟨D, hD, rfl⟩ := hC
    obtain ⟨C', hC', hfal⟩ := hLift D hD
    refine SemDer.ax ih hC' ?_
    intro x hx hsat
    have h1 : ¬ ClauseSat (emb c x) D := fun h =>
      hx ((Helpers.linOfClause_sat _ D).mpr h)
    exact hfal _ h1 (by rw [liftAssign_emb]; exact hsat)
  | @res σ C D R _ hC hD hR ih =>
    refine SemDer.inf ih (List.mem_map.2 ⟨C, hC, rfl⟩) (List.mem_map.2 ⟨D, hD, rfl⟩) ?_
    intro x hx
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    exact hx (Helpers.lin_resolvent_sound _ hR (not_not.1 hn.1) (not_not.1 hn.2))
  | @weak σ C D _ hC hw ih =>
    have hm : S c C ∈ (σ.map (S c)) := List.mem_map.2 ⟨C, hC, rfl⟩
    refine SemDer.inf ih hm hm ?_
    intro x hx
    left
    intro hs
    exact hx (hw _ hs)

end PEqualNP.ProofComplexity.LiftClass
