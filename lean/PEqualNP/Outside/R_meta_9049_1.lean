import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Isolate the finite geometry from the general cover-charge bound.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_9049_1
    (geometry : NoFourCycle (SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))))
    (coverLower : ∀ S : Finset (Fin 26), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))) S → 13 ≤ S.card)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      2 ≤ (junk G C).card → ∃ S : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → x3.size ≤ (63 : ℕ) → (13 : ℕ) + (PEqualNP.TopForm.Ustar x1 x3).card ≤ (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  let canonical : DecidableRel (SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))).Adj := inferInstance
  intro G inst C eq least top many small
  subst G
  have same : inst = canonical := Subsingleton.elim _ _
  subst inst
  have edges : (SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))).edgeFinset.Nonempty := by
    refine ⟨s(0,13), SimpleGraph.mem_edgeFinset.mpr ?_⟩
    decide
  obtain ⟨S,covers,bound⟩ := charge 26 (SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))) C geometry edges least top many
  have lower := coverLower S covers
  omega
