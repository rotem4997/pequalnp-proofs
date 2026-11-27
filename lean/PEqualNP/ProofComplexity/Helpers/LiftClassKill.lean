import PEqualNP.ProofComplexity.Helpers.LiftClassPlan

namespace PEqualNP.ProofComplexity.LiftClass

open PEqualNP.ProofComplexity

theorem kill_bridge {V : Type} [DecidableEq V] (q : LinEq (V × Fin 4)) (v : V)
    (hq : ∀ u ∈ q.1, u.1 = v) (pt : Fin 4 → Bool) (a : V × Fin 4 → Bool)
    (ha : ∀ u ∈ q.1, a u = pt u.2) :
    LinEqSat a q ↔ LinEqSat pt (q.1.image Prod.snd, q.2) := by
  unfold LinEqSat
  have : (q.1.filter (fun u => a u = true)).card
      = ((q.1.image Prod.snd).filter (fun j => pt j = true)).card := by
    refine Finset.card_bij (fun u _ => u.2) ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨Finset.mem_image_of_mem _ hu.1, ?_⟩
      rw [← ha u hu.1]; exact hu.2
    · intro u hu w hw h
      rw [Finset.mem_filter] at hu hw
      exact Prod.ext (by rw [hq u hu.1, hq w hw.1]) h
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_image] at hj
      obtain ⟨⟨u, hu, rfl⟩, h⟩ := hj
      exact ⟨u, Finset.mem_filter.2 ⟨hu, by rw [ha u hu]; exact h⟩, rfl⟩
  simp only [this]

theorem stmtKill : LiftClass.StmtKill := by
  intro V _ L v hv
  classical
  unfold lineLocalBlocks at hv
  rw [Finset.mem_biUnion] at hv
  obtain ⟨q, hqL, hvq⟩ := hv
  rw [Finset.mem_filter] at hqL
  obtain ⟨hqL, hcard⟩ := hqL
  have hq : ∀ u ∈ q.1, u.1 = v := by
    intro u hu
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
    have h1 : u.1 ∈ eqBlocks q := Finset.mem_image_of_mem _ hu
    rw [ha] at h1 hvq
    rw [Finset.mem_singleton] at h1 hvq
    rw [h1, hvq]
  have hne : (q.1.image Prod.snd).Nonempty := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
    have : (eqBlocks q).Nonempty := by rw [ha]; exact ⟨a, by simp⟩
    obtain ⟨b, hb⟩ := this
    obtain ⟨u, hu, _⟩ := Finset.mem_image.1 hb
    exact ⟨u.2, Finset.mem_image_of_mem _ hu⟩
  refine ⟨Finset.univ.filter (fun ij : Fin 10 × Fin 6 =>
      ¬ (LinEqSat (zeroPt ij.1) (q.1.image Prod.snd, q.2) ∧
         LinEqSat (onePt ij.2) (q.1.image Prod.snd, q.2))),
    stmtBlock _ _ hne, ?_⟩
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hc
  ext x
  simp only [S, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  refine ⟨q, hqL, ?_⟩
  cases hx : x v
  · rw [kill_bridge q v hq (zeroPt (c v).1) (emb c x)]
    · exact hc.1
    · intro u hu; simp [emb, hq u hu, hx]
  · rw [kill_bridge q v hq (onePt (c v).2) (emb c x)]
    · exact hc.2
    · intro u hu; simp [emb, hq u hu, hx]

end PEqualNP.ProofComplexity.LiftClass
