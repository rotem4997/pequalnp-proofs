import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.CoverPromise

-- Deleting a cubic vertex costs three edges. The cover term costs one more
-- only when the vertex occurs in a minimum cover.
theorem PEqualNP.Outside.R_meta_5018_3
    (cut : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∃ v ∉ A, (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 1) →
      ∃ z ∉ A, ∃ t, HasCircuitSize n (fun x => graphFun G A (Function.update x z false)) t ∧
        t + 3 ≤ C.size ∧
        ((∃ T : Finset (Fin n), IsVertexCover G T ∧ z ∈ T ∧
          ∀ U, IsVertexCover G U → T.card ≤ U.card) → t + 4 ≤ C.size))
    (res :
      ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (z : Fin n)
        (g : (Fin n → Bool) → Bool),
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
        (∀ i j : Fin n, G.Adj i j → i ∉ A) →
        (∃ i j : Fin n, G.Adj i j) →
        z ∉ A →
        (∀ x, g x = true ↔ (∃ a ∈ A, x a = true) ∨
          ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true) →
        (∀ T : Finset (Fin n), (∀ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
        PEqualNP.MetaComplexity.HasCircuitSize n g s →
        A.card + (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + k ≤ s + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) → (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) → (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) → PEqualNP.MetaComplexity.FanInTwo x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 → (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) → (∃ x16 ∉ x4, (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x16) x6.gates).length = (1 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  intro n k G A f C hdeg hgirth hA hedge htau hf hfan hfun hmin hread
  classical
  have hgraph : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    unfold graphFun
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hf x
  have hminimal : IsMinimalCircuit n C := by
    refine ⟨hfan, fun D hD heq => hmin D.size ⟨D, hD, le_rfl, ?_⟩⟩
    exact congrFun (heq.trans hfun)
  obtain ⟨z, hzA, t, hCt, hthree, hfour⟩ :=
    cut n G A C hdeg hgirth hA hedge hminimal (hfun.trans hgraph) hread
  rw [← hgraph] at hCt
  have hadj : ∀ i j : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i j ↔
      G.Adj i j ∧ i ≠ z ∧ j ≠ z := fun i j => SimpleGraph.deleteIncidenceSet_adj
  have hg : ∀ x : Fin n → Bool,
      f (Function.update x z false) = true ↔
        (∃ a ∈ A, x a = true) ∨
          ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true := by
    intro x
    rw [hf]
    constructor
    · rintro (⟨a, haA, ha⟩ | ⟨i, j, hij, hi, hj⟩)
      · have haz : a ≠ z := fun e => hzA (e ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using ha⟩
      · have hiz : i ≠ z := by intro e; simp [e] at hi
        have hjz : j ≠ z := by intro e; simp [e] at hj
        exact Or.inr ⟨i, j, (hadj i j).2 ⟨hij, hiz, hjz⟩,
          by simpa [Function.update_of_ne hiz] using hi,
          by simpa [Function.update_of_ne hjz] using hj⟩
    · rintro (⟨a, haA, ha⟩ | ⟨i, j, hij, hi, hj⟩)
      · have haz : a ≠ z := fun e => hzA (e ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using ha⟩
      · obtain ⟨hij, hiz, hjz⟩ := (hadj i j).1 hij
        exact Or.inr ⟨i, j, hij, by simpa [Function.update_of_ne hiz] using hi,
          by simpa [Function.update_of_ne hjz] using hj⟩
  have liftCover (T : Finset (Fin n))
      (hT : IsVertexCover (G.deleteEdges (G.incidenceSet z)) T) :
      IsVertexCover G (insert z T) := by
    intro i j hij
    by_cases hi : i = z
    · left; rw [hi]; exact Finset.mem_insert_self z T
    · by_cases hj : j = z
      · right; rw [hj]; exact Finset.mem_insert_self z T
      · rcases hT i j ((hadj i j).2 ⟨hij, hi, hj⟩) with h | h
        · left; exact Finset.mem_insert_of_mem h
        · right; exact Finset.mem_insert_of_mem h
  have hE : G.edgeSet.ncard =
      (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + 3 := by
    have hsub : G.incidenceSet z ⊆ G.edgeSet := SimpleGraph.incidenceSet_subset G z
    have hinc : (G.incidenceSet z).ncard = 3 := by
      rw [← SimpleGraph.coe_incidenceFinset, Set.ncard_coe_finset,
        SimpleGraph.card_incidenceFinset_eq_degree, ← SimpleGraph.ncard_neighborSet]
      exact hdeg z hzA
    rw [SimpleGraph.edgeSet_deleteEdges]
    have hsum := Set.ncard_sdiff_add_ncard_of_subset hsub (Set.toFinite _)
    omega
  by_cases hdrop : ∃ T : Finset (Fin n),
      IsVertexCover (G.deleteEdges (G.incidenceSet z)) T ∧ T.card < k
  · obtain ⟨T, hT, hsmall⟩ := hdrop
    have hcov := liftCover T hT
    have hle := htau (insert z T) hcov
    have hcard := Finset.card_insert_le z T
    have hminT : ∀ U, IsVertexCover G U → (insert z T).card ≤ U.card := by
      intro U hU
      have := htau U hU
      omega
    have hsave := hfour ⟨insert z T, hcov, Finset.mem_insert_self z T, hminT⟩
    have hk' : ∀ U, IsVertexCover (G.deleteEdges (G.incidenceSet z)) U → k - 1 ≤ U.card := by
      intro U hU
      have := htau (insert z U) (liftCover U hU)
      have := Finset.card_insert_le z U
      omega
    have := res n (k - 1) t G A z _ hdeg hgirth hA hedge hzA hg hk' hCt
    omega
  · have hk' : ∀ U, IsVertexCover (G.deleteEdges (G.incidenceSet z)) U → k ≤ U.card := by
      intro U hU
      exact Nat.le_of_not_gt fun hlt => hdrop ⟨U, hU, hlt⟩
    have := res n k t G A z _ hdeg hgirth hA hedge hzA hg hk' hCt
    omega
