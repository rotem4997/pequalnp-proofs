import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2084_1
    (cut :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
        (∀ i j : Fin n, G.Adj i j → i ∉ A) →
        (∃ i j : Fin n, G.Adj i j) →
        (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
          ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
        ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s →
          ∃ z ∉ A, ∃ t, t + 4 ≤ s ∧
            PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x z false)) t)
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
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  intro n k G A f hdeg hgirth hA hedge htau hf s hC
  classical
  obtain ⟨z, hzA, t, ht, hCt⟩ := cut n G A f hdeg hgirth hA hedge hf s hC
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
  have hk' : ∀ T : Finset (Fin n),
      (∀ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j → i ∈ T ∨ j ∈ T) →
      k - 1 ≤ T.card := by
    intro T hT
    have hcov : ∀ i j : Fin n, G.Adj i j → i ∈ insert z T ∨ j ∈ insert z T := by
      intro i j hij
      by_cases hi : i = z
      · left; rw [hi]; exact Finset.mem_insert_self z T
      · by_cases hj : j = z
        · right; rw [hj]; exact Finset.mem_insert_self z T
        · rcases hT i j ((hadj i j).2 ⟨hij, hi, hj⟩) with h | h
          · left; exact Finset.mem_insert_of_mem h
          · right; exact Finset.mem_insert_of_mem h
    have hle := htau (insert z T) hcov
    have hcard := Finset.card_insert_le z T
    omega
  have hrec := res n (k - 1) t G A z (fun x => f (Function.update x z false))
    hdeg hgirth hA hedge hzA hg hk' hCt
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
  omega
