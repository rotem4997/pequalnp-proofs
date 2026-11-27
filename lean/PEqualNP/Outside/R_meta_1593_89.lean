import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Nat.Find
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1593_89 :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool),
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = true ↔ ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s →
        A.card + G.edgeSet.ncard + k ≤ s + 1) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (s : ℕ),
      (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
      s + 1 = A.card + G.edgeSet.ncard + T.card →
      (∀ x : Fin n → Bool, f x = true ↔ ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨ ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  classical
  intro lower upper n G A hdeg hgirth hA hedge
  let f : (Fin n → Bool) → Bool := fun x => @decide
    ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)
  have hf : ∀ x : Fin n → Bool, f x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
    intro x
    simp only [f, decide_eq_true_eq]
  have coversExist : ∃ k : ℕ, ∃ T : Finset (Fin n),
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ T.card = k := by
    exact ⟨n, Finset.univ, by simp, by simp⟩
  let k := Nat.find coversExist
  obtain ⟨T, hcover, hTk⟩ := Nat.find_spec coversExist
  have minimum : ∀ U : Finset (Fin n),
      (∀ i j : Fin n, G.Adj i j → i ∈ U ∨ j ∈ U) → k ≤ U.card := by
    intro U hU
    exact Nat.find_min' coversExist ⟨U, hU, rfl⟩
  obtain ⟨a, b, hab⟩ := hedge
  have chosen : ∃ z : Fin n, z ∈ T ∧ z ∉ A := by
    rcases hcover a b hab with ha | hb
    · exact ⟨a, ha, hA a b hab⟩
    · exact ⟨b, hb, hA b a hab.symm⟩
  obtain ⟨z, hzT, hzA⟩ := chosen
  have hzdeg : G.degree z = 3 := by
    simpa only [SimpleGraph.ncard_neighborSet] using hdeg z hzA
  have nz : (G.neighborFinset z).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hzdeg]
    decide
  obtain ⟨v, hv⟩ := nz
  have hzv : G.Adj z v := by simpa using hv
  have hvdeg : G.degree v = 3 := by
    simpa only [SimpleGraph.ncard_neighborSet] using hdeg v (hA v z hzv.symm)
  have nsub : ¬ G.neighborFinset v ⊆ {z} := by
    intro hs
    have hh := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree, hvdeg, Finset.card_singleton] at hh
    omega
  obtain ⟨w, hw, hwz⟩ := Finset.not_subset.mp nsub
  have hvw : G.Adj v w := by simpa using hw
  have hwne : w ≠ z := by simpa using hwz
  let K := G.deleteIncidenceSet z
  have hedgeK : ∃ i j : Fin n, K.Adj i j := by
    refine ⟨v, w, ?_⟩
    exact SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hvw, G.ne_of_adj hzv.symm, hwne⟩
  have hcoverK : ∀ i j : Fin n, K.Adj i j → i ∈ T.erase z ∨ j ∈ T.erase z := by
    intro i j hij
    obtain ⟨hijG, hiz, hjz⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hij
    rcases hcover i j hijG with hi | hj
    · exact Or.inl (Finset.mem_erase.mpr ⟨hiz, hi⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hjz, hj⟩)
  have card_eq (J : SimpleGraph (Fin n)) : J.edgeFinset.card = J.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  have he : K.edgeSet.ncard = G.edgeSet.ncard - 3 := by
    simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hzdeg]
      using G.card_edgeFinset_deleteIncidenceSet z
  have hpositive : 0 < K.edgeSet.ncard := by
    rw [← card_eq K]
    apply Finset.card_pos.mpr
    obtain ⟨i, j, hij⟩ := hedgeK
    exact ⟨s(i, j), by simpa using hij⟩
  have htcard : (T.erase z).card + 1 = k := by
    have he := Finset.card_erase_add_one hzT
    omega
  refine ⟨z, hzA, ?_⟩
  intro s hs
  have hbound := lower n k G A f hdeg hgirth hA ⟨a, b, hab⟩ minimum hf s hs
  let t := A.card + K.edgeSet.ncard + (T.erase z).card - 1
  have hbudget : t + 1 = A.card + K.edgeSet.ncard + (T.erase z).card := by
    dsimp [t]
    omega
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    omega
  · apply upper n K A (T.erase z) _ t (Or.inr hedgeK) hcoverK hbudget
    intro x
    simp only [decide_eq_true_eq, K, SimpleGraph.deleteIncidenceSet]
