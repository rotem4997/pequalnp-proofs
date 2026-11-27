import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Extract a charged family of stars, then represent each star by a chain of binary unions.
theorem PEqualNP.Outside.R_meta_5761_1
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (D : Circuit) (U : Finset ℕ),
      (∀ p q l r, p ≠ q → l ≠ r → ¬ ((p,l) ∈ E ∧ (p,r) ∈ E ∧ (q,l) ∈ E ∧ (q,r) ∈ E)) →
      IsAO2 (n+m) D →
      (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      let g := NestedCover.gateAt D
      (∀ w ∈ U, w < n+m ∨
        ∃ i < D.size, w = n+m+i ∧ (g i).op = .or ∧ ∀ u ∈ (g i).inputs, u ∈ U) →
      (∀ i < D.size, (g i).op = .and → ∀ u ∈ (g i).inputs, u ∈ U) →
      ∃ (A : Finset (Fin n ⊕ Fin m)) (W : (Fin n ⊕ Fin m) → Finset (Fin n × Fin m)),
        (∀ e ∈ E, ∃ c ∈ A, e ∈ W c) ∧
        (∀ c ∈ A, ∀ e ∈ W c, c = Sum.inl e.1 ∨ c = Sum.inr e.2) ∧
        (∀ c ∈ A, (W c).Nonempty ∧ 2 * (W c).card ≤ n + m + D.size + 1) ∧
        A.card + ∑ c ∈ A, (W c).card ≤ D.size + 1)
    (chain : ∀ (n m : ℕ) (S : Finset (Fin n × Fin m)), S.Nonempty →
      ∃ (T : Finset ℕ) (F : ℕ → Finset (Fin n × Fin m)),
        T ⊆ Finset.range (2 * S.card - 1) ∧
        F (2 * S.card - 2) = S ∧ T.card + 1 = S.card ∧
        (∀ x, x ∉ T → (F x).card ≤ 1) ∧
        ∀ x ∈ T, 2 ≤ x ∧ F x = F (x - 2) ∪ F (x - 1)) :
    ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (D : Circuit) (U : Finset ℕ),
      (∀ p q l r, p ≠ q → l ≠ r → ¬ ((p,l) ∈ E ∧ (p,r) ∈ E ∧ (q,l) ∈ E ∧ (q,r) ∈ E)) →
      IsAO2 (n+m) D →
      (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      let g := NestedCover.gateAt D
      (∀ w ∈ U, w < n+m ∨
        ∃ i < D.size, w = n+m+i ∧ (g i).op = .or ∧ ∀ u ∈ (g i).inputs, u ∈ U) →
      (∀ i < D.size, (g i).op = .and → ∀ u ∈ (g i).inputs, u ∈ U) →
      let k := n+m+D.size
      ∃ (A : Finset (Fin n ⊕ Fin m)) (R T : (Fin n ⊕ Fin m) → Finset ℕ)
        (F : (Fin n ⊕ Fin m) → ℕ → Finset (Fin n × Fin m)) (a b : ℕ → ℕ) (t : ℕ),
        let W := fun c => (R c).biUnion (F c)
        (∀ e ∈ E, ∃ c ∈ A, e ∈ W c) ∧
        (∀ c ∈ A, ∀ e ∈ W c, c = Sum.inl e.1 ∨ c = Sum.inr e.2) ∧
        (∀ c ∈ A, R c ⊆ Finset.range k ∧ T c ⊆ Finset.range k ∧
          (∀ x < k, x ∉ T c → (F c x).card ≤ 1) ∧
          ∀ x ∈ T c, a x < x ∧ b x < x ∧ F c x = F c (a x) ∪ F c (b x)) ∧
        A.card ≤ t ∧ (∑ c ∈ A, (R c).card) ≤ t ∧ 2*t+(∑ c ∈ A, (T c).card) ≤ D.size+1 := by
  classical
  intro n m E D U hfour hao hfun g hclosed hand k
  obtain ⟨A, W, hcov, hinc, hsize, hcost⟩ := stars n m E D U hfour hao hfun hclosed hand
  have packed (c : Fin n ⊕ Fin m) (hc : c ∈ A) := chain n m (W c) (hsize c hc).1
  choose T F hT hroot hcard hleaf hjoin using packed
  let unions (c : Fin n ⊕ Fin m) := if h : c ∈ A then T c h else ∅
  let values (c : Fin n ⊕ Fin m) := if h : c ∈ A then F c h else fun _ => ∅
  let roots (c : Fin n ⊕ Fin m) : Finset ℕ := {2 * (W c).card - 2}
  have atRoot (c) (hc : c ∈ A) : (roots c).biUnion (values c) = W c := by
    simpa [roots, values, hc] using hroot c hc
  refine ⟨A, roots, unions, values, (· - 2), (· - 1), A.card, ?_, ?_, ?_, le_rfl, ?_, ?_⟩
  · intro e he
    obtain ⟨c,hc,hmem⟩ := hcov e he
    refine ⟨c, hc, ?_⟩
    change e ∈ (roots c).biUnion (values c)
    rwa [atRoot c hc]
  · intro c hc e he
    apply hinc c hc e
    rwa [← atRoot c hc]
  · intro c hc
    have hbound := (hsize c hc).2
    have hpos := Finset.card_pos.mpr (hsize c hc).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [roots] using (show 2 * (W c).card - 2 < n + m + D.size by omega)
    · simpa [unions, hc] using (hT c hc).trans (Finset.range_mono (show 2 * (W c).card - 1 ≤ n + m + D.size by omega))
    · intro x _ hx
      simpa [values, hc] using hleaf c hc x (by simpa [unions, hc] using hx)
    · intro x hx
      obtain ⟨h, he⟩ := hjoin c hc x (by simpa [unions, hc] using hx)
      exact ⟨(show x - 2 < x by omega), (show x - 1 < x by omega), by simpa [values, hc] using he⟩
  · simp [roots]
  · have eqsum : (∑ c ∈ A, (unions c).card) + A.card = ∑ c ∈ A, (W c).card := by
      calc
        _ = ∑ c ∈ A, ((unions c).card + 1) := by simp [Finset.sum_add_distrib]
        _ = _ := Finset.sum_congr rfl (fun c hc => by simpa [unions, hc] using hcard c hc)
    omega
