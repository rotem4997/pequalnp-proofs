import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2662_724
    (h_single : ∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      2*r+1 ≤ n →
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (u v : Fin n) (j : Fin C.gates.length), G.Adj u v →
        let onPair := fun p q : Fin n => PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true
        let outside := fun t : Fin n × Fin n => ({t.1,t.2} : Finset (Fin n)) \ {u,v}
        (onPair u u ∨ onPair v v) →
        ∃ F : Finset (Fin n × Fin n), F.card = r ∧
          (∀ t ∈ F, onPair t.1 t.2 ∧ ¬ G.Adj t.1 t.2) ∧
          ∀ t ∈ F, ∀ w ∈ F, t ≠ w → Disjoint (outside t) (outside w))
    (h_pack : ∃ m c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset,
        (∀ e ∈ T, ∀ u v : Fin n, e = s(u,v) → ∀ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v →
          let onPair := fun p q : Fin n => PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true
          let outside := fun t : Fin n × Fin n => ({t.1,t.2} : Finset (Fin n)) \ {u,v}
          ∃ F : Finset (Fin n × Fin n), F.card = m + 3 ∧
            (∀ t ∈ F, onPair t.1 t.2 ∧ ¬ G.Adj t.1 t.2) ∧
            ∀ t ∈ F, ∀ w ∈ F, t ≠ w → Disjoint (outside t) (outside w)) →
        T.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};                             x20 x15 x15 ∨ x20 x16 x16 ∨ ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  classical
  obtain ⟨m,c,hc⟩ := h_pack
  let q := 2*(m+3)+1
  refine ⟨m,c+q*q,?_⟩
  intro n G inst hdeg hgirth C hmin hfun T hsub hall
  by_cases hn : q ≤ n
  · apply le_trans _ (Nat.mul_le_mul_right _ (Nat.le_add_right c (q*q)))
    apply hc n G hdeg hgirth C hmin hfun T hsub
    intro e he u v heq j hj
    have hadj : G.Adj u v := by
      have hh := hsub he
      simpa [heq] using hh
    rcases hall e he u v heq j hj with hu | hv | hp
    · exact h_single (m+3) n G hn hdeg hgirth C hmin.1 u v j hadj (Or.inl hu)
    · exact h_single (m+3) n G hn hdeg hgirth C hmin.1 u v j hadj (Or.inr hv)
    · exact hp
  · have hSym : Fintype.card (Sym2 (Fin n)) ≤ n*n := by
      simpa using Fintype.card_le_of_surjective (Sym2.mk (α := Fin n)).uncurry Sym2.mk_surjective
    calc
      T.card ≤ Fintype.card (Sym2 (Fin n)) := Finset.card_le_univ T
      _ ≤ n*n := hSym
      _ ≤ q*q := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ c+q*q := Nat.le_add_left _ _
      _ ≤ (c+q*q)*(C.size+1) := by
        simpa using Nat.mul_le_mul_left (c+q*q) (show 1 ≤ C.size+1 by omega)
