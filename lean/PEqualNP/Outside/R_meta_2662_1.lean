import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2662_1
    (scatter : ∀ k : Nat, ∃ m : Nat, ∀ n : Nat, ∀ G : SimpleGraph (Fin n),
      (∀ a : Fin n, ∀ w : G.Walk a a, w.IsCycle → 5≤w.length) →
      ∀ (u v : Fin n) (F : Finset (Fin n × Fin n)), m≤F.card →
      (∀ p∈F, ¬G.Adj p.1 p.2) →
      (let support : Fin n × Fin n → Finset (Fin n) := fun p => {p.1,p.2} \ {u,v}
       ∀ p∈F, ∀ q∈F, p≠q → Disjoint (support p) (support q)) →
      ∃ S : Finset (Fin n), (∀ a∈S, ∀ b∈S, ¬G.Adj a b) ∧
        ∀ B : Finset (Fin n), B.card≤k → u∉B → v∉B →
        ∃ p∈F, p.1∈S\B ∧ p.2∈S\B)
    (persistent : ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             ∃ S : Finset (Fin x3), Maximal (fun T : Finset (Fin x3) => ∀ a∈T, ∀ b∈T, ¬x4.Adj a b) S ∧
          ∀ B : Finset (Fin x3), B.card≤x1 → x15∉B → x16∉B →
          ∃ p∈S\B, ∃ q∈S\B, x20 p q) → x11.card ≤ x2 * (x8.size + (1 : ℕ))) :
    ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};                             x20 x15 x15 ∨ x20 x16 x16 ∨ ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,K,bound⟩ := persistent
  obtain ⟨m,chooseSet⟩ := scatter k
  refine ⟨m,K,?_⟩
  intro n G inst deg girth C least computes T sub dirty
  apply bound n G deg girth C least computes T sub
  intro e he u v pts j own
  let hit := fun p q : Fin n => PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true
  suffices localSet : ∃ S : Finset (Fin n), (∀ p∈S, ∀ q∈S, ¬G.Adj p q) ∧
      ∀ B : Finset (Fin n), B.card≤k → u∉B → v∉B → ∃ p∈S\B, ∃ q∈S\B, hit p q by
    obtain ⟨S,indep,fault⟩ := localSet
    obtain ⟨M,incl,maximal⟩ := Finite.exists_le_maximal
      (p:=fun T : Finset (Fin n) => ∀ a∈T, ∀ b∈T, ¬G.Adj a b) indep
    refine ⟨M,maximal,?_⟩
    intro B card hu hv
    obtain ⟨p,hp,q,hq,accepted⟩ := fault B card hu hv
    exact ⟨p,Finset.sdiff_subset_sdiff_left B incl hp,q,Finset.sdiff_subset_sdiff_left B incl hq,accepted⟩
  have atEndpoint (a : Fin n) (endpoint : a=u ∨ a=v) (ha : hit a a) :
      ∃ S : Finset (Fin n), (∀ p∈S, ∀ q∈S, ¬G.Adj p q) ∧
        ∀ B : Finset (Fin n), B.card≤k → u∉B → v∉B → ∃ p∈S\B, ∃ q∈S\B, hit p q := by
    refine ⟨{a},by simp,?_⟩
    intro B _ hu hv
    have outside : a∉B := endpoint.elim (fun h => h ▸ hu) (fun h => h ▸ hv)
    exact ⟨a,by simp [outside],a,by simp [outside],ha⟩
  rcases dirty e he u v pts j own with hu|hv|⟨F,size,valid,disjoint⟩
  · exact atEndpoint u (Or.inl rfl) hu
  · exact atEndpoint v (Or.inr rfl) hv
  · obtain ⟨S,indep,robust⟩ := chooseSet n G girth u v F (by omega) (fun p hp => (valid p hp).2) disjoint
    refine ⟨S,indep,?_⟩
    intro B small hu hv
    obtain ⟨p,hF,a,b⟩ := robust B small hu hv
    exact ⟨p.1,a,p.2,b,(valid p hF).1⟩
