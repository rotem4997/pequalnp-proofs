import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_1900_963
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      let f := fun x : Fin n → Bool => ∃ u v : Fin n, G.Adj u v ∧ x u=true ∧ x v=true
      let pivotal := fun (B : Circuit) (j : ℕ) (u v : Fin n) =>
        (⟨B.gates.set j ⟨.or,[]⟩,B.output⟩ : Circuit).eval (List.ofFn (pairInput u v))=false
      (∃ u v : Fin n, G.Adj u v) → Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x)=true ↔ f x) →
      ∃ D : Circuit, IsAO2 n D ∧ Monotone2 D ∧ D.size≤C.size ∧ (∀ x : Fin n → Bool, D.eval (List.ofFn x)=true ↔ f x) ∧
        (∀ B : Circuit, Monotone2 B → (∀ x : Fin n → Bool, B.eval (List.ofFn x)=true ↔ f x) → D.size≤B.size) ∧ (∀ j, j<D.gates.length → ∃ u v, G.Adj u v ∧ pivotal D j u v) ∧ (∀ j, j<D.gates.length → (gateAt D j).op=.and →
        (∃ u v, ¬G.Adj u v ∧ gateVal n D j (pairInput u v)=true) →
        ∃ u v a b, G.Adj u v ∧ G.Adj a b ∧ s(u,v)≠s(a,b) ∧
          pivotal D j u v ∧ pivotal D j a b))
    (coldBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x)=true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u=true ∧ x v=true) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → g.op=.and →
        ∀ (u v : Fin n), ¬G.Adj u v → gateVal n C j (pairInput u v)=false) → HasBlockCost G C.size)
    (pivotalBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Circuit),
      let f := fun x : Fin n → Bool => ∃ u v : Fin n, G.Adj u v ∧ x u=true ∧ x v=true
      let pivotal := fun (B : Circuit) (j : ℕ) (u v : Fin n) =>
        (⟨B.gates.set j ⟨.or,[]⟩,B.output⟩ : Circuit).eval (List.ofFn (pairInput u v))=false
      let leaks := fun j : ℕ => ∃ u v, ¬G.Adj u v ∧ gateVal n D j (pairInput u v)=true
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      IsAO2 n D → (∀ x : Fin n → Bool, D.eval (List.ofFn x)=true ↔ f x) → (∀ B : Circuit, Monotone2 B → (∀ x : Fin n → Bool, B.eval (List.ofFn x)=true ↔ f x) → D.size≤B.size) →
      (∀ j, j<D.gates.length → ∃ u v, G.Adj u v ∧ pivotal D j u v) →
      (∀ j, j<D.gates.length → (gateAt D j).op=.and →
        leaks j →
        ∃ u v a b, G.Adj u v ∧ G.Adj a b ∧ s(u,v)≠s(a,b) ∧
          pivotal D j u v ∧ pivotal D j a b) →
      (∃ j, j<D.gates.length ∧ (gateAt D j).op=.and ∧
        leaks j) → HasBlockCost G D.size) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x)=true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u=true ∧ x v=true) → HasBlockCost G C.size := by
  classical
  intro n G C nonempty cycle mono eval
  obtain ⟨D,dao,dm,cap,de,minimum,all,twice⟩ := normalize n G C nonempty mono eval
  have budget : HasBlockCost G D.size := by
    by_cases leaking : (∃ j, j<D.gates.length ∧ (gateAt D j).op=.and ∧
        ∃ u v, ¬G.Adj u v ∧ gateVal n D j (pairInput u v)=true)
    · exact pivotalBound n G D nonempty cycle dao de minimum all twice leaking
    · apply coldBound n G D nonempty cycle dm de
      intro j g atJ and_j u v nonedge
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp atJ
      have gate : gateAt D j=g := by
        change D.gates.getD j ⟨.or,[]⟩=g
        rw [List.getD_eq_getElem?_getD,atJ]
        rfl
      exact leaking ⟨j,hj,gate ▸ and_j,u,v,nonedge,on⟩
  obtain ⟨W,cover,cost⟩ := budget
  exact ⟨W,cover,cost.trans cap⟩
