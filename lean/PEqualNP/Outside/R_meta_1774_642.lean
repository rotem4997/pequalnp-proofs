import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1774_642
  (locate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    NoFourCycle G → ∀ (C : Circuit), Monotone2 C → ∀ j a b c d,
    G.Adj a b → G.Adj c d → Owns n C j a b → Owns n C j c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∃ u v, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧ ¬ G.Adj u v ∧
      gateVal n C j (pairInput u v) = true)
  (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
    let E := fun (D : Circuit) (i : ℕ) (a b : Fin n) => G.Adj a b ∧ Owns n D i a b
    let ready := fun (D : Circuit) => Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, (gateAt D i).op = .and → ∃ a b, E D i a b
    ∀ C, IsMinimalMonoCircuit n C → ready C → ∀ j a b c d, E C j a b → E C j c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    (∃ u v, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧ ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true) →
    ∃ D : Circuit, ready D ∧ D.size ≤ C.size ∧ ∃ f : Equiv.Perm ℕ, ∀ i,
      (∃ s, ∀ a b, E D i a b → a = s ∨ b = s) ∨
      (f i ≠ j ∧ ∀ a b, E D i a b → E C (f i) a b)) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  classical
  intro n G dec triangle square live count C least computes every positive
  let bad (D : Circuit) : Set ℕ := {i | ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
    Owns n D i a b ∧ Owns n D i c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}
  change 0 < (bad C).ncard at positive
  have finite (D : Circuit) : (bad D).Finite := by
    apply (Set.finite_Iio D.gates.length).subset
    rintro i ⟨a,b,c,d,_,_,own,_⟩
    exact own.1
  obtain ⟨j,hj⟩ := (Set.ncard_pos (finite C)).mp positive
  obtain ⟨a,b,c,d,ab,cd,jab,jcd,ac,ad,bc,bd⟩ := hj
  have spot := locate n G triangle square C least.1 j a b c d ab cd jab jcd ac ad bc bd
  obtain ⟨D,⟨mono,eval,works⟩,size,f,retain⟩ :=
    exchange n G triangle square C least ⟨least.1,computes,every⟩ j a b c d ⟨ab,jab⟩ ⟨cd,jcd⟩ ac ad bc bd spot
  refine ⟨D,mono,eval,size,works,?_⟩
  change (bad D).ncard < (bad C).ncard
  let kept : Set ℕ := bad C \ {j}
  have into : Set.MapsTo f (bad D) kept := by
    intro i hi
    obtain ⟨p,q,r,s,h₁,h₂,o₁,o₂,pr,ps,qr,qs⟩ := hi
    rcases retain i with ⟨v,star⟩ | ⟨dist,old⟩
    · rcases star p q ⟨h₁,o₁⟩ with h | h
      · rcases star r s ⟨h₂,o₂⟩ with k | k
        · exact False.elim (pr (h.trans k.symm))
        · exact False.elim (ps (h.trans k.symm))
      · rcases star r s ⟨h₂,o₂⟩ with k | k
        · exact False.elim (qr (h.trans k.symm))
        · exact False.elim (qs (h.trans k.symm))
    · exact ⟨⟨p,q,r,s,h₁,h₂,(old p q ⟨h₁,o₁⟩).2,(old r s ⟨h₂,o₂⟩).2,pr,ps,qr,qs⟩,dist⟩
  have le := Set.ncard_le_ncard_of_injOn f into f.injective.injOn ((finite C).subset Set.sdiff_subset)
  have mem : j ∈ bad C := ⟨a,b,c,d,ab,cd,jab,jcd,ac,ad,bc,bd⟩
  have sizeDrop := Set.ncard_sdiff_singleton_add_one mem (finite C)
  change kept.ncard + 1 = (bad C).ncard at sizeDrop
  omega
