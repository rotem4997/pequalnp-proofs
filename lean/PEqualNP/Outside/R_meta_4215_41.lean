import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Test the two directions of every AND gate on maximal independent vertex sets.
theorem PEqualNP.Outside.R_meta_4215_41
    (bound : ∀ D : Circuit, Monotone2 D → ReadsBack 14 D → circuitFun 14 D = (fun (x : Fin 14 → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) → 27 ≤ D.size)
    (prune : ∀ (C : Circuit) (j : ℕ) (b : Fin 2),
      let F := fun (x : Fin 14 → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
      let maximal := fun (x : Fin 14 → Bool) => F x = false ∧ ∀ y, x ≤ y → F y = false → y = x
      let T := fun (j : ℕ) (b : Fin 2) (x : Fin 14 → Bool) => wireVal 14 C (opnd C j b) x
      IsAO2 14 C → circuitFun 14 C = F → j < C.size → (gateAt C j).op = .and →
      (∀ x, maximal x → T j b x = true → T j (1-b) x = true) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 14 D ∧ circuitFun 14 D = F ∧ D.size < C.size)
    (diamonds : ∀ C : Circuit,
      let F := fun (x : Fin 14 → Bool) => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
      let W := wireVal 14 C
      let o := opnd C
      let A := fun j => (gateAt C j).op = GateOp.and
      let V := fun w (p l : Fin 14) => W w (pairInput p l)
      let Z := fun w => V w 0 0 = false ∧ V w 7 7 = false
      let R := fun (w a : ℕ) => 14+a=w ∨ InCone 14 C a (w-14)
      C.size = 27 → IsAO2 14 C → circuitFun 14 C = F →
      ∀ g, A g → V (14+g) 0 7 = true → (∀ b, Z (o g b)) →
      (∀ b, ∃ x, F x = false ∧ (∀ y, x ≤ y → F y = false → y=x) ∧ W (o g b) x = true ∧ W (o g (1-b)) x = false) →
      ¬ ∃ a, R (o g 0) a ∧ R (o g 1) a ∧ A a ∧ Z (14+a) ∧
        ∃ b : Fin 2, V (o a b) 0 0 = true ∧ V (o a (1-b)) 7 7 = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13 := by
  intro C _V _birth size ao distinct good
  have mono : Monotone2 C := by
    intro g hg
    exact ⟨ao.1 g hg, (ao.2.2 g hg).le⟩
  have low := bound C mono ao.2.1 good
  intro j op _live pairOn singles common
  let a := common.choose
  have h0 := common.choose_spec.1
  have h1 := common.choose_spec.2
  have hj : j < C.size := by
    by_contra! large
    have defaultGate : gateAt C j = ⟨.or,[]⟩ := List.getD_eq_default _ _ large
    rw [defaultGate] at op
    contradiction
  apply diamonds C (by omega) ao good j op pairOn singles ?_ ⟨a,h0.1,h1.1,h0.2.1,⟨h0.2.2.1,h0.2.2.2.1⟩,h0.2.2.2.2⟩
  intro b
  by_contra! bad
  obtain ⟨D,dm,db,dg,ds⟩ := prune C j b ao good hj op (by
    intro x mx tx
    have h := bad x mx.1 mx.2 tx
    simpa using h)
  have impossible := bound D dm db dg
  omega
