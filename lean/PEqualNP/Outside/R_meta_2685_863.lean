import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2685_863
    (charge : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
  let n := Np + Nl
  (∀ (p p' : Fin Np) (l l' : Fin Nl), p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 n C →
  (∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C z = decide (∃ (p : Fin Np) (l : Fin Nl), I p l ∧
  z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
  ∃ own : List (ℕ × List ℕ), (∀ tx ∈ own, tx.2 ≠ [] ∧
  ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < n) ∨
   (Np ≤ tx.1 ∧ tx.1 < n ∧ ∀ u ∈ tx.2, u < Np))) ∧ (∀ (p : Fin Np) (l : Fin Nl), I p l ↔
  ∃ tx ∈ own, (tx.1 = p.val ∧ Np + l.val ∈ tx.2) ∨
    (tx.1 = Np + l.val ∧ p.val ∈ tx.2)) ∧ (own.map (fun tx => tx.2.length)).sum + own.length - 1 ≤ C.size)
    (realize : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (own : List (ℕ × List ℕ)),
  let n := Np + Nl
  (∀ tx ∈ own, tx.2 ≠ [] ∧
  ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < n) ∨
   (Np ≤ tx.1 ∧ tx.1 < n ∧ ∀ u ∈ tx.2, u < Np))) → (∀ (p : Fin Np) (l : Fin Nl), I p l ↔
  ∃ tx ∈ own, (tx.1 = p.val ∧ Np + l.val ∈ tx.2) ∨
    (tx.1 = Np + l.val ∧ p.val ∈ tx.2)) →
  let D := PEqualNP.MetaComplexity.coverCircuitB n own
  D.size = (own.map (fun tx => tx.2.length)).sum + own.length - 1 ∧ ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D z = decide (∃ (p : Fin Np) (l : Fin Nl), I p l ∧
  z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (shaped : ∀ (Np Nl : ℕ) (own : List (ℕ × List ℕ)),
  let n := Np + Nl
  (∀ tx ∈ own, tx.2 ≠ [] ∧
  ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < n) ∨
   (Np ≤ tx.1 ∧ tx.1 < n ∧ ∀ u ∈ tx.2, u < Np))) → let D := PEqualNP.MetaComplexity.coverCircuitB n own
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt D
  ∃ P L : Finset ℕ, PEqualNP.TopForm.IsAO2 n D ∧
    (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length,
      w = n + i ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ P) ∧
    (∀ w ∈ L, (Np ≤ w ∧ w < n) ∨ ∃ i < D.gates.length,
      w = n + i ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ L) ∧
    ∀ i < D.gates.length, (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ a b : ℕ, (g i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  intro Np Nl I _ C free ao correct
  obtain ⟨own, tagged, covered, budget⟩ := charge Np Nl I C free ao correct
  obtain ⟨size, computes⟩ := realize Np Nl I own tagged covered
  obtain ⟨P,L,aoD,pureP,pureL,ands⟩ := shaped Np Nl own tagged
  refine ⟨PEqualNP.MetaComplexity.coverCircuitB (Np+Nl) own,P,L,aoD,computes,?_,pureP,pureL,ands⟩
  rwa [size]
