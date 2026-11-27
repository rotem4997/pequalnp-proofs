import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2976_418
    (normalize : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1)
    (charge : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (D : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p q l m, p ≠ q → l ≠ m → ¬ ((p,l) ∈ E ∧ (p,m) ∈ E ∧ (q,l) ∈ E ∧ (q,m) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (P+L) D →
      (∀ x : Fin (P+L) → Bool, PEqualNP.MetaComplexity.circuitFun (P+L) D x =
        decide (∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      PEqualNP.ReadK.IsReadK (P+L) D 1 →
      ∃ (A : Finset (Fin P)) (B : Finset (Fin L)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ D.size + 1)
    (build : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 Bool.false ∧ x14 ∈ x8 Bool.true) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
  intro P L I inst C square ao correct
  classical
  let E : Finset (Fin P × Fin L) := Finset.univ.filter (fun e => I e.1 e.2)
  have spec (p : Fin P) (l : Fin L) : (p,l) ∈ E ↔ I p l := by simp [E]
  obtain ⟨D,dao,dev,dsz,dr⟩ := normalize P L I C square ao correct
  have de (x : Fin (P + L) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (P+L) D x =
      decide (∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
    simpa only [spec] using dev x
  have sq : ∀ p q l m, p ≠ q → l ≠ m → ¬ ((p,l) ∈ E ∧ (p,m) ∈ E ∧ (q,l) ∈ E ∧ (q,m) ∈ E) := by
    simpa only [spec] using square
  obtain ⟨A,B,covers,paid⟩ := charge P L E D sq dao de dr
  obtain ⟨F,W,fao,sz,ev,sides,hands⟩ := build P L E A B covers
  refine ⟨F,W false,W true,fao,fun x => ?_,by omega,?_,?_,hands⟩
  · simpa only [spec] using ev x
  · intro w hw
    rcases sides false w hw with ⟨_,hb⟩|h
    · exact Or.inl (by simpa using hb)
    · exact Or.inr h
  · intro w hw
    rcases sides true w hw with ⟨hn,hb⟩|h
    · exact Or.inl ⟨by simpa using hb,hn⟩
    · exact Or.inr h
