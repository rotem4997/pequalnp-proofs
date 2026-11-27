import Mathlib.Tactic
import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3291_37
    (hLow : ∀ (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (hao : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hs : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z=false),
    let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
    (∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧
      (a ≤ 44 ∨ b ≤ 44 ∨ a*b ≤ 44*(a+b+min a b)) ∧
      (∀ p, (E.filter fun e => e.1=p).card ≤ a) ∧
      (∀ l, (E.filter fun e => e.2=l).card ≤ b)) → E.card ≤ 44*C.size)
    (hHigh : ∀ (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hq : 131 ≤ q) (hN : N=q^2+q+1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (hao : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hs : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z=false),
    let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
    (¬ (∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧
      (a ≤ 44 ∨ b ≤ 44 ∨ a*b ≤ 44*(a+b+min a b)) ∧
      (∀ p, (E.filter fun e => e.1=p).card ≤ a) ∧
      (∀ l, (E.filter fun e => e.2=l).card ≤ b))) → E.card ≤ 44*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN hcol hu hao hs
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
  have bound : E.card ≤ 44*C.size := by
    by_cases good : (∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧
      (a ≤ 44 ∨ b ≤ 44 ∨ a*b ≤ 44*(a+b+min a b)) ∧
      (∀ p, (E.filter fun e => e.1=p).card ≤ a) ∧
      (∀ l, (E.filter fun e => e.2=l).card ≤ b))
    · exact hLow q N I C (by omega) hN hcol hu hao hs good
    · exact hHigh q N I C hq hN hcol hu hao hs good
  simpa only [E,Fintype.card_subtype] using bound
