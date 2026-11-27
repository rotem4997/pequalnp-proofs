import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2718_1
    (geometry : let D : Finset (Fin 13) := {0,1,3,9}
    let A := fun (p l : Fin 13) => ∃ d ∈ D, p=l+d
    let L := fun (S : Finset (Fin 13)) l => ∀ p ∈ S, ¬ A p l
    let M := fun (S : Finset (Fin 13)) => ∀ p ∉ S, ∃ l, L S l ∧ A p l
let B := fun (S : Finset (Fin 13)) => (∃ l, ∀ p ∈ S, A p l) ∨ ∃ p, ∀ l, L S l → A p l
    ∀ S, M S → ¬B S → S.card=3 ∨ (∃ T : Finset (Fin 13), T.card=3 ∧ ∀ j, j ∈ T ↔ L S j))
    (allMaximal : let D : Finset (Fin 13) := {0,1,3,9}
    let A := fun (p l : Fin 13) => ∃ d ∈ D, p=l+d
    let L := fun (S : Finset (Fin 13)) l => ∀ p ∈ S, ¬ A p l
    let M := fun (S : Finset (Fin 13)) => ∀ p ∉ S, ∃ l, L S l ∧ A p l
    let X := fun (S : Finset (Fin 13)) (v : Fin 26) => decide
      ((∃ p ∈ S, v=Fin.castAdd 13 p) ∨ ∃ l, v=Fin.natAdd 13 l ∧ L S l)
    ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
    (∀ p l, A p l → circuitFun 26 C (fun v => decide (v=Fin.castAdd 13 p ∨ v=Fin.natAdd 13 l))=true) →
    (∀ S, M S → circuitFun 26 C (X S)=false) → False)
    (triangle : let D : Finset (Fin 13) := {0,1,3,9}
    let A := fun (p l : Fin 13) => ∃ d ∈ D, p=l+d
    let L := fun (S : Finset (Fin 13)) l => ∀ p ∈ S, ¬ A p l
    let M := fun (S : Finset (Fin 13)) => ∀ p ∉ S, ∃ l, L S l ∧ A p l
    let X := fun (S : Finset (Fin 13)) (v : Fin 26) => decide
      ((∃ p ∈ S, v=Fin.castAdd 13 p) ∨ ∃ l, v=Fin.natAdd 13 l ∧ L S l)
    let B := fun (S : Finset (Fin 13)) => (∃ l, ∀ p ∈ S, A p l) ∨ ∃ p, ∀ l, L S l → A p l
    ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
    (∀ p l, A p l → circuitFun 26 C (fun v => decide (v=Fin.castAdd 13 p ∨ v=Fin.natAdd 13 l))=true) →
    (∀ T, M T → B T → circuitFun 26 C (X T)=false) →
    ∀ S, (S.card=3 ∨ (∃ T : Finset (Fin 13), T.card=3 ∧ ∀ j, j ∈ T ↔ L S j)) → M S → circuitFun 26 C (X S)=false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ)) := by
  intro D good C hc
  exfalso
  apply allMaximal C hc.1 hc.2.1 hc.2.2.1
  intro S hm
  by_cases h : (∃ l : Fin 13, ∀ p ∈ S, ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d) ∨
      (∃ p : Fin 13, ∀ l : Fin 13, (∀ i ∈ S, ¬∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), i=l+d) →
        ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d)
  · have off := hc.2.2.2 S hm h
    convert off using 2 <;> (funext v; apply decide_congr; rfl)
  · exact triangle C hc.1 hc.2.1 hc.2.2.1 (fun T ht hb => by
      have off := hc.2.2.2 T ht hb
      convert off using 2 <;> (funext v; apply decide_congr; rfl)) S (geometry S hm h) hm
