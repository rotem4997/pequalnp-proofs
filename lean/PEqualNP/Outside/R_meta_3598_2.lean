import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3598_2
    (acceptingPrefix : ∀ (n : ℕ) (C : Circuit), Monotone2 C → n ≤ C.output → C.output < n+C.size →
      (∃ g : Gate, C.gates[C.output-n]? = some g ∧ g.op = .and) →
      (∀ j (g : Gate), C.gates[j]? = some g → ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a < b ∧ b < n+j) →
      ∃ (K : Circuit) (a b : ℕ), Monotone2 K ∧ K.size+1 ≤ C.size ∧ a < b ∧ b < n+K.size ∧
let val := fun (w : ℕ) (x : Fin n → Bool) => (K.wires (List.ofFn x)).getD w false;
        (∀ x, circuitFun n C x = true → val a x = true ∧ val b x = true) ∧
        (∀ x y, val a x = true → val b y = true → circuitFun n C (fun i => x i || y i) = true))
    (crossIncidence : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (K : Circuit) (a b : ℕ),
      300 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 K → a < b → b < n+n+K.size →
      let read := fun (w : ℕ) (x : Fin (n+n) → Bool) => (K.wires (List.ofFn x)).getD w false
      (∀ p l, I p l → let x := fun i : Fin (n+n) => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l);
                       read a x = true ∧ read b x = true) →
      (∀ x y : Fin (n+n) → Bool, read a x = true → read b y = true →
        let z := fun i => x i || y i
        Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        ∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
      n*q ≤ 100*(K.size+1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I inst C hq hn hcard hplane hmono above below hg shape hit reject
  obtain ⟨K,a,b,hK,budget,hab,hb,accept,joinAccept⟩ :=
    acceptingPrefix (n+n) C hmono above below hg shape
  apply le_trans _ (Nat.mul_le_mul_left 100 budget)
  apply crossIncidence q n I K a b hq hn hcard hplane hK hab hb
  · intro p l hp
    exact accept _ (hit p l hp)
  · intro x y hx hy z hsize
    by_contra empty
    have no := reject z hsize empty
    have yes := joinAccept x y hx hy
    exact Bool.noConfusion (no.symm.trans yes)
