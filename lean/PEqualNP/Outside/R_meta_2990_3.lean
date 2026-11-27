import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2990_3
    (occurrences : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      300 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → PEqualNP.MetaComplexity.Monotone2 C →
      C.output < N+N+C.size → (∀ j g, C.gates[j]? = some g → ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a < b ∧ b < N+N+j) →
      (∀ p l, I p l → PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) →
      let paths := fun k : Fin C.size =>
        (C.gates.foldl (fun (w : List ℕ) g => w ++ [(if w.length = N+N+k.val then 1 else 0) +
          (g.inputs.map fun i => w.getD i 0).sum]) (List.replicate (N+N) 0)).getD C.output 0
      N*(q+1) ≤ 1 + ∑ k : Fin C.size, paths k)
    (shared : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      300 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → PEqualNP.MetaComplexity.Monotone2 C →
      C.output < N+N+C.size → (∀ j g, C.gates[j]? = some g → ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a < b ∧ b < N+N+j) →
      (∀ p l, I p l → PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) →
      let paths := fun k : Fin C.size =>
        (C.gates.foldl (fun (w : List ℕ) g => w ++ [(if w.length = N+N+k.val then 1 else 0) +
          (g.inputs.map fun i => w.getD i 0).sum]) (List.replicate (N+N) 0)).getD C.output 0
      N ≤ ∑ k : Fin C.size, (paths k - 100) → N*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hN degree join mono out ordered pos neg
  classical
  let paths := fun k : Fin C.size =>
        (C.gates.foldl (fun (w : List ℕ) g => w ++ [(if w.length = N+N+k.val then 1 else 0) +
          (g.inputs.map fun i => w.getD i 0).sum]) (List.replicate (N+N) 0)).getD C.output 0
  have low : N*(q+1) ≤ 1+∑ k : Fin C.size, paths k :=
    occurrences q N I C hq hN degree join mono out ordered pos neg
  by_contra! small
  apply (Nat.not_le_of_gt small) (shared q N I C hq hN degree join mono out ordered pos neg ?_)
  change N ≤ ∑ k : Fin C.size, (paths k - 100)
  have cap : (∑ k : Fin C.size, paths k) ≤ ∑ k : Fin C.size, (100+(paths k-100)) :=
    Finset.sum_le_sum (fun k _ => by omega)
  rw [Finset.sum_add_distrib] at cap
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at cap
  norm_cast at cap
  rw [Nat.mul_comm C.size 100] at cap
  rw [Nat.mul_add, Nat.mul_one] at low
  omega
