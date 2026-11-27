import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1896_52
    (compiler : ∀ (C : Circuit), Monotone2 C → ∀ A : (Fin 13 × Fin 4) → Fin 26 → Bool,
      (∀ e, circuitFun 26 C (A e) = true) →
      ∃ zs : List (Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4)), zs.length ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ∧
        ∀ y : Fin 26 → Bool, circuitFun 26 C y = false → (zs.foldl (fun (D : Finset (Fin 13 × Fin 4) → Prop) (ab : Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4)) (U : Finset (Fin 13 × Fin 4)) => D U ∨ (U ⊆ ab.1 ∪ ab.2 ∧ D ab.1 ∧ D ab.2)) (fun U : Finset (Fin 13 × Fin 4) => U = ∅ ∨ ∃ k : Fin 26, y k = false ∧ ∀ e ∈ U, A e k = true)) Finset.univ)
    (geometry : ∀ (s : Fin 16) (a : Fin 13) (b : Fin 3),
      let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let X := Finset.univ.filter fun p : Fin 13 => (([4544,2464,6464,5440,4416,3332,5264,3204,3076,2336,6400,5376,5136,6164,6148,6160] : List Nat).getD s.val 0).testBit (((p - a) * ([1,3,9] : List (Fin 13)).getD b.val 0).val)
      (∀ v ∉ X, ∃ l, (∀ p ∈ X, ¬ I p l) ∧ I v l) ∧
        (¬ ∃ l, ∀ p ∈ X, I p l) ∧ ¬ ∃ v, ∀ l : Fin 13, (∀ p ∈ X, ¬ I p l) → I v l)
    (obstruction : ∀ zs : List (Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4)), zs.length ≤ 50 →
      ∃ (s : Fin 16) (a : Fin 13) (b : Fin 3),
      let A := fun (e : Fin 13 × Fin 4) (k : Fin 26) => decide (k = Fin.castAdd 13 (e.1 + ([0,1,3,9] : List (Fin 13)).getD e.2.val 0) ∨ k = Fin.natAdd 13 e.1)
      let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let X := Finset.univ.filter fun p : Fin 13 => (([4544,2464,6464,5440,4416,3332,5264,3204,3076,2336,6400,5376,5136,6164,6148,6160] : List Nat).getD s.val 0).testBit (((p - a) * ([1,3,9] : List (Fin 13)).getD b.val 0).val)
      let y := fun k : Fin 26 => decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬ I p l)
      ¬ (zs.foldl (fun (D : Finset (Fin 13 × Fin 4) → Prop) (ab : Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4)) (U : Finset (Fin 13 × Fin 4)) => D U ∨ (U ⊆ ab.1 ∪ ab.2 ∧ D ab.1 ∧ D ab.2)) (fun U : Finset (Fin 13 × Fin 4) => U = ∅ ∨ ∃ k : Fin 26, y k = false ∧ ∀ e ∈ U, A e k = true)) Finset.univ) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C mono yes no
  by_contra! low
  let A := fun (e : Fin 13 × Fin 4) (k : Fin 26) => decide (k = Fin.castAdd 13 (e.1 + ([0,1,3,9] : List (Fin 13)).getD e.2.val 0) ∨ k = Fin.natAdd 13 e.1)
  have hA : ∀ e, circuitFun 26 C (A e) = true := by
    rintro ⟨l,d⟩
    apply yes
    fin_cases d <;> simp
  obtain ⟨zs,len,reach⟩ := compiler C mono A hA
  obtain ⟨s,a,b,bad⟩ := obstruction zs (by omega)
  obtain ⟨maximal,nonlinear,nonpencil⟩ := geometry s a b
  exact bad (reach _ (no _ maximal ⟨nonlinear,nonpencil⟩))
