import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.ReadK PEqualNP.GenericRejection PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5180_842
    (extract : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → IsAO2 (n+n) C →
      (∀ U : Finset (Fin (n+n)), (List.finRange n).countP (fun l => decide (Fin.natAdd n l ∈ U)) ≤ q →
        (IsPrimeImplicant (n+n) C U ↔ ∃ p l, p ∈ S l ∧ U = {Fin.castAdd n p, Fin.natAdd n l})) → 100*C.size < n*q → 300 ≤ q ∧
      ∃ j < C.size, (gateAt C j).op = GateOp.or ∧
        Nat.card {l : Fin n // PEqualNP.CleanedNonEdge.wireVal (n+n) C (n+n+j) (fun i => decide (i=Fin.natAdd n l)) = true} <
          6*(q+2)*(Nat.log2 q+1) ∧
        ∃ P : Finset (Fin n), 100 < P.card ∧ ∀ p ∈ P,
          ∃ l r : Fin n, p ∈ S l ∧ p ∈ S r ∧
            let A := fun (b : Fin 2) (u : Fin n) => wireValue C (incidenceInput {p} {u}) (opnd C j b)
            A 0 l = true ∧ A 1 l = false ∧ A 0 r = false ∧ A 1 r = true)
    (crowded : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → IsAO2 (n+n) C →
      ¬IsReadK (n+n) C 2 → C.output < n+n+C.size →
      (∀ U : Finset (Fin (n+n)), (List.finRange n).countP (fun l => decide (Fin.natAdd n l ∈ U)) ≤ q →
        (IsPrimeImplicant (n+n) C U ↔ ∃ p l, p ∈ S l ∧ U = {Fin.castAdd n p, Fin.natAdd n l})) →
      (∃ j < C.size, (gateAt C j).op = GateOp.or ∧
        Nat.card {l : Fin n // PEqualNP.CleanedNonEdge.wireVal (n+n) C (n+n+j) (fun i => decide (i=Fin.natAdd n l)) = true} <
          6*(q+2)*(Nat.log2 q+1) ∧
        ∃ P : Finset (Fin n), 100 < P.card ∧ ∀ p ∈ P,
          ∃ l r : Fin n, p ∈ S l ∧ p ∈ S r ∧
            let A := fun (b : Fin 2) (u : Fin n) => wireValue C (incidenceInput {p} {u}) (opnd C j b)
            A 0 l = true ∧ A 1 l = false ∧ A 0 r = false ∧ A 1 r = true) → n*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn degree join ao reads output primes
  by_contra! small
  obtain ⟨large, witness⟩ := extract q n S C hq hn degree join ao primes small
  exact small.not_ge (crowded q n S C large hn degree join ao reads output primes witness)
