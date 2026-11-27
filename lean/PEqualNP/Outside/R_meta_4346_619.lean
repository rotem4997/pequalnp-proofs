import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

-- Choose a least circuit on the sparse inputs. Redundant gates can change proof-tree counts
-- without changing any answer, so use the short-proof bound again after minimizing.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4346_619
    (orLower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ p l, I p l → circuitFun (N+N) C (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      2 * q^2 + 1 ≤ (C.gates.filter (fun g => g.op.eval [true,false])).length)
    (shortBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let short := Fintype.card {e : Fin N × Fin N //
        let v := (readVectors C (N+N) [e.1.val,N+e.2.val] 2).getD C.output []
        I e.1 e.2 ∧ ([2,2] ∈ v ∨ [1,1] ∈ v ∨ [2,1] ∈ v)}
      300 ≤ q → (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) → N*q ≤ 2*short → N*q ≤ 100*C.size)
    (deficit : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ p l, I p l → circuitFun (N+N) C (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let short := Fintype.card {e : Fin N × Fin N //
        let v := (readVectors C (N+N) [e.1.val,N+e.2.val] 2).getD C.output []
        I e.1 e.2 ∧ ([2,2] ∈ v ∨ [1,1] ∈ v ∨ [2,1] ∈ v)}
      2*short < N*q →
      (∀ D : Circuit, IsAO2 (N+N) D →
        (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
          circuitFun (N+N) D z = circuitFun (N+N) C z) → C.size ≤ D.size) →
      let ors := (C.gates.filter (fun g => g.op.eval [true,false])).length
      2*q^2+1 ≤ ors → 100*ors < N*q →
      N*q - 100*ors ≤ 100*(C.size-ors)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : ℕ :=     Fintype.card       { x6 : Fin x2 × Fin x2 //         have x7 : List (List ℕ) := (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑x6.1, x2 + ↑x6.2] (2 : ℕ)).getD x5.output [];         x3 x6.1 x6.2 ∧ ([(2 : ℕ), (2 : ℕ)] ∈ x7 ∨ [(1 : ℕ), (1 : ℕ)] ∈ x7 ∨ [(2 : ℕ), (1 : ℕ)] ∈ x7) };   (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → (2 : ℕ) * x6 < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C
  dsimp only
  intro big order degree unique original accepts rejects _few
  classical
  let Agrees (D : Circuit) : Prop := ∀ z : Fin (N+N) → Bool,
    Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      circuitFun (N+N) D z = circuitFun (N+N) C z
  let Has (k : ℕ) : Prop := ∃ D : Circuit, IsAO2 (N+N) D ∧ Agrees D ∧ D.size = k
  have nonempty : ∃ k, Has k := ⟨C.size,C,original,fun _ _ => rfl,rfl⟩
  obtain ⟨D, aD, agrees, sizeD⟩ := Nat.find_spec nonempty
  have budget : D.size ≤ C.size := by
    rw [sizeD]
    exact Nat.find_min' nonempty ⟨C,original,fun _ _ => rfl,rfl⟩
  have least (A : Circuit) (aA : IsAO2 (N+N) A)
      (eq : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        circuitFun (N+N) A z = circuitFun (N+N) D z) : D.size ≤ A.size := by
    rw [sizeD]
    exact Nat.find_min' nonempty ⟨A,aA,fun z nz => (eq z nz).trans (agrees z nz),rfl⟩
  have pos (p l : Fin N) (on : I p l) : circuitFun (N+N) D
      (fun w => decide (w = Fin.castAdd N p ∨ w = Fin.natAdd N l)) = true := by
    rw [agrees]
    · exact accepts p l on
    · have noInter (r : Fin N) : Fin.natAdd N r ≠ Fin.castAdd N p := by
        intro eq
        have nums := congrArg Fin.val eq
        have hp := p.isLt
        change N + r.val = p.val at nums
        omega
      have simpSet :
          (Finset.univ.filter (fun r : Fin N =>
            decide (Fin.natAdd N r = Fin.castAdd N p ∨ Fin.natAdd N r = Fin.natAdd N l) = true)) =
            {l} := by
        ext r
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,
          noInter r,false_or,Fin.natAdd_inj,Finset.mem_singleton]
      rw [Fintype.card_subtype, simpSet, Finset.card_singleton]
      omega
  have neg (z : Fin (N+N) → Bool) (cap : Fintype.card {l : Fin N //
      z (Fin.natAdd N l) = true} ≤ q)
      (absent : ¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
      circuitFun (N+N) D z = false := by
    rw [agrees z cap]
    exact rejects z cap absent
  let traces := Fintype.card {e : Fin N × Fin N //
    let v := (readVectors D (N+N) [e.1.val,N+e.2.val] 2).getD D.output []
    I e.1 e.2 ∧ ([2,2] ∈ v ∨ [1,1] ∈ v ∨ [2,1] ∈ v)}
  apply le_trans ?_ (Nat.mul_le_mul_left 100 budget)
  by_cases short : N*q ≤ 2*traces
  · exact shortBound q N I D big unique aD neg short
  · let ors := (D.gates.filter (fun g => g.op.eval [true,false])).length
    have or_le : ors ≤ D.size := List.length_filter_le _ _
    by_cases enough : N*q ≤ 100*ors
    · exact enough.trans (Nat.mul_le_mul_left 100 or_le)
    · have manyOR : 2*q^2+1 ≤ ors := orLower q N I D big order degree unique aD pos neg
      have rest := deficit q N I D big order degree unique aD pos neg
        (Nat.lt_of_not_ge short) least manyOR (Nat.lt_of_not_ge enough)
      change N*q - 100*ors ≤ 100*(D.size-ors) at rest
      omega
