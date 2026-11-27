import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_3475_317
    (small : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (E : Finset (Fin N × Fin N)),
      1 ≤ q → (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      C.size ≤ 4400 → E.card ≤ 24 * C.size)
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let hits := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) →
      4400 < C.size → E.card ≤ 24 * C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let hits := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) → E.card ≤ 24 * C.size := by
  intro q N I _ C E hq hN cols uniq hao sound hits accepted dense
  by_cases budget : C.size ≤ 4400
  · exact small q N I C E (by omega) uniq hao sound
      (fun e he => ⟨(accepted e he).1, (accepted e he).2.1⟩) budget
  · exact large q N I C E hq hN cols uniq hao sound accepted dense (by omega)
