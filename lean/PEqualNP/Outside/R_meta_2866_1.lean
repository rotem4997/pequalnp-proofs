import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The OR gate bound is proved by the lemma main in L_meta_2862.
-- Only the deficit after counting OR gates needs to be covered by AND gates.
theorem PEqualNP.Outside.R_meta_2866_1
    (orLower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      2 * q ^ 2 + 1 ≤ (C.gates.filter (fun g => g.op.eval [true, false])).length)
    (andDeficit : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      let ors := (C.gates.filter (fun g => g.op.eval [true, false])).length
      2 * q ^ 2 + 1 ≤ ors → 100 * ors < N * q →
      N * q - 100 * ors ≤ 100 * (C.gates.filter (fun g => !(g.op.eval [true, false]))).length) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      have singleton : Fin N → Fin N → Bool := fun p i => decide (i = p);
      have wire : ℕ → Fin N → Fin N → Bool := fun i p l =>
        (C.wires (List.ofFn (singleton p) ++ List.ofFn (singleton l))).getD i false;
      have product : ℕ → ℕ → Fin N → Fin N → Bool := fun a b p l => wire a p l && wire b p l;
      ∀ marked : Finset ℕ,
        (∀ (j : ℕ) (g : Gate) (a b : ℕ),
          C.gates[j]? = some g → g.op = GateOp.and → g.inputs = [a, b] → j ∉ marked →
          (∃ i ∈ [a, b], ∀ p l : Fin N, product a b p l = wire i p l) ∨
            ((∀ p l : Fin N, product a b p l = true → I p l) →
              ∀ p r l m : Fin N,
                product a b p l = true → product a b r m = true → p = r ∨ l = m)) →
        100 * marked.card < N * q → N * q ≤ 100 * C.size := by
  intro q N I _ C hq hN lineCard uniqueLines mono accepts sound singleton wire product marked _ _
  let isOr (g : Gate) : Bool := g.op.eval [true, false]
  let ors := (C.gates.filter isOr).length
  change N * q ≤ 100 * C.gates.length
  have countLower : 2 * q ^ 2 + 1 ≤ ors :=
    orLower q N I C hq hN lineCard uniqueLines mono accepts sound
  by_cases sufficient : N * q ≤ 100 * ors
  · exact sufficient.trans (Nat.mul_le_mul_left 100 (List.length_filter_le _ _))
  · have remaining := andDeficit q N I C hq hN lineCard uniqueLines mono accepts sound
      countLower (Nat.lt_of_not_ge sufficient)
    change N * q - 100 * ors ≤ 100 * (C.gates.filter (fun g => !(isOr g))).length at remaining
    have partition : C.gates.length =
        ors + (C.gates.filter (fun g => !(isOr g))).length := by
      simpa only [ors, List.countP_eq_length_filter, decide_not, Bool.decide_coe] using
        (List.length_eq_countP_add_countP isOr (l := C.gates))
    omega
