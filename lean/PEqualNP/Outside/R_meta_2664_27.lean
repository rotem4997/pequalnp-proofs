import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2664_27
  (hfull : ∀ (n : ℕ) (I : Fin n → Fin n → Prop) (D : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 D →
    (∀ p l : Fin n, I p l → PEqualNP.MetaComplexity.circuitFun (n+n) D (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) = true) →
    (∀ x : Fin (n+n) → Bool, (¬ ∃ p l : Fin n, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) → PEqualNP.MetaComplexity.circuitFun (n+n) D x = false) →
    (∀ x : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) D x = true ↔ ∃ p l : Fin n, l ∈ (Finset.univ : Finset (Fin n)) ∧ I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true))
  (hdrop : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I], 199 ≤ q → n = q ^ 2 + q + 1 →
    (∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q + 1) →
    (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, I p l ∧ I r l) →
    ∀ (S : Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
    S.Nonempty → PEqualNP.MetaComplexity.Monotone2 D → (∀ x : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) D x = true ↔ ∃ p l : Fin n, l ∈ S ∧ I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
    ∃ removed ∈ S, ∃ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧
      (∀ x : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) E x = true ↔ ∃ p l : Fin n, l ∈ (S.erase removed) ∧ I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) ∧ 100 * E.size + q ≤ 100 * D.size) :
  ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit), 199 ≤ q → n = q ^ 2 + q + 1 →
    (∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q + 1) →
    (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, I p l ∧ I r l) →
    PEqualNP.MetaComplexity.Monotone2 D → D.output < n+n+D.size →
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[j]? = some g →
      ∃ u v : ℕ, g.inputs = [u,v] ∧ u < v ∧ v < n+n+j) →
    (∀ p l : Fin n, I p l → PEqualNP.MetaComplexity.circuitFun (n+n) D (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) = true) →
    (∀ x : Fin (n+n) → Bool, (¬ ∃ p l : Fin n, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) → PEqualNP.MetaComplexity.circuitFun (n+n) D x = false) →
    ∀ T : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[j]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∉ T →
      ¬ ((∀ w ∈ g.inputs, ∃ y : Fin n → Bool,
        (D.wires (List.ofFn y ++ List.replicate n false)).getD w false ≠
        (D.wires (List.ofFn y ++ List.replicate n true)).getD w false) ∨
        ∀ w ∈ g.inputs, ∃ y : Fin n → Bool,
        (D.wires (List.replicate n false ++ List.ofFn y)).getD w false ≠
        (D.wires (List.replicate n true ++ List.ofFn y)).getD w false)) →
    100 * T.card < n * q → n * q ≤ 100 * D.size := by
  classical
  intro q n I inst D hq hn hdeg hpair hm _ _ hp hz T _ _
  let exactOn := fun (S : Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) => (∀ x : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) D x = true ↔ ∃ p l : Fin n, l ∈ S ∧ I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)
  have go (k : ℕ) : ∀ (S : Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
      S.card = k → PEqualNP.MetaComplexity.Monotone2 D → exactOn S D → k * q ≤ 100 * D.size := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S D hk hmono hex
      by_cases hs : S.Nonempty
      · obtain ⟨l, hl, E, he, hx, hcost⟩ := hdrop q n I hq hn hdeg hpair S D hs hmono hex
        have hc := Finset.card_erase_of_mem hl
        have hpos := Finset.card_pos.mpr hs
        have hlt : (S.erase l).card < k := by omega
        have hprev := ih _ hlt (S.erase l) E rfl he hx
        have hsucc : k = (S.erase l).card + 1 := by omega
        rw [hsucc, Nat.add_mul, Nat.one_mul]
        omega
      · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst S
        have hk0 : k = 0 := by simpa using hk.symm
        simp [hk0]
  exact go n Finset.univ D (by simp) hm (hfull n I D hm hp hz)
