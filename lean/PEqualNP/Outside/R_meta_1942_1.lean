import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1942_1 :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
       2 ≤ q → N = q ^ 2 + q + 1 →
       (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
       (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
       PEqualNP.TopForm.IsAO2 (N + N) C →
       (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
       Fintype.card { e : Fin N × Fin N // I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true } ≤ 33 * C.size) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
       2 ≤ q → N = q ^ 2 + q + 1 →
       (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
       (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
       PEqualNP.TopForm.IsAO2 (N + N) C →
       (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
       Fintype.card { e : Fin N × Fin N // I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true } ≤ 33 * C.size) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
       2 ≤ q → N = q ^ 2 + q + 1 →
       (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
       (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
       PEqualNP.TopForm.IsAO2 (N + N) C →
       (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
       PEqualNP.ReadK.IsReadK (N + N) C 2 →
       Fintype.card { e : Fin N × Fin N // I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false } ≤ 34 * C.size) →
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  intro c1 c2 c3 q N I _ C hq hN hline huniq hao hfun hr2
  have hline' : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1 := by
    intro l
    rw [Fintype.card_subtype]
    exact hline l
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let Ey : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true)
  let Ex : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true)
  let Ed : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false)
  have hE_eq : E = (Finset.univ : Finset (Fin N)).biUnion
      (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    ext ⟨p, l⟩
    simp [E]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun l : Fin N => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    intro l1 _ l2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp hx2
    exact hne (Prod.mk.inj heq).2.symm
  have hE_card : E.card = N * (q + 1) := by
    rw [hE_eq, Finset.card_biUnion hdisj]
    have hach : ∀ l : Fin N, ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card = q + 1 := by
      intro l
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), hline l]
    simp [hach]
  have hsub : E ⊆ (Ey ∪ Ex) ∪ Ed := by
    intro e he
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_union, Ey, Ex, Ed, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hy : PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val)
    · cases hx : PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val)
      · exact Or.inr ⟨he, rfl, rfl⟩
      · exact Or.inl (Or.inr ⟨he, rfl⟩)
    · exact Or.inl (Or.inl ⟨he, rfl⟩)
  have hcov : E.card ≤ Ey.card + Ex.card + Ed.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Ey ∪ Ex) Ed
    have h3 := Finset.card_union_le Ey Ex
    omega
  have b1 := c1 q N I C hq hN hline' huniq hao hfun
  have b2 := c2 q N I C hq hN hline' huniq hao hfun
  have b3 := c3 q N I C hq hN hline' huniq hao hfun hr2
  rw [Fintype.card_subtype] at b1 b2 b3
  change Ey.card ≤ 33 * C.size at b1
  change Ex.card ≤ 33 * C.size at b2
  change Ed.card ≤ 34 * C.size at b3
  have hle : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
