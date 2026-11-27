import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection

-- Count useful OR gates in a single column, then isolate an OR gate shared across many columns.
theorem PEqualNP.Outside.R_meta_3378_17
    (column : ∀ (n : ℕ) (C : Circuit) (s : Finset (Fin n)) (l : Fin n),
      IsAO2 (n + n) C → C.output < n + n + C.size →
      (∀ p ∈ s, C.eval (incidenceInput {p} {l}) = true) →
      C.eval (incidenceInput sᶜ {l}) = false →
      ∃ J : Finset ℕ, s.card ≤ J.card + 1 ∧ ∀ j ∈ J, j < C.size ∧
        (gateAt C j).op = .or ∧
        wireValue C (incidenceInput sᶜ {l}) (n + n + j) = false ∧
        ∃ u v : ℕ, (gateAt C j).inputs = [u, v] ∧
          (∃ a b : Fin n, wireValue C (incidenceInput {a} {l}) u = true ∧
            wireValue C (incidenceInput {b} {l}) v = true) ∧
          ∀ p : Fin n, wireValue C (incidenceInput {p} {l}) u = true →
            wireValue C (incidenceInput {p} {l}) v = false)
    (sharing : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      300 ≤ q → n = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p p' : Fin n, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l) →
      IsAO2 (n + n) C → C.output < n + n + C.size →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∃ j < C.size, (gateAt C j).op = .or ∧ ∃ u v : ℕ,
        (gateAt C j).inputs = [u, v] ∧ ∃ K : Finset (Fin n), 100 < K.card ∧
        ∀ l ∈ K, wireValue C (incidenceInput (S l)ᶜ {l}) (n + n + j) = false ∧
          (∃ a b : Fin n, wireValue C (incidenceInput {a} {l}) u = true ∧
            wireValue C (incidenceInput {b} {l}) v = true) ∧
          ∀ p : Fin n, wireValue C (incidenceInput {p} {l}) u = true →
            wireValue C (incidenceInput {p} {l}) v = false) →
      n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C hq shape sizeLine common hC output accept reject
  have each (l : Fin n) := column n C (S l) l hC output (accept l)
    (reject _ _ (by simp; omega) (by
      intro k hk
      simp only [Finset.mem_singleton] at hk
      subst k
      exact disjoint_compl_right))
  choose large enough useful using each
  let K (j : ℕ) := (Finset.univ.filter fun l : Fin n => j ∈ large l)
  by_cases heavy : ∃ j < C.size, 100 < (K j).card
  · obtain ⟨j, hj, hjcount⟩ := heavy
    obtain ⟨l₀, hl₀⟩ := Finset.card_pos.mp (show 0 < (K j).card by omega)
    have cert (l : Fin n) (hl : l ∈ K j) := useful l j (Finset.mem_filter.mp hl).2
    obtain ⟨_, hop, _, u, v, huv, _, _⟩ := cert l₀ hl₀
    apply sharing q n S C hq shape sizeLine common hC output accept reject
    refine ⟨j, hj, hop, u, v, huv, K j, hjcount, ?_⟩
    intro l hl
    obtain ⟨_, _, hoff, a, b, hab, hne, hdisj⟩ := cert l hl
    have heq : [a, b] = [u, v] := hab.symm.trans huv
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨hoff, hne, hdisj⟩
  · have small (j : ℕ) (hj : j ∈ Finset.range C.size) : (K j).card ≤ 100 :=
      Nat.le_of_not_gt (fun h => heavy ⟨j, Finset.mem_range.mp hj, h⟩)
    have cardJ (l : Fin n) :
        (large l).card = ∑ j ∈ Finset.range C.size, (if j ∈ large l then 1 else 0) := by
      rw [← Finset.sum_filter]
      have heq : (Finset.range C.size).filter (fun j => j ∈ large l) = large l := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨And.right, fun h => ⟨(useful l j h).1, h⟩⟩
      simp [heq]
    calc
      n * q = ∑ _ : Fin n, q := by simp
      _ ≤ ∑ l : Fin n, (large l).card := by
        apply Finset.sum_le_sum
        intro l _
        have h := enough l
        rw [sizeLine] at h
        omega
      _ = ∑ j ∈ Finset.range C.size, (K j).card := by
        simp_rw [cardJ]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact (Finset.card_filter _ _).symm
      _ ≤ ∑ _j ∈ Finset.range C.size, 100 := Finset.sum_le_sum small
      _ = 100 * C.size := by simp [Nat.mul_comm]
