import Mathlib
import PEqualNP.Defs

-- Split by the AND gates. h1: every AND gate, on inputs with at most one point and one line
-- on, agrees with one of its inputs or is a product of its inputs on disjoint parts of the input.
-- A walk from the output then ends at a product gate whose point set times line set is
-- incident; two lines share one point, so a Nechiporuk count gives N (q + 1) <= 6 gates.
-- h2: some AND gate is neither. Either bound gives the program of line prefixes.
theorem PEqualNP.Outside.R_meta_3572_641
    (h1 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) →
    (let v := fun (w : ℕ) (S : Finset (Fin (x2 + x2))) => (x4.wires (List.ofFn fun i => decide (i ∈ S))).getD w false
      ∀ (j a b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and → g.inputs = [a, b] →
        (∀ (p l : Fin x2), ∀ S ⊆ {Fin.castAdd x2 p, Fin.natAdd x2 l}, v a S = true → v b S = true) ∨
        (∀ (p l : Fin x2), ∀ S ⊆ {Fin.castAdd x2 p, Fin.natAdd x2 l}, v b S = true → v a S = true) ∨
        ∀ (p l : Fin x2), ∀ S ⊆ {Fin.castAdd x2 p, Fin.natAdd x2 l}, v a S = true → v b S = true →
          ∃ A ⊆ S, v a A = true ∧ v b (S \ A) = true) →
    x2 * x1 ≤ 100 * x4.size)
    (h2 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) →
    (¬ (let v := fun (w : ℕ) (S : Finset (Fin (x2 + x2))) => (x4.wires (List.ofFn fun i => decide (i ∈ S))).getD w false
      ∀ (j a b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and → g.inputs = [a, b] →
        (∀ (p l : Fin x2), ∀ S ⊆ {Fin.castAdd x2 p, Fin.natAdd x2 l}, v a S = true → v b S = true) ∨
        (∀ (p l : Fin x2), ∀ S ⊆ {Fin.castAdd x2 p, Fin.natAdd x2 l}, v b S = true → v a S = true) ∨
        ∀ (p l : Fin x2), ∀ S ⊆ {Fin.castAdd x2 p, Fin.natAdd x2 l}, v a S = true → v b S = true →
          ∃ A ⊆ S, v a A = true ∧ v b (S \ A) = true)) →
    x2 * x1 ≤ 100 * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : List (Finset (Fin x2))), x11.length ≤ (100 : ℕ) * x4.size ∧ (∀ (x12 : Fin x2), x3 x12 ∈ x11) ∧ ∀ (x12 : ℕ) (x13 : Finset (Fin x2)), x11[x12]? = Option.some x13 → ∃ (x15 : Finset (Fin x2)) (x16 : Finset (Fin x2)), x13 = x15 ∪ x16 ∧ (x15.card ≤ (1 : ℕ) ∨ x15 ∈ List.take x12 x11) ∧ (x16.card ≤ (1 : ℕ) ∨ x16 ∈ List.take x12 x11) := by
  intro x1 x2 x3 x4 hq hN hF huniq hm hcorr
  have lb : x2 * x1 ≤ 100 * x4.size :=
    (em _).elim (h1 x1 x2 x3 x4 hq hN hF huniq hm hcorr) (h2 x1 x2 x3 x4 hq hN hF huniq hm hcorr)
  have snoc : ∀ (xs : List (Finset (Fin x2))) (A B : Finset (Fin x2)),
      (∀ (j : ℕ) (S : Finset (Fin x2)), xs[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ xs.take j) ∧ (Y.card ≤ 1 ∨ Y ∈ xs.take j)) → (A.card ≤ 1 ∨ A ∈ xs) → (B.card ≤ 1 ∨ B ∈ xs) →
      ∀ (j : ℕ) (S : Finset (Fin x2)), (xs ++ [A ∪ B])[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ (xs ++ [A ∪ B]).take j) ∧ (Y.card ≤ 1 ∨ Y ∈ (xs ++ [A ∪ B]).take j) := by
    intro xs A B hx hA hB j S h
    by_cases hj : j < xs.length
    · rw [List.getElem?_append_left hj] at h
      obtain ⟨A', B', e, h1, h2⟩ := hx j S h
      have ht : (xs ++ [A ∪ B]).take j = xs.take j := List.take_append_of_le_length hj.le
      exact ⟨A', B', e, by rw [ht]; exact h1, by rw [ht]; exact h2⟩
    · by_cases hje : j = xs.length
      · subst hje
        rw [List.getElem?_append_right (le_refl _)] at h
        simp at h
        have ht : (xs ++ [A ∪ B]).take xs.length = xs := by simp
        exact ⟨A, B, h.symm, by rw [ht]; exact hA, by rw [ht]; exact hB⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at h
        cases h
  have chain : ∀ (ps : List (Fin x2)) (U : Finset (Fin x2)) (xs : List (Finset (Fin x2))),
      (∀ (j : ℕ) (S : Finset (Fin x2)), xs[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ xs.take j) ∧ (Y.card ≤ 1 ∨ Y ∈ xs.take j)) → (U.card ≤ 1 ∨ U ∈ xs) →
      ∃ ys : List (Finset (Fin x2)), (∀ (j : ℕ) (S : Finset (Fin x2)), ys[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ ys.take j) ∧ (Y.card ≤ 1 ∨ Y ∈ ys.take j)) ∧ ys.length = xs.length + ps.length ∧
        (∀ T ∈ xs, T ∈ ys) ∧ ((U ∪ ps.toFinset).card ≤ 1 ∨ U ∪ ps.toFinset ∈ ys) := by
    intro ps
    induction ps with
    | nil =>
      intro U xs hx hU
      exact ⟨xs, hx, by simp, fun T h => h, by simpa using hU⟩
    | cons p ps ih =>
      intro U xs hx hU
      have h1 := snoc xs U {p} hx hU (Or.inl (by simp))
      obtain ⟨ys, hy, hl, hsub, hfin⟩ := ih (U ∪ {p}) (xs ++ [U ∪ {p}]) h1 (Or.inr (by simp))
      refine ⟨ys, hy, by simp [hl]; omega, fun T hT => hsub T (by simp [hT]), ?_⟩
      have e : U ∪ (p :: ps).toFinset = U ∪ {p} ∪ ps.toFinset := by
        ext a; simp
      rw [e]; exact hfin
  have oneLine : ∀ (l : Fin x2) (xs : List (Finset (Fin x2))), (∀ (j : ℕ) (S : Finset (Fin x2)), xs[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ xs.take j) ∧ (Y.card ≤ 1 ∨ Y ∈ xs.take j)) →
      ∃ ys : List (Finset (Fin x2)), (∀ (j : ℕ) (S : Finset (Fin x2)), ys[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ ys.take j) ∧ (Y.card ≤ 1 ∨ Y ∈ ys.take j)) ∧ ys.length = xs.length + x1 ∧
        (∀ T ∈ xs, T ∈ ys) ∧ x3 l ∈ ys := by
    intro l xs hx
    have hlen : (x3 l).toList.length = x1 + 1 := by simp [hF l]
    obtain ⟨p, ps, hps⟩ : ∃ p ps, (x3 l).toList = p :: ps := by
      cases h : (x3 l).toList with
      | nil => rw [h] at hlen; simp at hlen
      | cons p ps => exact ⟨p, ps, rfl⟩
    have hpsl : ps.length = x1 := by rw [hps] at hlen; simpa using hlen
    obtain ⟨ys, hy, hl, hsub, hfin⟩ := chain ps {p} xs hx (Or.inl (by simp))
    have e : ({p} : Finset (Fin x2)) ∪ ps.toFinset = x3 l := by
      rw [← Finset.toList_toFinset (x3 l), hps]
      ext a; simp
    rw [e] at hfin
    refine ⟨ys, hy, by rw [hl, hpsl], hsub, ?_⟩
    rcases hfin with h | h
    · rw [hF l] at h; omega
    · exact h
  have all : ∀ ls : List (Fin x2), ∃ xs : List (Finset (Fin x2)), (∀ (j : ℕ) (S : Finset (Fin x2)), xs[j]? = some S → ∃ X Y : Finset (Fin x2), S = X ∪ Y ∧ (X.card ≤ 1 ∨ X ∈ xs.take j) ∧ (Y.card ≤ 1 ∨ Y ∈ xs.take j)) ∧
      xs.length = ls.length * x1 ∧ ∀ l ∈ ls, x3 l ∈ xs := by
    intro ls
    induction ls with
    | nil => exact ⟨[], fun j S h => by simp at h, by simp, by simp⟩
    | cons l ls ih =>
      obtain ⟨xs, hx, hl, hin⟩ := ih
      obtain ⟨ys, hy, hyl, hsub, hF'⟩ := oneLine l xs hx
      refine ⟨ys, hy, by rw [hyl, hl]; simp; ring, ?_⟩
      intro m hm'
      rcases List.mem_cons.mp hm' with e | e
      · rw [e]; exact hF'
      · exact hsub _ (hin m e)
  obtain ⟨xs, hx, hl, hin⟩ := all (List.finRange x2)
  refine ⟨xs, ?_, fun l => hin l (List.mem_finRange l), hx⟩
  rw [hl, List.length_finRange]
  exact lb
