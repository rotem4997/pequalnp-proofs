import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3572_23
    (commonOr : ∀ (q n : ℕ) (lines : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2 + q + 1 → (∀ l, (lines l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ lines l ∧ r ∈ lines l) → Monotone2 C →
      (∀ (x : Fin (n + n) → Bool),
        Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        circuitFun (n + n) C x =
          decide (∃ p l, p ∈ lines l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      ∃ D : Circuit, D.size ≤ 100 * C.size ∧
        (∀ g ∈ D.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
        ∀ l, ∃ w : ℕ, ∀ p : Fin n,
          (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD w false =
            decide (p ∈ lines l))
    (wireSupports : ∀ (n : ℕ) (D : Circuit),
      (∀ g ∈ D.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) →
      ∃ sets : List (Finset (Fin n)), sets.length ≤ D.size ∧
        (∀ w : ℕ, let S := Finset.univ.filter (fun p : Fin n =>
            (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD w false);
          S.card ≤ 1 ∨ S ∈ sets) ∧
        ∀ j S, sets[j]? = some S → ∃ A B : Finset (Fin n), S = A ∪ B ∧
          (A.card ≤ 1 ∨ A ∈ sets.take j) ∧ (B.card ≤ 1 ∨ B ∈ sets.take j)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : List (Finset (Fin x2))), x11.length ≤ (100 : ℕ) * x4.size ∧ (∀ (x12 : Fin x2), x3 x12 ∈ x11) ∧ ∀ (x12 : ℕ) (x13 : Finset (Fin x2)), x11[x12]? = Option.some x13 → ∃ (x15 : Finset (Fin x2)) (x16 : Finset (Fin x2)), x13 = x15 ∪ x16 ∧ (x15.card ≤ (1 : ℕ) ∨ x15 ∈ List.take x12 x11) ∧ (x16.card ≤ (1 : ℕ) ∨ x16 ∈ List.take x12 x11) := by
  intro q n lines C hq hn hc hu hm hf
  obtain ⟨D, hsize, hg, hlines⟩ := commonOr q n lines C hq hn hc hu hm hf
  obtain ⟨sets, hlen, hw, hsteps⟩ := wireSupports n D hg
  refine ⟨sets, hlen.trans hsize, ?_, hsteps⟩
  intro l
  obtain ⟨w, heq⟩ := hlines l
  have hs : (Finset.univ.filter (fun p : Fin n =>
      (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD w false)) = lines l := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq p, decide_eq_true_eq]
  have h := hw w
  dsimp only at h
  rw [hs] at h
  rcases h with h | h
  · have := hc l
    omega
  · exact h
