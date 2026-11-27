import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- A proper subset of the lines through a point has at most q lines.
-- Outside the centre, every point reads the complement of one pencil line.
-- These tests include the maximal negative input for each single line.
theorem PEqualNP.Outside.R_meta_4598_517
    (pencil : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      0 < q → N = q^2 + q + 1 →
      (∀ m, Fintype.card {p // I p m} = q + 1) →
      (∀ p r, p ≠ r → ∃! m, I p m ∧ I r m) →
      ∀ r m, I r m → ((Finset.univ.filter (I r)).erase m).card = q ∧
        ∃ f : Fin N → Fin N, ∀ p l, p ≠ r → I r l → (I p l ↔ f p = l))
    (bound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
      (E : Finset (Fin N × Fin N)), 87 ≤ q → N = q^2 + q + 1 →
      (∀ m, Fintype.card {p // I p m} = q + 1) →
      (∀ p r, p ≠ r → ∃! m, I p m ∧ I r m) →
      IsAO2 (N+N) C →
      (∀ r m, I r m → ∃ f : Fin N → Fin N,
        (∀ p l, p ≠ r → I r l → (I p l ↔ f p = l)) ∧
        ∀ T ⊆ (Finset.univ.filter (I r)).erase m,
        C.eval (List.ofFn (fun p => decide (if p = r then T = ∅ else f p ∉ T)) ++
          List.ofFn (fun l => decide (l ∈ T))) = false) →
      let hits := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun v => decide (hits v e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) →
      4400 < C.size → E.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → (4400 : ℕ) < x5.size → x6.card ≤ (24 : ℕ) * x5.size := by
  intro q N I inst C E hq hn cols uniq hao sound
  apply bound q N I C E hq hn cols uniq hao
  intro r m hr
  obtain ⟨count, f, proj⟩ := pencil q N I (by omega) hn cols uniq r m hr
  refine ⟨f, proj, ?_⟩
  intro T hT
  let points := fun p => decide (if p = r then T = ∅ else f p ∉ T)
  let lines := fun l => decide (l ∈ T)
  change C.eval (List.ofFn points ++ List.ofFn lines) = false
  rw [← List.ofFn_fin_append points lines]
  apply sound (Fin.addCases (motive := fun _ => Bool) points lines)
  · have ht := Finset.card_le_card hT
    rw [Fintype.card_subtype]
    simpa only [Fin.addCases_right, lines, decide_eq_true_eq, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using ht.trans count.le
  · rintro ⟨p, l, hp, hx, hy⟩
    simp only [Fin.addCases_left, Fin.addCases_right, points, lines, decide_eq_true_eq] at hx hy
    by_cases he : p = r
    · have empty : T = ∅ := by simpa only [ite_eq_left he] using hx
      simp [empty] at hy
    · have avoid : f p ∉ T := by simpa only [ite_eq_right he] using hx
      have hr' := (Finset.mem_filter.mp (Finset.mem_erase.mp (hT hy)).2).2
      rw [(proj p l he hr').mp hp] at avoid
      exact avoid hy
