import PEqualNP.Defs

-- Every incident pair is single on the line side (L-meta-2970, checked), single on the
-- point side (L-meta-2972), or read twice on both sides (L-meta-2974). The three counts
-- give at most 44 gates per size unit, so n times q is at most 100 times the size.
theorem PEqualNP.Outside.R_meta_3378_44
    (lineSide : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size)
    (pointSide : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size)
    (doubleSide : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C hq hn hline hjoin hC _ hright hfalse
  -- the two input layouts agree: points first, then lines
  have hof : ∀ z : Fin (n + n) → Bool, List.ofFn z =
      PEqualNP.GenericRejection.incidenceInput
        (Finset.univ.filter fun p : Fin n => z (Fin.castAdd n p) = true)
        (Finset.univ.filter fun l : Fin n => z (Fin.natAdd n l) = true) := by
    intro z
    rw [List.ofFn_add]
    unfold PEqualNP.GenericRejection.incidenceInput
    congr 1
    · congr 1
      funext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.decide_eq_true]
      rfl
    · congr 1
      funext i
      simp
  -- soundness with at most q lines on, in the function form
  have hsound : ∀ (z : Fin (n + n) → Bool),
      Fintype.card { l : Fin n // z (Fin.natAdd n l) = true } ≤ q →
      (¬∃ (p : Fin n) (l : Fin n), p ∈ S l ∧ z (Fin.castAdd n p) = true ∧
        z (Fin.natAdd n l) = true) →
      PEqualNP.MetaComplexity.circuitFun (n + n) C z = false := by
    intro z hcard hno
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [hof z]
    apply hfalse
    · rw [Fintype.card_subtype] at hcard
      exact hcard
    · intro l hl
      rw [Finset.disjoint_left]
      intro p hp hpX
      exact hno ⟨p, l, hp, (Finset.mem_filter.mp hpX).2, (Finset.mem_filter.mp hl).2⟩
  have hsound1 : ∀ (z : Fin (n + n) → Bool),
      Fintype.card { l : Fin n // z (Fin.natAdd n l) = true } ≤ 1 →
      (¬∃ (p : Fin n) (l : Fin n), p ∈ S l ∧ z (Fin.castAdd n p) = true ∧
        z (Fin.natAdd n l) = true) →
      PEqualNP.MetaComplexity.circuitFun (n + n) C z = false := by
    intro z hcard hno
    exact hsound z (by omega) hno
  have hfree : ∀ (a b c d : Fin n), a ≠ b → c ≠ d →
      ¬(a ∈ S c ∧ b ∈ S c ∧ a ∈ S d ∧ b ∈ S d) := by
    intro a b c d hab hcd h
    obtain ⟨l, _, huniq⟩ := hjoin a b hab
    exact hcd ((huniq c ⟨h.1, h.2.1⟩).trans (huniq d ⟨h.2.2.1, h.2.2.2⟩).symm)
  -- every incident pair is accepted, in the function form
  have hedge : ∀ (p l : Fin n), p ∈ S l →
      PEqualNP.MetaComplexity.circuitFun (n + n) C
        (fun k : Fin (n + n) => decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l)) = true := by
    intro p l hp
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [hof]
    have hX : (Finset.univ.filter fun p' : Fin n =>
        decide (Fin.castAdd n p' = Fin.castAdd n p ∨ Fin.castAdd n p' = Fin.natAdd n l) = true)
          = {p} := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
      have := p'.isLt
      omega
    have hY : (Finset.univ.filter fun l' : Fin n =>
        decide (Fin.natAdd n l' = Fin.castAdd n p ∨ Fin.natAdd n l' = Fin.natAdd n l) = true)
          = {l} := by
      ext l'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
      have := p.isLt
      omega
    rw [hX, hY]
    exact hright l p hp
  have h1 := lineSide n (fun p l => p ∈ S l) C hfree hC hsound1
  have h2 := pointSide q n (fun p l => p ∈ S l) C (by omega) hn
    (fun l => by convert (Fintype.card_coe (S l)).trans (hline l)) hjoin hC hsound
  have h3 := doubleSide q n (fun p l => p ∈ S l) C (by omega) hn
    (fun l => by convert (Fintype.card_coe (S l)).trans (hline l)) hjoin hC hsound
  rw [Fintype.card_subtype] at h1 h2 h3
  -- count the incident pairs
  have htotal : (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2).card = n * (q + 1) := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    have hrow : ∀ l : Fin n, (∑ p : Fin n, if p ∈ S l then 1 else 0) = q + 1 := by
      intro l
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact hline l
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hcover : (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2) ⊆
      ((Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (n ≤ x)) e.1 (n + e.2) = true) ∪
        (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (x < n)) e.1 (n + e.2) = true)) ∪
        (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.MetaComplexity.circuitFun (n + n) C
            (fun k : Fin (n + n) => decide (k = Fin.castAdd n e.1 ∨ k = Fin.natAdd n e.2)) = true ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (n ≤ x)) e.1 (n + e.2) = false ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (x < n)) e.1 (n + e.2) = false) := by
    intro e he
    have hin := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Bool.eq_false_or_eq_true
        (PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (n ≤ x)) e.1 (n + e.2)) with ha | ha
    · exact Or.inl (Or.inl ⟨hin, ha⟩)
    · rcases Bool.eq_false_or_eq_true
          (PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (x < n)) e.1 (n + e.2)) with hb | hb
      · exact Or.inl (Or.inr ⟨hin, hb⟩)
      · exact Or.inr ⟨hin, hedge e.1 e.2 hin, ha, hb⟩
  have hle := Finset.card_le_card hcover
  have hu1 := Finset.card_union_le
    ((Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (n ≤ x)) e.1 (n + e.2) = true) ∪
        (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (x < n)) e.1 (n + e.2) = true))
    (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.MetaComplexity.circuitFun (n + n) C
            (fun k : Fin (n + n) => decide (k = Fin.castAdd n e.1 ∨ k = Fin.natAdd n e.2)) = true ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (n ≤ x)) e.1 (n + e.2) = false ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (x < n)) e.1 (n + e.2) = false)
  have hu2 := Finset.card_union_le
    (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (n ≤ x)) e.1 (n + e.2) = true)
    (Finset.univ.filter fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.lineSingle C (n + n) (fun x => decide (x < n)) e.1 (n + e.2) = true)
  rw [htotal] at hle
  have hmul : n * q ≤ n * (q + 1) := Nat.mul_le_mul_left n (Nat.le_succ q)
  omega
