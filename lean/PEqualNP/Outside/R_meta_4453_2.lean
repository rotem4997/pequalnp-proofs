import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4453_2
    (hdual : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      131 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      (∀ p : Fin N, Fintype.card { l : Fin N // I p l } = q + 1) ∧
      (∀ l1 l2 : Fin N, l1 ≠ l2 → ∃! p : Fin N, I p l1 ∧ I p l2))
    (hcore : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      131 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      (∀ p : Fin N, Fintype.card { l : Fin N // I p l } = q + 1) →
      (∀ l1 l2 : Fin N, l1 ≠ l2 → ∃! p : Fin N, I p l1 ∧ I p l2) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card { l : Fin N // x (Fin.natAdd N l) = Bool.true } ≤ q →
        (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = Bool.true ∧ x (Fin.natAdd N l) = Bool.true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C x = Bool.false) →
      have E : Finset (Fin N × Fin N) := {e : Fin N × Fin N | I e.1 e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun i : Fin (N + N) => Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = Bool.true};
      (∀ v : Fin (N + N),
        have d : ℕ := {e ∈ E | v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2}.card;
        d = 0 ∨ 44 < d) →
      E.Nonempty → 0 < C.size → 44 * C.size < N * (q + 1) →
      E.card ≤ 44 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (131 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : Finset (Fin x2 × Fin x2) := {x12 : Fin x2 × Fin x2 | x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true};               (∀ (x13 : Fin (x2 + x2)),                   have x14 : ℕ := {x14 ∈ x12 | x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2}.card;                   x14 = (0 : ℕ) ∨ (44 : ℕ) < x14) →                 x12.card ≤ (44 : ℕ) * x5.size := by
  intro q N I inst C hq hN hdeg huniq hao hsound
  dsimp only
  intro hdeg44
  let E : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun e : Fin N × Fin N =>
      I e.1 e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun i : Fin (N + N) => Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = Bool.true
  change E.card ≤ 44 * C.size
  by_cases hne : E.Nonempty
  · by_cases hsmall : 44 * C.size < N * (q + 1)
    · have hpos : 0 < C.size := by
        by_contra hzero
        have hlen0 : C.gates.length = 0 := by
          change ¬ 0 < C.gates.length at hzero
          omega
        have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hlen0
        have heval_nil : ∀ x : Fin (N + N) → Bool,
            PEqualNP.MetaComplexity.circuitFun (N + N) C x = (List.ofFn x).getD C.output false := by
          intro x
          change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
          rw [hnil]
          rfl
        by_cases hout : C.output < N + N
        · have heval_at : ∀ x : Fin (N + N) → Bool,
              PEqualNP.MetaComplexity.circuitFun (N + N) C x = x ⟨C.output, hout⟩ := by
            intro x
            rw [heval_nil x]
            simp [List.getD, List.getElem?_ofFn, hout]
          by_cases hpt : C.output < N
          · let p : Fin N := ⟨C.output, hpt⟩
            let xp : Fin (N + N) → Bool := fun i => Decidable.decide (i = Fin.castAdd N p)
            have hfalse : PEqualNP.MetaComplexity.circuitFun (N + N) C xp = Bool.false := by
              apply hsound xp
              · have hempty : (Finset.univ.filter fun l : Fin N => xp (Fin.natAdd N l) = Bool.true) = ∅ := by
                  ext l
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                    iff_false]
                  intro h
                  have heq : Fin.natAdd N l = Fin.castAdd N p := of_decide_eq_true h
                  have hval := congrArg Fin.val heq
                  simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
                  omega
                rw [Fintype.card_subtype, hempty, Finset.card_empty]
                omega
              · rintro ⟨p', l', _, _, hl'⟩
                have heq : Fin.natAdd N l' = Fin.castAdd N p := of_decide_eq_true hl'
                have hval := congrArg Fin.val heq
                simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
                omega
            have htrue : PEqualNP.MetaComplexity.circuitFun (N + N) C xp = Bool.true := by
              rw [heval_at xp]
              have hv : (⟨C.output, hout⟩ : Fin (N + N)) = Fin.castAdd N p := Fin.ext rfl
              simp [xp, hv]
            rw [htrue] at hfalse
            cases hfalse
          · let l : Fin N := ⟨C.output - N, by omega⟩
            let xl : Fin (N + N) → Bool := fun i => Decidable.decide (i = Fin.natAdd N l)
            have hfalse : PEqualNP.MetaComplexity.circuitFun (N + N) C xl = Bool.false := by
              apply hsound xl
              · have hsub : (Finset.univ.filter fun k : Fin N => xl (Fin.natAdd N k) = Bool.true) ⊆ {l} := by
                  intro k hk
                  have hk' := of_decide_eq_true (Finset.mem_filter.mp hk).2
                  have hval := congrArg Fin.val hk'
                  simp only [Fin.val_natAdd] at hval
                  exact Finset.mem_singleton.mpr (Fin.ext (by omega))
                rw [Fintype.card_subtype]
                have hc := Finset.card_le_card hsub
                simp only [Finset.card_singleton] at hc
                omega
              · rintro ⟨p', l', _, hp', _⟩
                have heq : Fin.castAdd N p' = Fin.natAdd N l := of_decide_eq_true hp'
                have hval := congrArg Fin.val heq
                simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
                omega
            have htrue : PEqualNP.MetaComplexity.circuitFun (N + N) C xl = Bool.true := by
              rw [heval_at xl]
              have hv : (⟨C.output, hout⟩ : Fin (N + N)) = Fin.natAdd N l := by
                apply Fin.ext
                simp only [Fin.val_natAdd, l]
                omega
              simp [xl, hv]
            rw [htrue] at hfalse
            cases hfalse
        · rcases hne with ⟨e, he⟩
          have hacc := (Finset.mem_filter.mp he).2.2
          rw [heval_nil] at hacc
          have hge : ¬ C.output < N + N := hout
          simp [List.getD, List.getElem?_ofFn, hge] at hacc
      rcases hdual q N I hq hN hdeg huniq with ⟨hpdeg, hluniq⟩
      exact hcore q N I C hq hN hdeg huniq hpdeg hluniq hao hsound hdeg44 hne hpos hsmall
    · have hsub : E ⊆ Finset.univ.biUnion (fun l : Fin N =>
          (Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))) := by
        intro e he
        have hI := (Finset.mem_filter.mp he).2.1
        refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩, rfl⟩
      have hcard_le : E.card ≤ Finset.univ.sum (fun l : Fin N =>
          ((Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))).card) :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have hterm : ∀ l : Fin N,
          ((Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))).card ≤ q + 1 := by
        intro l
        have h1 : ((Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))).card ≤
            (Finset.univ.filter fun p : Fin N => I p l).card := Finset.card_image_le
        have h2 : (Finset.univ.filter fun p : Fin N => I p l).card = q + 1 := by
          rw [← Fintype.card_subtype]
          exact hdeg l
        omega
      have hsum : Finset.univ.sum (fun l : Fin N =>
          ((Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))).card) ≤
          N * (q + 1) := by
        calc Finset.univ.sum (fun l : Fin N =>
              ((Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p, l))).card)
            ≤ Finset.univ.sum (fun _ : Fin N => q + 1) :=
              Finset.sum_le_sum (fun l _ => hterm l)
          _ = N * (q + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
  · have hempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.card_empty]
    omega
