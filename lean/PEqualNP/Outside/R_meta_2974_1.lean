import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2974_1
    (pin : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n),
      PEqualNP.TopForm.IsAO2 n C →
      (∃ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) ∧
        PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) →
      PEqualNP.MetaComplexity.circuitFun n C (fun i => decide (i = v)) = false →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
        (∀ x, PEqualNP.MetaComplexity.circuitFun n D x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧
        (∀ x, x v = false → PEqualNP.MetaComplexity.circuitFun n D x = PEqualNP.MetaComplexity.circuitFun n C x) ∧
        ∀ (s : ℕ → Bool) (a b : ℕ), v.val ≠ a → v.val ≠ b →
          PEqualNP.ReadK.lineSingle D n s a b = PEqualNP.ReadK.lineSingle C n s a b)
    (core : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q ^ 2 + q + 1 → (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      let hits := fun (v : Fin (N + N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (fun i => decide (hits i e)) = true ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) → E.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  intro q N I inst C hq hN hcol huniq hao hsound
  let hits := fun (v : Fin (N + N)) (e : Fin N × Fin N) => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
  let pair := fun (e : Fin N × Fin N) (i : Fin (N + N)) => decide (hits i e)
  let single := fun (v i : Fin (N + N)) => decide (i = v)
  let sound := fun (D : PEqualNP.CircuitLowerBounds.Circuit) => ∀ z : Fin (N + N) → Bool,
    Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    PEqualNP.MetaComplexity.circuitFun (N + N) D z = false
  let bad := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (e : Fin N × Fin N) =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) D (pair e) = true ∧
      PEqualNP.ReadK.lineSingle D (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      PEqualNP.ReadK.lineSingle D (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false
  have separate (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro eq
    have := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := p.isLt
    omega
  have singleton_off (D) (hs : sound D) (w : Fin (N + N)) :
      PEqualNP.MetaComplexity.circuitFun (N + N) D (single w) = false := by
    apply hs
    · rw [Fintype.card_subtype]
      apply Nat.le_trans (Finset.card_le_one.mpr ?_) (by omega)
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, single, decide_eq_true_eq] at ha hb
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha.trans hb.symm)))
    · rintro ⟨p, l, _, hp, hl⟩
      exact separate p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have peel : ∀ k (D : PEqualNP.CircuitLowerBounds.Circuit), D.size = k →
      PEqualNP.TopForm.IsAO2 (N + N) D → sound D → ∀ E : Finset (Fin N × Fin N),
      (∀ e ∈ E, bad D e) → E.card ≤ 24 * D.size := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hsize hAO hs E hE
      by_cases dense : ∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card
      · exact core q N I D E hq hN hcol huniq hAO hs hE dense
      push Not at dense
      obtain ⟨e, he, v, hv, hdeg⟩ := dense
      have acc := (hE e he).2.1
      have essential : ∃ x y : Fin (N + N) → Bool, (∀ i, i ≠ v → x i = y i) ∧
          PEqualNP.MetaComplexity.circuitFun (N + N) D x ≠ PEqualNP.MetaComplexity.circuitFun (N + N) D y := by
        rcases hv with rfl | rfl
        · refine ⟨pair e, single (Fin.natAdd N e.2), ?_, ?_⟩
          · intro i hi; simp only [pair, hits, single, hi, false_or]
          · rw [acc, singleton_off D hs]; decide
        · refine ⟨pair e, single (Fin.castAdd N e.1), ?_, ?_⟩
          · intro i hi; simp only [pair, hits, single, hi, or_false]
          · rw [acc, singleton_off D hs]; decide
      obtain ⟨D', hAO', hlt, hdom, hsame, hparts⟩ := pin _ D v hAO essential (singleton_off D hs v)
      have hs' : sound D' := by
        intro z hcount hno
        apply Bool.eq_false_iff.mpr
        intro h
        exact Bool.noConfusion ((hdom z h).symm.trans (hs z hcount hno))
      let F := E.filter fun f => ¬ hits v f
      have keep : ∀ f ∈ F, bad D' f := by
        intro f hf
        obtain ⟨hfE, hmiss⟩ := Finset.mem_filter.mp hf
        obtain ⟨hi, hyes, hline, hpoint⟩ := hE f hfE
        have hleft : v.val ≠ f.1.val := fun eq => hmiss (Or.inl (Fin.ext eq))
        have hright : v.val ≠ N + f.2.val := fun eq => hmiss (Or.inr (Fin.ext eq))
        exact ⟨hi, (hsame (pair f) (by simp [pair, hmiss])).trans hyes,
          (hparts _ _ _ hleft hright).trans hline, (hparts _ _ _ hleft hright).trans hpoint⟩
      have small := ih D'.size (by omega) D' rfl hAO' hs' F keep
      have split := Finset.card_filter_add_card_filter_not (s := E) (hits v)
      change (E.filter (hits v)).card + F.card = E.card at split
      omega
  rw [Fintype.card_subtype]
  exact peel C.size C rfl hao hsound _ (fun _ he => (Finset.mem_filter.mp he).2)
