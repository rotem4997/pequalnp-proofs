import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_3698_731
    (support : ∀ (N : ℕ) (C : Circuit) (E : Finset (Fin N × Fin N)),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ v : Fin (N + N), circuitFun (N + N) C (fun i => decide (i = v)) = false) →
      (∀ e ∈ E, circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size + 1)
    (small : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ ((p, l) ∈ E ∧ (p', l) ∈ E ∧ (p, l') ∈ E ∧ (p', l') ∈ E)) →
      min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2256 →
      E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1))
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      let H := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
        circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true ∧
        lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false)
      let S := ∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false
      let K := ∀ v : Fin (N + N),
        let d := (H.filter fun e => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2).card
        0 < d → 24 * max 1 (Fintype.card {j : Fin C.size // v.val ∈ (C.gates.get j).inputs}) < d
      IsAO2 (N + N) C → S → K →
      2256 < min (H.image Prod.fst).card (H.image Prod.snd).card →
      24 * C.size < (H.image Prod.snd).card * (q + 1) → H.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           have x9 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) => {x10 : Fin x2 × Fin x2 | x3 x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 fun (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x10.1 ∨ x11 = Fin.natAdd x2 x10.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x9 (x2 + x2) (fun (x11 : ℕ) => Decidable.decide (x2 ≤ x11)) (↑x10.1) (x2 + ↑x10.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x9 (x2 + x2) (fun (x11 : ℕ) => Decidable.decide (x11 < x2)) (↑x10.1) (x2 + ↑x10.2) = Bool.false};           have x10 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.false;           have x11 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x11 : PEqualNP.CircuitLowerBounds.Circuit) =>             ∀ (x12 : Fin (x2 + x2)),               have x13 : ℕ := {x13 ∈ x9 x11 | x12 = Fin.castAdd x2 x13.1 ∨ x12 = Fin.natAdd x2 x13.2}.card;               (0 : ℕ) < x13 → (24 : ℕ) * Max.max (1 : ℕ) (Fintype.card { x15 : Fin x11.size // ↑x12 ∈ (x11.gates.get x15).inputs }) < x13;           ∀ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x12 → x10 x12 → (4513 : ℕ) ≤ x12.size → x11 x12 → (x9 x12).card ≤ (24 : ℕ) * x12.size := by
  intro q N I inst hq hN reg uniq H S K C hao hsafe _hsize hheavy
  let E := H C
  change E.card ≤ 24 * C.size
  have hmem {e : Fin N × Fin N} (he : e ∈ E) :
      I e.1 e.2 ∧ circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true := by
    have h := (Finset.mem_filter.mp he).2
    exact ⟨h.1, h.2.1⟩
  have hsingle (v : Fin (N + N)) :
      circuitFun (N + N) C (fun i => decide (i = v)) = false := by
    apply hsafe
    · have hone : Fintype.card {l : Fin N // decide (Fin.natAdd N l = v) = true} ≤ 1 := by
        rw [← Fintype.card_fin 1]
        apply Fintype.card_le_of_injective (fun _ => 0)
        intro a b _
        apply Subtype.ext
        have ha : Fin.natAdd N a.val = v := of_decide_eq_true a.property
        have hb : Fin.natAdd N b.val = v := of_decide_eq_true b.property
        have hab := congrArg Fin.val (ha.trans hb.symm)
        apply Fin.ext
        simp only [Fin.val_natAdd] at hab
        omega
      exact hone.trans (by omega)
    · rintro ⟨p, l, _, hp, hl⟩
      have hvp : Fin.castAdd N p = v := of_decide_eq_true hp
      have hvl : Fin.natAdd N l = v := of_decide_eq_true hl
      have hval := congrArg Fin.val (hvp.trans hvl.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
  by_cases hs : min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2256
  · have hsupport := support N C E (fun g hg => (hao.2.2 g hg).le) hsingle
        (fun e he => (hmem he).2)
    have hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ ((p, l) ∈ E ∧ (p', l) ∈ E ∧ (p, l') ∈ E ∧ (p', l') ∈ E) := by
      rintro p p' l l' hp hl ⟨hpl, hp'l, hpl', hp'l'⟩
      obtain ⟨w, _, hw⟩ := uniq p p' hp
      exact hl ((hw l ⟨(hmem hpl).1, (hmem hp'l).1⟩).trans
        (hw l' ⟨(hmem hpl').1, (hmem hp'l').1⟩).symm)
    exact (small N E hfour hs).trans (Nat.mul_le_mul_left 24 (by omega))
  · have hinc : E.card ≤ (E.image Prod.snd).card * (q + 1) := by
      let ActiveLines := {l : Fin N // l ∈ E.image Prod.snd}
      let embed : {e : Fin N × Fin N // e ∈ E} → (Σ l : ActiveLines, {p : Fin N // I p l.val}) :=
        fun e => ⟨⟨e.val.2, Finset.mem_image_of_mem _ e.property⟩, ⟨e.val.1, (hmem e.property).1⟩⟩
      have hinjective : Function.Injective embed := by
        intro a b h
        apply Subtype.ext
        exact Prod.ext (congrArg (fun e => e.2.val) h) (congrArg (fun e => e.1.val) h)
      calc
        E.card = Fintype.card {e : Fin N × Fin N // e ∈ E} := (Fintype.card_coe E).symm
        _ ≤ Fintype.card (Σ l : ActiveLines, {p : Fin N // I p l.val}) :=
          Fintype.card_le_of_injective embed hinjective
        _ = (E.image Prod.snd).card * (q + 1) := by simp [Fintype.card_sigma, reg, ActiveLines]
    by_cases hbudget : (E.image Prod.snd).card * (q + 1) ≤ 24 * C.size
    · exact hinc.trans hbudget
    · exact large q N I C hq hN reg uniq hao hsafe hheavy
        (lt_of_not_ge hs) (lt_of_not_ge hbudget)
