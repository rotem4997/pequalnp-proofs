import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_2475_299
    (hlinear :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        2 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
        Monotone2 C → ReadsBack (N + N) C →
        (∀ p l : Fin N, I p l →
          circuitFun (N + N) C (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
        (∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
          (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          circuitFun (N + N) C x = false) →
        2 * N ≤ C.size + 1)
    (hpairs :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        2 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
        Monotone2 C →
        (∀ u v : Fin (N + N),
          circuitFun (N + N) C (fun i => decide (i = u ∨ i = v)) = true ↔
            ∃ p l : Fin N, I p l ∧
              (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
              (Fin.natAdd N l = u ∨ Fin.natAdd N l = v)) →
        3 * N ≤ C.size + 1)
    (hlarge :
      ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → x3 * x2 ≤ (100 : ℕ) * x6.size) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q N I dec C hq hN hlines hconnect hmono hout horder haccept hreject U hU hcharacter hfew
  have hNlarge : 100 ≤ N := by omega
  by_cases hsmall : q ≤ 199
  · have hread : ReadsBack (N + N) C := by
      intro j hj i hi
      have hget : C.gates[j]? = some (gateAt C j) := by
        change C.gates[j]? = some (C.gates.getD j ⟨.or, []⟩)
        rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
      obtain ⟨a, b, hab, hlt, hback⟩ := horder j (gateAt C j) hget
      rw [hab] at hi
      simp at hi
      rcases hi with rfl | rfl
      · omega
      · exact hback
    have hfloor := @hlinear q N I dec C (by omega) hN hlines hconnect hmono hread haccept hreject
    have hm := Nat.mul_le_mul_left N hsmall
    omega
  by_cases hmid : q ≤ 299
  · have htest (u v : Fin (N + N)) :
        circuitFun (N + N) C (fun i => decide (i = u ∨ i = v)) = true ↔
          ∃ p l : Fin N, I p l ∧
            (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
            (Fin.natAdd N l = u ∨ Fin.natAdd N l = v) := by
      let x : Fin (N + N) → Bool := fun i => decide (i = u ∨ i = v)
      change circuitFun (N + N) C x = true ↔ _
      constructor
      · intro ht
        by_contra hn
        let pins : Finset (Fin (N + N)) := {u, v}
        let embed : {l : Fin N // x (Fin.natAdd N l) = true} → ↥pins := fun l =>
          ⟨Fin.natAdd N l.val, by
            have hh : Fin.natAdd N l.val = u ∨ Fin.natAdd N l.val = v :=
              of_decide_eq_true l.property
            simpa only [pins, Finset.mem_insert, Finset.mem_singleton] using hh⟩
        have hinj : Function.Injective embed := by
          intro l r he
          apply Subtype.ext
          apply Fin.ext
          have ha := congrArg (fun t : ↥pins => t.val.val) he
          change N + l.val.val = N + r.val.val at ha
          omega
        have hc : Fintype.card ↥pins ≤ 2 := by
          rw [Fintype.card_coe pins]
          simpa [pins] using (Finset.card_insert_le u ({v} : Finset (Fin (N + N))))
        have hcount := (Fintype.card_le_of_injective embed hinj).trans hc
        have hf := hreject x (hcount.trans (by omega)) (by
          rintro ⟨p, l, hI, hp, hl⟩
          exact hn ⟨p, l, hI, of_decide_eq_true hp, of_decide_eq_true hl⟩)
        exact Bool.noConfusion (ht.symm.trans hf)
      · rintro ⟨p, l, hI, hp, hl⟩
        have hsep : (Fin.castAdd N p : Fin (N + N)) ≠ Fin.natAdd N l := by
          intro he
          have hv := congrArg Fin.val he
          change p.val = N + l.val at hv
          have := p.isLt
          omega
        rcases hp with hp | hp
        · rcases hl with hl | hl
          · exact (hsep (hp.trans hl.symm)).elim
          · simpa only [x, ← hp, ← hl] using haccept p l hI
        · rcases hl with hl | hl
          · simpa only [x, ← hp, ← hl, or_comm] using haccept p l hI
          · exact (hsep (hp.trans hl.symm)).elim
    have hfloor := @hpairs q N I dec C (by omega) hN hlines hconnect hmono htest
    have hm := Nat.mul_le_mul_left N hmid
    omega
  exact @hlarge q N I dec C (by omega) hN hlines hconnect hmono hout horder haccept hreject
