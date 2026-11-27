import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- A small set of active points or lines gives a four-cycle-free counting bound.
-- The unresolved case then has more than 2208 active vertices on each side.
theorem PEqualNP.Outside.R_meta_4598_1
    (support : ∀ (N : ℕ) (C : Circuit) (E : Finset (Fin N × Fin N)),
      IsAO2 (N+N) C →
      (∀ v : Fin (N+N), circuitFun (N+N) C (fun i => decide (i = v)) = false) →
      (∀ e ∈ E, circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size+1)
    (small : ∀ {N : ℕ} (E : Finset (Fin N × Fin N)),
      (∀ p r l m : Fin N, p ≠ r → l ≠ m →
        ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E)) →
      ((E.image Prod.fst).card ≤ 2208 ∨ (E.image Prod.snd).card ≤ 2208) →
      E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card-1))
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let hits := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) →
      4400 < C.size → 2208 < (E.image Prod.fst).card → 2208 < (E.image Prod.snd).card →
      E.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → (4400 : ℕ) < x5.size → x6.card ≤ (24 : ℕ) * x5.size := by
  intro q N I dec C E hq hN cols uniq shape sound hits accepted dense budget
  by_cases hs : (E.image Prod.fst).card ≤ 2208 ∨ (E.image Prod.snd).card ≤ 2208
  · have hFour : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
        ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E) := by
      intro p r l m hp hl h
      obtain ⟨g,_,hg⟩ := uniq p r hp
      apply hl
      exact (hg l ⟨(accepted (p,l) h.1).1,(accepted (r,l) h.2.1).1⟩).trans
        (hg m ⟨(accepted (p,m) h.2.2.1).1,(accepted (r,m) h.2.2.2).1⟩).symm
    have singleton (v : Fin (N+N)) :
        circuitFun (N+N) C (fun i => decide (i = v)) = false := by
      let z : Fin (N+N) → Bool := fun i => decide (i = v)
      have few : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q := by
        let f : {l : Fin N // z (Fin.natAdd N l) = true} → Fin 1 := fun _ => 0
        have injective : Function.Injective f := by
          intro a b _
          have ha : Fin.natAdd N a.val = v := of_decide_eq_true a.property
          have hb : Fin.natAdd N b.val = v := of_decide_eq_true b.property
          have he : N+a.val.val = N+b.val.val := congrArg Fin.val (ha.trans hb.symm)
          exact Subtype.ext (Fin.ext (Nat.add_left_cancel he))
        have h := Fintype.card_le_of_injective f injective
        rw [Fintype.card_fin] at h
        omega
      have noEdge : ¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
        rintro ⟨p,l,_,hp,hl⟩
        have a : Fin.castAdd N p = v := of_decide_eq_true hp
        have b : Fin.natAdd N l = v := of_decide_eq_true hl
        have h := congrArg Fin.val (a.trans b.symm)
        change p.val = N+l.val at h
        omega
      exact sound z few noEdge
    have hCount := support N C E shape singleton (fun e he => (accepted e he).2.1)
    have hE := small E hFour hs
    exact hE.trans (Nat.mul_le_mul_left 24 (by omega))
  · have hP : 2208 < (E.image Prod.fst).card := by omega
    have hL : 2208 < (E.image Prod.snd).card := by omega
    exact @large q N I dec C E hq hN cols uniq shape sound accepted dense budget hP hL
