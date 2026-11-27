import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4710_619
    (single : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size)
    (rest : ∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit),
      300 ≤ q → n = q^2 + q + 1 →
      (∀ l, Fintype.card {p : Fin n // R p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, R p l ∧ R r l) →
      PEqualNP.TopForm.IsAO2 (n+n) C →
      (∀ p l, R p l → circuitFun (n+n) C
        (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) = true) →
      (∀ z : Fin (n+n) → Bool, Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l : Fin n, R p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
        circuitFun (n+n) C z = false) →
      Fintype.card {e : Fin n × Fin n // R e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (n ≤ i)) e.1.val (n+e.2.val) = false}
        ≤ 90 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ x16 ∈ x6, x16 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x17 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.true ↔ ∃ x18 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x18 x17 = Bool.true) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → ∃ x21 ∈ x6, (PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x21 fun (x22 : Fin (x2 + x2)) => Decidable.decide (x22 = Fin.castAdd x2 x18 ∨ x22 = Fin.natAdd x2 x19)) = Bool.true) → (∀ (x19 : Fin (x2 + x2) → Bool), Fintype.card { x20 : Fin x2 // x19 (Fin.natAdd x2 x20) = Bool.true } ≤ x1 → (¬∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19 (Fin.castAdd x2 x21) = Bool.true ∧ x19 (Fin.natAdd x2 x22) = Bool.true) → ∀ x22 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x22 x19 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R inst C F hq hn degree join hm hout hout' hor ordered front eval accept sound
  have back : ReadsBack (n+n) C := by
    intro j hj i hi
    have hgate : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    obtain ⟨a,b,hin,hab,hb⟩ := ordered j C.gates[j] (List.getElem?_eq_getElem hj)
    rw [hgate, hin] at hi
    simp at hi
    rcases hi with rfl | rfl <;> omega
  have ao : PEqualNP.TopForm.IsAO2 (n+n) C := by
    refine ⟨?_, back, ?_⟩
    · intro g hg
      simpa using (hm g hg).1
    · intro g hg
      obtain ⟨j,hj,hg⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,hin,_,_⟩ := ordered j g (hg ▸ List.getElem?_eq_getElem hj)
      simp [hin]
  have neg (z : Fin (n+n) → Bool)
      (hz : Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q)
      (hf : ¬ ∃ p l : Fin n, R p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) :
      circuitFun (n+n) C z = false := by
    cases h : circuitFun (n+n) C z
    · rfl
    · obtain ⟨j,hj,ht⟩ := (eval z).mp h
      rw [sound z hz hf j hj] at ht
      contradiction
  have pos (p l : Fin n) (hp : R p l) : circuitFun (n+n) C
      (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) = true :=
    (eval _).mpr (accept p l hp)
  have c4 (p r l k : Fin n) (hpr : p ≠ r) (hlk : l ≠ k) :
      ¬ (R p l ∧ R r l ∧ R p k ∧ R r k) := by
    rintro ⟨a,b,c,d⟩
    obtain ⟨m,_,unique⟩ := join p r hpr
    exact hlk ((unique l ⟨a,b⟩).trans (unique k ⟨c,d⟩).symm)
  have hi := single n R C c4 ao (fun z hz => neg z (by omega))
  have hr := rest q n R C hq hn degree join ao pos neg
  let E := {e : Fin n × Fin n // R e.1 e.2}
  let S (e : E) := PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (n ≤ i))
    e.val.1.val (n+e.val.2.val) = true
  have ecard : Fintype.card E = n * (q+1) := by
    let equiv : E ≃ (Σ l : Fin n, {p : Fin n // R p l}) :=
      ⟨fun e => ⟨e.val.2, e.val.1, e.property⟩,
       fun e => ⟨(e.2.val,e.1),e.2.property⟩, fun _ => rfl, fun _ => rfl⟩
    rw [Fintype.card_congr equiv, Fintype.card_sigma]
    simp [degree]
  have split (b : Bool) : {e : E // PEqualNP.ReadK.lineSingle C (n+n)
      (fun i => decide (n ≤ i)) e.val.1.val (n+e.val.2.val) = b} ≃
      {e : Fin n × Fin n // R e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (n+n)
      (fun i => decide (n ≤ i)) e.1.val (n+e.2.val) = b} :=
    ⟨fun e => ⟨e.val.val,e.val.property,e.property⟩,
      fun e => ⟨⟨e.val,e.property.1⟩,e.property.2⟩, fun _ => rfl, fun _ => rfl⟩
  have sum := Fintype.card_subtype_compl S
  have negS : (fun e : E => ¬ S e) = (fun e : E =>
      PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (n ≤ i))
        e.val.1.val (n+e.val.2.val) = false) := by
    funext e
    unfold S
    cases (PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (n ≤ i))
        e.val.1.val (n+e.val.2.val)) <;> simp
  have conv : {e : E // ¬ S e} ≃ {e : E // PEqualNP.ReadK.lineSingle C (n+n) (fun i => decide (n ≤ i)) e.val.1.val (n+e.val.2.val) = false} := by
    apply Equiv.subtypeEquivRight
    intro e
    exact Iff.of_eq (congrFun negS e)
  rw [Fintype.card_congr (conv.trans (split false))] at sum
  change _ = Fintype.card E - Fintype.card {e : E // PEqualNP.ReadK.lineSingle C (n+n)
      (fun i => decide (n ≤ i)) e.val.1.val (n+e.val.2.val) = true} at sum
  rw [Fintype.card_congr (split true), ecard] at sum
  rw [Nat.mul_succ] at sum
  omega
