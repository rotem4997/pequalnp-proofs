import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_3258_17
    (monotoneInput : ∀ (n : ℕ) (C : Circuit), IsAO2 (n+n) C →
      ∀ (A B X Y : Finset (Fin n)), A ⊆ X → B ⊆ Y →
      C.eval (incidenceInput A B) = true → C.eval (incidenceInput X Y) = true)
    (mintermBound : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit)
      (H : Finset (Finset (Fin n) × Finset (Fin n))),
      100 < q → n = q^2 + q + 1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → C.output < n+n+C.size →
      (∀ e ∈ H, q < e.2.card ∧ IsFalseInput S e.1 e.2) →
      (∀ e ∈ H, ∀ d ∈ H, d.1 ⊆ e.1 → d.2 ⊆ e.2 → d = e) →
      (∀ X Y, C.eval (incidenceInput X Y) = true ↔
        incidenceFun S X Y = true ∨ ∃ e ∈ H, e.1 ⊆ X ∧ e.2 ⊆ Y) →
      (∃ j < C.size, (gateAt C j).op = .or ∧ ∃ K : Finset (Fin n), 100 < K.card ∧
        let A := fun l : Fin n => Finset.univ.filter (fun p : Fin n =>
          wireValue C (incidenceInput {p} {l}) (n+n+j))
        Set.InjOn A ↑K ∧ ∀ l ∈ K, 1 < (A l).card ∧ A l ⊆ S l ∧
          wireValue C (incidenceInput (S l)ᶜ {l}) (n+n+j) = false) →
      n*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →                 (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →                   (∃ x13 < x4.size,                       (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                         ∃ (x14 : Finset (Fin x2)),                           (100 : ℕ) < x14.card ∧                             have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};                             Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →                     x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C hq plane degree unique model out positive sparse gate
  let accepts (e : Finset (Fin n) × Finset (Fin n)) := C.eval (incidenceInput e.1 e.2) = true
  let H := Finset.univ.filter (fun e : Finset (Fin n) × Finset (Fin n) =>
    IsFalseInput S e.1 e.2 ∧ accepts e ∧
    ∀ d : Finset (Fin n) × Finset (Fin n), d.1 ⊆ e.1 → d.2 ⊆ e.2 → accepts d → d = e)
  have memH (e) : e ∈ H ↔ IsFalseInput S e.1 e.2 ∧ accepts e ∧
      ∀ d, d.1 ⊆ e.1 → d.2 ⊆ e.2 → accepts d → d = e := by
    simp only [H,Finset.mem_filter,Finset.mem_univ,true_and]
  apply mintermBound q n S C H hq plane degree unique model out
  · intro e he
    obtain ⟨bad,yes,_⟩ := (memH e).mp he
    refine ⟨?_,bad⟩
    by_contra! small
    exact Bool.noConfusion ((sparse _ _ small bad).symm.trans yes)
  · intro e he d hd hP hL
    exact ((memH e).mp he).2.2 d hP hL ((memH d).mp hd).2.1
  · intro X Y
    constructor
    · intro ok
      by_cases incident : ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l
      · left
        change decide _ = true
        exact decide_eq_true incident
      · right
        have bad : IsFalseInput S X Y := by
          intro l hl
          exact Finset.disjoint_left.mpr (fun p on inside => incident ⟨p,inside,l,hl,on⟩)
        let witness (k : ℕ) := ∃ P ⊆ X, ∃ Z ⊆ Y, P.card + Z.card = k ∧ accepts (P,Z)
        have existsWitness : ∃ k, witness k := ⟨_,X,Finset.Subset.rfl,Y,Finset.Subset.rfl,rfl,ok⟩
        obtain ⟨P,subP,Z,subZ,kval,accept⟩ := Nat.find_spec existsWitness
        refine ⟨(P,Z),(memH _).mpr ⟨fun l hl => (bad l (subZ hl)).mono_right subP,accept,?_⟩,subP,subZ⟩
        rintro ⟨A,B⟩ hA hB yes
        change A ⊆ P at hA
        change B ⊆ Z at hB
        have minimum := Nat.find_min' existsWitness (m := A.card+B.card)
          ⟨A,hA.trans subP,B,hB.trans subZ,rfl,yes⟩
        have ha := Finset.card_le_card hA
        have hb := Finset.card_le_card hB
        have bound : P.card + Z.card ≤ A.card + B.card := kval.trans_le minimum
        have eqA : A = P := Finset.eq_of_subset_of_card_le hA (by omega)
        have eqB : B = Z := Finset.eq_of_subset_of_card_le hB (by omega)
        exact Prod.ext eqA eqB
    · rintro (hit | ⟨e,he,hP,hL⟩)
      · change decide _ = true at hit
        obtain ⟨p,hp,l,hl,on⟩ := of_decide_eq_true hit
        exact monotoneInput n C model {p} {l} X Y (Finset.singleton_subset_iff.mpr hp)
          (Finset.singleton_subset_iff.mpr hl) (positive l p on)
      · exact monotoneInput n C model _ _ X Y hP hL ((memH e).mp he).2.1
  · exact gate
