import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection in
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_2990_2
    (dual :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)),
        2 ≤ q → n = q ^ 2 + q + 1 →
        (∀ l, (S l).card = q + 1) →
        (∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l) →
        (∀ p : Fin n, Fintype.card {l : Fin n // p ∈ S l} = q + 1) ∧
        (∀ l l' : Fin n, l ≠ l' → (S l ∩ S l').card = 1))
    (bound :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
        300 ≤ q → n = q ^ 2 + q + 1 →
        (∀ l, (S l).card = q + 1) →
        (∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l) →
        (∀ p : Fin n, Fintype.card {l : Fin n // p ∈ S l} = q + 1) →
        (∀ l l' : Fin n, l ≠ l' → (S l ∩ S l').card = 1) →
        IsAO2 (n + n) C → C.output < n + n + C.size → RightOnIncidentPairs S C →
        (∀ Y : Finset (Fin n), Y.card ≤ q → C.eval (incidenceInput (zeroSet S Y) Y) = false) →
        n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R dec C qLarge geom lines connects basis output order accept reject
  let S (l : Fin n) := Finset.univ.filter fun p : Fin n => R p l
  have incident (p l : Fin n) : p ∈ S l ↔ R p l := by simp [S]
  have lineSize (l : Fin n) : (S l).card = q + 1 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun p => incident p l))).trans (lines l)
  have through (p p' : Fin n) (unequal : p ≠ p') :
      ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l := by
    simpa only [incident] using connects p p' unequal
  have gateSome (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j]? = some (gateAt C j) := by
    rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
    exact List.getElem?_eq_getElem hj
  have model : IsAO2 (n + n) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa using (basis g hg).1
    · intro j hj i hi
      obtain ⟨a, b, ab, lt, back⟩ := order j _ (gateSome j hj)
      rw [ab, List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j, hj, eq⟩ := List.mem_iff_getElem.mp hg
      have get : C.gates[j]? = some g := by
        rw [List.getElem?_eq_getElem hj, eq]
      obtain ⟨a, b, ab, _, _⟩ := order j g get
      simp [ab]
  let vector (X Y : Finset (Fin n)) : Fin (n + n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have listForm (X Y : Finset (Fin n)) : List.ofFn (vector X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have vp (X Y : Finset (Fin n)) (p : Fin n) : vector X Y (Fin.castAdd n p) = decide (p ∈ X) :=
    Fin.addCases_left ..
  have vl (X Y : Finset (Fin n)) (l : Fin n) : vector X Y (Fin.natAdd n l) = decide (l ∈ Y) :=
    Fin.addCases_right ..
  have diff (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castAdd, Fin.val_natAdd] at values
    have lt := p.isLt
    omega
  have pair (p l : Fin n) :
      vector {p} {l} = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
    funext i
    refine Fin.addCases (motive := fun i => vector {p} {l} i =
      decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) ?_ ?_ i
    · intro a
      rw [vp]
      simp only [Finset.mem_singleton, Fin.castAdd_inj, diff a l, or_false]
    · intro b
      rw [vl]
      simp only [Finset.mem_singleton, Fin.natAdd_inj, Ne.symm (diff p b), false_or]
  have correct : RightOnIncidentPairs S C := by
    intro l p hp
    rw [← listForm, pair]
    exact accept p l ((incident p l).mp hp)
  have canonical (Y : Finset (Fin n)) (budget : Y.card ≤ q) :
      C.eval (incidenceInput (zeroSet S Y) Y) = false := by
    let X := zeroSet S Y
    have count : Fintype.card {l : Fin n // vector X Y (Fin.natAdd n l) = true} = Y.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine Equiv.subtypeEquivRight (fun l => ?_)
      simp only [vl, decide_eq_true_eq]
    have outside : ¬ ∃ (p l : Fin n), R p l ∧ vector X Y (Fin.castAdd n p) = true ∧
        vector X Y (Fin.natAdd n l) = true := by
      rintro ⟨p, l, h, px, ly⟩
      have pX : p ∈ X := of_decide_eq_true ((vp X Y p).symm.trans px)
      have lY : l ∈ Y := of_decide_eq_true ((vl X Y l).symm.trans ly)
      have avoids : ∀ k ∈ Y, p ∉ S k := (Finset.mem_filter.mp pX).2
      exact avoids l lY ((incident p l).mpr h)
    change C.eval (incidenceInput X Y) = false
    rw [← listForm]
    exact reject (vector X Y) (count.trans_le budget) outside
  have facts := dual q n S (by omega) geom lineSize through
  exact bound q n S C qLarge geom lineSize through facts.1 facts.2 model output correct canonical
