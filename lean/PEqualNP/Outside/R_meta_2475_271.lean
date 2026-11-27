import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership in
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_2475_271
    (rectangles :
      let overlap := fun (n : ℕ) (C : Circuit) (g : Gate) => g.op = GateOp.and ∧
        ((∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
          wireValue C (List.ofFn x ++ List.replicate n false) w ≠
            wireValue C (List.ofFn x ++ List.replicate n true) w) ∨
         ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
          wireValue C (List.replicate n false ++ List.ofFn x) w ≠
            wireValue C (List.replicate n true ++ List.ofFn x) w)
      ∀ (n : ℕ) (C : Circuit) (U : Finset ℕ), IsAO2 (n+n) C →
        (∀ j g, C.gates[j]? = some g → overlap n C g → j ∈ U) →
        ∀ j < C.size, j ∉ U → (gateAt C j).op = GateOp.and →
          ∃ P L : Finset (Fin n) → Bool, ∀ X Y : Finset (Fin n),
            wireValue C (incidenceInput X Y) (n+n+j) = (P X && L Y))
    (lower :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (U : Finset ℕ),
        100 < q → n = q^2+q+1 →
        (∀ l, (S l).card = q+1) →
        (∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l) →
        IsAO2 (n+n) C → C.output < n+n+C.size →
        RightOnIncidentPairs S C →
        (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
        (∀ j < C.size, j ∉ U → (gateAt C j).op = GateOp.and →
          ∃ P L : Finset (Fin n) → Bool, ∀ X Y : Finset (Fin n),
            wireValue C (incidenceInput X Y) (n+n+j) = (P X && L Y)) →
        100 * U.card < n * q → n * q ≤ 100 * C.size) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q n R dec C qLarge geom lines connects basis output order accept reject U urange exactU few
  let S (l : Fin n) := Finset.univ.filter fun p : Fin n => R p l
  have incident (p l : Fin n) : p ∈ S l ↔ R p l := by simp [S]
  have lineSize (l : Fin n) : (S l).card = q+1 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun p => incident p l))).trans (lines l)
  have through (p p' : Fin n) (unequal : p ≠ p') :
      ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l := by
    simpa only [incident] using connects p p' unequal
  have gateSome (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j]? = some (gateAt C j) := by
    have eq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    rw [eq]
    exact List.getElem?_eq_getElem hj
  have model : IsAO2 (n+n) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa using (basis g hg).1
    · intro j hj i hi
      obtain ⟨a,b,ab,lt,back⟩ := order j _ (gateSome j hj)
      rw [ab, List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
      have get : C.gates[j]? = some g := by
        rw [List.getElem?_eq_getElem hj, eq]
      obtain ⟨a,b,ab,_,_⟩ := order j g get
      simp [ab]
  let vector (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
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
  have sound (X Y : Finset (Fin n)) (budget : Y.card ≤ q) (empty : IsFalseInput S X Y) :
      C.eval (incidenceInput X Y) = false := by
    have count : Fintype.card {l : Fin n // vector X Y (Fin.natAdd n l) = true} = Y.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine Equiv.subtypeEquivRight (fun l => ?_)
      simp only [vl, decide_eq_true_eq]
    have outside : ¬ ∃ (p l : Fin n), R p l ∧ vector X Y (Fin.castAdd n p) = true ∧
        vector X Y (Fin.natAdd n l) = true := by
      rintro ⟨p,l,h,px,ly⟩
      have pX : p ∈ X := of_decide_eq_true ((vp X Y p).symm.trans px)
      have lY : l ∈ Y := of_decide_eq_true ((vl X Y l).symm.trans ly)
      exact Finset.disjoint_left.mp (empty l lY) ((incident p l).mpr h) pX
    rw [← listForm]
    exact reject (vector X Y) (count.trans_le budget) outside
  refine lower q n S C U qLarge geom lineSize through model output correct sound ?_ few
  exact rectangles n C U model (fun j g get h => (exactU j g get).2 h)
