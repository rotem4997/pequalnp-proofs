import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cofactor redundancy budget. After any vertex is set to zero, each gate
-- that becomes constant or agrees with an earlier wire can be omitted, all
-- at once. The restricted graph is Petersen minus one vertex. Its surviving
-- distinguished literal is represented by a first NOT in one of two orbits.
-- The two corresponding first-gate bounds are L-meta-1665 and L-meta-1666.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5369_669
    (compress : ∀ (C : Circuit) (u : Fin 9) (p : Fin 10 → ℕ) (T : Finset ℕ),
      let x := fun (y : Fin 9 → Bool) (i : Fin 10) => (List.ofFn y).getD (p i) false
      let w := fun y => List.ofFn (x y) ++ [!x y 0]
      let V := fun i y => (C.wires (w y)).getD i false
      FanInTwo C → (p 0 = u.val ∨ 9 ≤ p 0) →
      (∀ i ∈ T, 11 ≤ i ∧ i < 11+C.size ∧ ((∃ b, ∀ y, V i y = b) ∨ ∃ j < i, ∀ y, V i y = V j y)) →
      (∃ b, ∀ y, C.eval (w y) = b) ∨
      ∃ D : Circuit, FanInTwo D ∧ D.size + T.card ≤ C.size + 1 ∧
        (∀ y : Fin 9 → Bool, (D.wires (List.ofFn y)).getD 9 false = !y u) ∧
        ∀ y, D.eval (List.ofFn y) = C.eval (w y))
    (degreeThree : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (degreeTwo : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (core : ∀ C : Circuit,
      let w := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
      let V := fun i x => (C.wires (w x)).getD i false
      FanInTwo C → C.size ≤ 18 →
      (∀ (v : Fin 10) (T : Finset ℕ),
        (∀ i ∈ T, 11 ≤ i ∧ i < 11+C.size ∧ ((∃ b, ∀ x, x v = false → V i x = b) ∨
          ∃ j < i, ∀ x, x v = false → V i x = V j x)) → T.card+15 ≤ C.size) →
      ∃ x, C.eval (w x) ≠ ([(1 : ℕ),12,23,34,40,5,16,27,38,49,57,79,96,68,85].any
        fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       List.countP             (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) =>               have x5 : List ℕ := PEqualNP.CircuitLowerBounds.GateOp.rec x4.inputs x4.inputs (List.take (1 : ℕ) x4.inputs) (fun (x5 : ℕ) => x4.inputs) x4.inputs x4.op;               x5.contains (0 : ℕ) || x5.contains (10 : ℕ))             x1.gates ≤           (3 : ℕ) →         ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C legal small _reads
  by_contra! comp
  let f : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let h : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = f x := comp
  have anyEq (x : Fin 10 → Bool) : ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) = f x := by
    simp only [List.any_cons, List.any_nil, Bool.or_false, f, Bool.or_assoc]
    rfl
  obtain ⟨bad, ne⟩ := core C legal small (by
    intro v T hT
    suffices iso : ∃ (u : Fin 9) (p : Fin 10 → ℕ), (u = 0 ∨ u = 4) ∧ (p 0 = u.val ∨ 9 ≤ p 0) ∧
        p v = 9 ∧ ∀ y : Fin 9 → Bool, f (fun i => (List.ofFn y).getD (p i) false) = h y by
      obtain ⟨u,p,hu,hp,hv,iso⟩ := iso
      let x := fun (y : Fin 9 → Bool) i => (List.ofFn y).getD (p i) false
      have xoff y : x y v = false := by simp [x,hv,List.getD_eq_getElem?_getD]
      have he y : C.eval (List.ofFn (x y) ++ [!x y 0]) = h y := (hc _).trans (iso _)
      rcases compress C u p T legal hp (by
        intro i hi
        obtain ⟨lo,hi,alt⟩ := hT i hi
        refine ⟨lo,hi,?_⟩
        rcases alt with ⟨b,hb⟩ | ⟨j,hj,eq⟩
        · exact Or.inl ⟨b,fun y => hb (x y) (xoff y)⟩
        · exact Or.inr ⟨j,hj,fun y => eq (x y) (xoff y)⟩) with ⟨b,hb⟩ | ⟨D,hD,sz,first,Dval⟩
      · have h0 : h (fun _ => false) = false := by decide
        have h1 : h (fun _ => true) = true := by decide
        have e0 : false = b := h0.symm.trans ((he (fun _ => false)).symm.trans (hb _))
        have e1 : true = b := h1.symm.trans ((he (fun _ => true)).symm.trans (hb _))
        exact False.elim (Bool.false_ne_true (e0.trans e1.symm))
      · have eq : circuitFun 9 D = h := funext fun y => (Dval y).trans (he y)
        rcases hu with rfl|rfl
        · have := degreeThree D hD first eq; omega
        · have := degreeTwo D hD first eq; omega
    fin_cases v
    · refine ⟨0,fun i => ([9,4,0,1,6,7,3,5,2,8] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((false && y 4) || (y 4 && y 0) || (y 0 && y 1) || (y 1 && y 6) || (y 6 && false) || (false && y 7) || (y 4 && y 3) || (y 0 && y 5) || (y 1 && y 2) || (y 6 && y 8) || (y 7 && y 5) || (y 5 && y 8) || (y 8 && y 3) || (y 3 && y 2) || (y 2 && y 7)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false] <;> ac_rfl
    · refine ⟨4,fun i => ([4,9,6,1,0,3,7,8,2,5] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 4 && false) || (false && y 6) || (y 6 && y 1) || (y 1 && y 0) || (y 0 && y 4) || (y 4 && y 3) || (false && y 7) || (y 6 && y 8) || (y 1 && y 2) || (y 0 && y 5) || (y 3 && y 8) || (y 8 && y 5) || (y 5 && y 7) || (y 7 && y 2) || (y 2 && y 3)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false] <;> ac_rfl
    · refine ⟨0,fun i => ([0,4,9,6,1,5,3,7,8,2] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 0 && y 4) || (y 4 && false) || (false && y 6) || (y 6 && y 1) || (y 1 && y 0) || (y 0 && y 5) || (y 4 && y 3) || (false && y 7) || (y 6 && y 8) || (y 1 && y 2) || (y 5 && y 7) || (y 7 && y 2) || (y 2 && y 3) || (y 3 && y 8) || (y 8 && y 5)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨0,fun i => ([0,1,6,9,4,5,2,8,7,3] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 0 && y 1) || (y 1 && y 6) || (y 6 && false) || (false && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 2) || (y 6 && y 8) || (false && y 7) || (y 4 && y 3) || (y 5 && y 8) || (y 8 && y 3) || (y 3 && y 2) || (y 2 && y 7) || (y 7 && y 5)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨4,fun i => ([4,0,1,6,9,3,5,2,8,7] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 4 && y 0) || (y 0 && y 1) || (y 1 && y 6) || (y 6 && false) || (false && y 4) || (y 4 && y 3) || (y 0 && y 5) || (y 1 && y 2) || (y 6 && y 8) || (false && y 7) || (y 3 && y 2) || (y 2 && y 7) || (y 7 && y 5) || (y 5 && y 8) || (y 8 && y 3)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨4,fun i => ([4,0,1,2,3,9,5,6,7,8] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 4 && y 0) || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && false) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (false && y 6) || (y 6 && y 8) || (y 8 && y 5) || (y 5 && y 7) || (y 7 && false)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨0,fun i => ([0,4,3,2,1,5,9,8,7,6] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 0 && y 4) || (y 4 && y 3) || (y 3 && y 2) || (y 2 && y 1) || (y 1 && y 0) || (y 0 && y 5) || (y 4 && false) || (y 3 && y 8) || (y 2 && y 7) || (y 1 && y 6) || (y 5 && y 8) || (y 8 && y 6) || (y 6 && false) || (false && y 7) || (y 7 && y 5)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨0,fun i => ([0,1,6,8,5,4,2,9,3,7] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 0 && y 1) || (y 1 && y 6) || (y 6 && y 8) || (y 8 && y 5) || (y 5 && y 0) || (y 0 && y 4) || (y 1 && y 2) || (y 6 && false) || (y 8 && y 3) || (y 5 && y 7) || (y 4 && false) || (false && y 7) || (y 7 && y 2) || (y 2 && y 3) || (y 3 && y 4)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨0,fun i => ([0,1,2,7,5,4,6,3,9,8] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 7) || (y 7 && y 5) || (y 5 && y 0) || (y 0 && y 4) || (y 1 && y 6) || (y 2 && y 3) || (y 7 && false) || (y 5 && y 8) || (y 4 && y 3) || (y 3 && y 8) || (y 8 && y 6) || (y 6 && false) || (false && y 4)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl
    · refine ⟨0,fun i => ([0,1,2,3,4,5,6,7,8,9] : List ℕ).getD i.val 9,by decide,by decide,by decide,?_⟩
      intro y
      change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 4 && false) || (y 5 && y 7) || (y 7 && false) || (false && y 6) || (y 6 && y 8) || (y 8 && y 5)) = h y
      simp only [h, Bool.false_and, Bool.and_false, Bool.or_false] <;> ac_rfl)
  exact ne ((hc bad).trans (anyEq bad).symm)
