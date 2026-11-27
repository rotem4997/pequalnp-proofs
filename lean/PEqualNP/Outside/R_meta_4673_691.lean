import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4673_691
    (hSearch :
      let E (p : Fin 9) (l : Fin 12) : Prop :=
        (([1,3,4,5,6,7,9,10,11] : List ℕ).getD p.val 0 + l.val + 15) % 13 ∈
          ([0,1,3,9] : List ℕ)
      let Z (p : Fin 9 → Bool) (l : Fin 12) : Bool := decide (∀ i, E i l → p i = false)
      ∃ (C : Circuit) (u : ℕ), IsAO2 21 C ∧ C.size ≤ 45 ∧
        C.output < 21+C.size ∧ u < 21+C.size ∧
        (∀ i < C.size, (gateAt C i).inputs.Nodup ∧
          (21+i = C.output ∨ 21+i = u ∨ ∃ j < C.size, 21+i ∈ (gateAt C j).inputs)) ∧
        (∀ p l, E p l → C.eval (List.ofFn fun i : Fin 21 =>
          decide (i = Fin.castAdd 12 p ∨ i = Fin.natAdd 9 l)) = true) ∧
        (∀ j : Fin 21, j = 9 ∨ j = 11 ∨ j = 17 →
          (C.wires (List.ofFn fun i : Fin 21 => decide (i = j))).getD u false = true) ∧
        ∀ (b : Bool) (p : Fin 9 → Bool),
          (C.wires (List.ofFn (Fin.addCases p (fun l : Fin 12 =>
            Z p l && (b || !(decide (l = 0 ∨ l = 2 ∨ l = 8))))))).getD
            (if b then C.output else u) false = false)
    (hMono : ∀ (C : Circuit), IsAO2 21 C → ∀ (x y : Fin 21 → Bool),
      (∀ i, x i = true → y i = true) → ∀ w : ℕ,
      (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 (21 : ℕ) x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (21 : ℕ) + x1.size ∧ x2 < (21 : ℕ) + x1.size ∧ (∀ x3 < x1.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs.Nodup ∧ ((21 : ℕ) + x3 = x1.output ∨ (21 : ℕ) + x3 = x2 ∨ ∃ x5 < x1.size, (21 : ℕ) + x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).inputs)) ∧ ∀ (x3 : Fin (21 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (9 : ℕ)) (x5 : Fin (12 : ℕ)), ([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD ↑x4 (0 : ℕ) + ↑x5 + (15 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (9 : ℕ) x5) = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (9 : Fin (21 : ℕ)) || x3 (11 : Fin (21 : ℕ)) || x3 (17 : Fin (21 : ℕ)))) := by
  let E (p : Fin 9) (l : Fin 12) : Prop :=
    (([1,3,4,5,6,7,9,10,11] : List ℕ).getD p.val 0 + l.val + 15) % 13 ∈
      ([0,1,3,9] : List ℕ)
  let Z (p : Fin 9 → Bool) (l : Fin 12) : Bool := decide (∀ i, E i l → p i = false)
  obtain ⟨C,u,hmodel,hsize,hout,hu,hused,hpos,hauxpos,hneg⟩ := hSearch
  have mono := hMono C hmodel
  have positive (p : Fin 9) (l : Fin 12) (h : E p l) :
      C.eval (List.ofFn fun i : Fin 21 =>
        decide (i = Fin.castAdd 12 p ∨ i = Fin.natAdd 9 l)) = true := hpos p l h
  have mainNeg (p : Fin 9 → Bool) :
      C.eval (List.ofFn (Fin.addCases p (Z p))) = false := by
    change (C.wires (List.ofFn (Fin.addCases p (Z p)))).getD C.output false = false
    simpa only [Bool.true_or, Bool.and_true, ite_true] using hneg true p
  have auxNeg (p : Fin 9 → Bool) :
      (C.wires (List.ofFn (Fin.addCases p (fun l : Fin 12 =>
        Z p l && !(decide (l = 0 ∨ l = 2 ∨ l = 8)))))).getD u false = false := by
    exact hneg false p
  have mainSpec (x : Fin 21 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ p l, E p l ∧ x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 9 l) = true := by
    constructor
    · intro hon
      by_contra hnone
      let p : Fin 9 → Bool := fun i => x (Fin.castAdd 12 i)
      have lift : ∀ i : Fin 21, x i = true → Fin.addCases p (Z p) i = true := by
        intro i
        refine Fin.addCases (m := 9) (n := 12) (fun a ha => ?_) (fun l hl => ?_) i
        · simpa [p] using ha
        · simp only [Fin.addCases_right, Z, decide_eq_true_eq]
          intro a hea
          cases hp : p a with
          | false => rfl
          | true => exact False.elim (hnone ⟨a,l,hea,hp,hl⟩)
      have bad := mono x (fun i => Fin.addCases p (Z p) i) lift C.output hon
      change C.eval (List.ofFn (Fin.addCases p (Z p))) = true at bad
      rw [mainNeg p] at bad
      contradiction
    · rintro ⟨p,l,hpl,hp,hl⟩
      apply mono _ x _ C.output (positive p l hpl)
      intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hp
      · exact hl
  refine ⟨C,u,hmodel,hsize,hout,hu,hused,?_⟩
  intro x
  refine ⟨mainSpec x, ?_⟩
  intro hoff
  let p : Fin 9 → Bool := fun i => x (Fin.castAdd 12 i)
  have hnone : ¬ ∃ a l, E a l ∧ x (Fin.castAdd 12 a) = true ∧
      x (Fin.natAdd 9 l) = true := by
    intro h
    have := (mainSpec x).mpr h
    rw [hoff] at this
    contradiction
  cases ht : (x 9 || x 11 || x 17) with
  | true =>
    have some : ∃ j : Fin 21, (j = 9 ∨ j = 11 ∨ j = 17) ∧ x j = true := by
      simp only [Bool.or_eq_true] at ht
      rcases ht with (h | h) | h
      · exact ⟨9,Or.inl rfl,h⟩
      · exact ⟨11,Or.inr (Or.inl rfl),h⟩
      · exact ⟨17,Or.inr (Or.inr rfl),h⟩
    obtain ⟨j,hj,hxj⟩ := some
    apply mono _ x _ u (hauxpos j hj)
    intro i hi
    simp only [decide_eq_true_eq] at hi
    simpa [hi] using hxj
  | false =>
    have zeros : x 9 = false ∧ x 11 = false ∧ x 17 = false := by
      simpa only [Bool.or_eq_false_iff, and_assoc] using ht
    let y : Fin 21 → Bool := fun i => Fin.addCases p (fun l : Fin 12 =>
      Z p l && !(decide (l = 0 ∨ l = 2 ∨ l = 8))) i
    have lift : ∀ i : Fin 21, x i = true → y i = true := by
      intro i
      refine Fin.addCases (m := 9) (n := 12) (fun a ha => ?_) (fun l hl => ?_) i
      · simpa [y,p] using ha
      · simp only [y, Fin.addCases_right]
        apply Bool.and_eq_true_iff.mpr
        constructor
        · simp only [Z, decide_eq_true_eq]
          intro a hea
          cases hp : p a with
          | false => rfl
          | true => exact False.elim (hnone ⟨a,l,hea,hp,hl⟩)
        · have away : ¬ (l = 0 ∨ l = 2 ∨ l = 8) := by
            rintro (rfl | rfl | rfl)
            · have := zeros.1
              change x 9 = true at hl
              rw [this] at hl
              contradiction
            · have := zeros.2.1
              change x 11 = true at hl
              rw [this] at hl
              contradiction
            · have := zeros.2.2
              change x 17 = true at hl
              rw [this] at hl
              contradiction
          simp [away]
    cases hv : (C.wires (List.ofFn x)).getD u false with
    | false => rfl
    | true =>
      have bad := mono x y lift u hv
      have off := auxNeg p
      change (C.wires (List.ofFn y)).getD u false = false at off
      rw [off] at bad
      contradiction
