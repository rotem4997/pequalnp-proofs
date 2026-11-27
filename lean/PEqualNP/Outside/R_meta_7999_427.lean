import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_7999_427
    (anchor :
      let mark : List Bool := (List.range 14).map fun i => i == 0 || i == 7
      ∀ D : Circuit, D.size ≤ 26 → TopForm.IsAO2 15 D →
      (∀ j < D.size, TopForm.opnd D j 0 ≠ TopForm.opnd D j 1) →
      (∀ x : Fin 14 → Bool, let w := List.ofFn x
        D.eval (w ++ [w.getD 0 false && w.getD 7 false]) = true ↔
        ∃ p w : Fin 7, (p = w ∨ p = w + 1 ∨ p = w + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 w) = true) →
      (((ReadK.linearParts D (fun i => decide (7 ≤ i)) (mark ++ [true])).getD D.output (false, false)).2 = true ∨
       ((ReadK.linearParts D (fun i => decide (i < 7 ∨ i = 14)) (mark ++ [true])).getD D.output (false, false)).2 = true))
    (offAnchor :
      let mark : List Bool := (List.range 14).map fun i => i == 0 || i == 7
      ∀ u ∈ ([(0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)), ∀ D : Circuit, D.size ≤ 26 → TopForm.IsAO2 15 D →
      (∀ j < D.size, TopForm.opnd D j 0 ≠ TopForm.opnd D j 1) →
      (∀ x : Fin 14 → Bool, let w := List.ofFn x
        D.eval (w ++ [w.getD u.1 false && w.getD u.2 false]) = true ↔
        ∃ p w : Fin 7, (p = w ∨ p = w + 1 ∨ p = w + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 w) = true) →
      (((ReadK.linearParts D (fun i => decide (7 ≤ i)) (mark ++ [false])).getD D.output (false, false)).2 = true ∨
       ((ReadK.linearParts D (fun i => decide (i < 7 ∨ i = 14)) (mark ++ [false])).getD D.output (false, false)).2 = true)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∃ x5 ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (11 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (8 : ℕ))], PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5.1, x5.2] : PEqualNP.CircuitLowerBounds.Gate }) → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7)) [((0 : ℕ), (7 : ℕ))] → False) := by
  intro C hsize hao hdist hfst hF hbad
  obtain ⟨u, hu, hgate⟩ := hfst
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil =>
    have hh := congrArg Gate.op hgate
    cases hh
  | cons g gs =>
    change g = ⟨GateOp.and, [u.1, u.2]⟩ at hgate
    subst g
    let D : Circuit := ⟨gs, out⟩
    have hbound : D.size ≤ 26 := Nat.le_of_succ_le_succ hsize
    have hAO : TopForm.IsAO2 15 D := by
      refine ⟨fun g hg => hao.1 g (List.mem_cons_of_mem _ hg), ?_,
        fun g hg => hao.2.2 g (List.mem_cons_of_mem _ hg)⟩
      intro j hj i hi
      have hh := hao.2.1 (j+1) (Nat.succ_lt_succ hj) i hi
      omega
    have hdistinct : ∀ j < D.size, TopForm.opnd D j 0 ≠ TopForm.opnd D j 1 :=
      fun j hj => hdist (j+1) (Nat.succ_lt_succ hj)
    have interpret (x : Fin 14 → Bool) :
        let w := List.ofFn x
        D.eval (w ++ [w.getD u.1 false && w.getD u.2 false]) = true ↔
        ∃ p w : Fin 7, (p = w ∨ p = w + 1 ∨ p = w + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 w) = true := by
      have hand : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by decide
      convert hF x using 2 <;> delta Circuit.eval Circuit.wires <;> dsimp only [D, List.foldl_cons, List.map_cons, List.map_nil] <;> simp only [List.map_cons, List.map_nil, hand]
    apply hbad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rcases anchor D hbound hAO hdistinct interpret with ha | hb
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [0, 7]⟩ :: gs, out⟩ : Circuit) 14 (fun i => decide (7 ≤ i)) 0 7 = true := ha
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [0, 7]⟩ :: gs, out⟩ : Circuit) 14 (fun i => !decide (7 ≤ i)) 0 7 = true := hb
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
    · rcases offAnchor _ (by decide) D hbound hAO hdistinct interpret with ha | hb
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [0, 11]⟩ :: gs, out⟩ : Circuit) 14 (fun i => decide (7 ≤ i)) 0 7 = true := ha
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [0, 11]⟩ :: gs, out⟩ : Circuit) 14 (fun i => !decide (7 ≤ i)) 0 7 = true := hb
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
    · rcases offAnchor _ (by decide) D hbound hAO hdistinct interpret with ha | hb
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [1, 8]⟩ :: gs, out⟩ : Circuit) 14 (fun i => decide (7 ≤ i)) 0 7 = true := ha
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [1, 8]⟩ :: gs, out⟩ : Circuit) 14 (fun i => !decide (7 ≤ i)) 0 7 = true := hb
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
    · rcases offAnchor _ (by decide) D hbound hAO hdistinct interpret with ha | hb
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [2, 8]⟩ :: gs, out⟩ : Circuit) 14 (fun i => decide (7 ≤ i)) 0 7 = true := ha
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
      · have hs : ReadK.lineSingle (⟨⟨GateOp.and, [2, 8]⟩ :: gs, out⟩ : Circuit) 14 (fun i => !decide (7 ≤ i)) 0 7 = true := hb
        delta ReadK.IsSingleRead ReadK.doubleReread
        simp [hs]
