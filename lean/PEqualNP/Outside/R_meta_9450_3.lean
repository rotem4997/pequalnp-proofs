import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_9450_3
    (hmono :
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 27 D →
        ∀ (w : ℕ), Monotone (fun x : Fin 26 → Bool =>
          (D.wires (List.ofFn x ++ [x 1 || x 2])).getD w false))
    (hcert :
      let E : Fin 13 → Fin 13 → Prop :=
        fun p l => l ≠ 1 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (useOr : Bool)
        (a : Fin (27 + D.size)) (s : List (Fin (27 + D.size))),
        let eval (x : Fin 26 → Bool) : Bool :=
          let w := D.wires (List.ofFn x ++ [x 1 || x 2])
          if useOr = true then (a :: s).any (fun i => w.getD (↑i) false)
          else (a :: s).all (fun i => w.getD (↑i) false)
        s ≠ [] ∧ (a :: s).Nodup ∧ D.size + s.length ≤ 58 ∧
          PEqualNP.TopForm.IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ p l : Fin 13, E p l →
            eval (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
          (∀ y : Fin 13 → Bool,
            eval (Fin.append y (fun l => decide (∀ p, y p = true → ¬ E p l))) = false)) :
    (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x3 ≠ (1 : Fin (13 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool) (x4 : Fin ((27 : ℕ) + x2.size)) (x5 : List (Fin ((27 : ℕ) + x2.size))),   x5 ≠ [] ∧     (x4 :: x5).Nodup ∧       x2.size + x5.length ≤ (58 : ℕ) ∧         PEqualNP.TopForm.IsAO2 (27 : ℕ) x2 ∧           (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧             ∀ (x6 : Fin (26 : ℕ) → Bool),               Minimal x1 x6 ∨ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x1 x7) x6 →                 have x8 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (1 : Fin (26 : ℕ)) || x6 (2 : Fin (26 : ℕ))]);                 (if x3 = Bool.true then (x4 :: x5).any fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false else (x4 :: x5).all fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false) = Bool.true ↔ x1 x6) := by
  classical
  let E : Fin 13 → Fin 13 → Prop :=
    fun p l => l ≠ 1 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
  obtain ⟨D, useOr, a, s, hs, hnodup, hsize, hao2, hgnodup, hpos, hneg⟩ := hcert
  let eval (x : Fin 26 → Bool) : Bool :=
    let w := D.wires (List.ofFn x ++ [x 1 || x 2])
    if useOr = true then (a :: s).any (fun i => w.getD (↑i) false)
    else (a :: s).all (fun i => w.getD (↑i) false)
  change ∀ p l : Fin 13, E p l →
    eval (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true at hpos
  change ∀ y : Fin 13 → Bool,
    eval (Fin.append y (fun l => decide (∀ p, y p = true → ¬ E p l))) = false at hneg
  have hm := hmono D hao2
  have heval_mono : Monotone eval := by
    intro x y hxy
    dsimp only [eval]
    cases useOr
    · change ((a :: s).all fun i => (D.wires (List.ofFn x ++ [x 1 || x 2])).getD (↑i) false) ≤
        ((a :: s).all fun i => (D.wires (List.ofFn y ++ [y 1 || y 2])).getD (↑i) false)
      cases h : (a :: s).all fun i => (D.wires (List.ofFn x ++ [x 1 || x 2])).getD (↑i) false
      · exact Bool.false_le _
      · rw [List.all_eq_true] at h
        have h' : ((a :: s).all fun i => (D.wires (List.ofFn y ++ [y 1 || y 2])).getD (↑i) false) = true := by
          rw [List.all_eq_true]
          intro i hi
          exact Bool.eq_true_of_true_le ((h i hi) ▸ hm (↑i) hxy)
        rw [h']
    · change ((a :: s).any fun i => (D.wires (List.ofFn x ++ [x 1 || x 2])).getD (↑i) false) ≤
        ((a :: s).any fun i => (D.wires (List.ofFn y ++ [y 1 || y 2])).getD (↑i) false)
      cases h : (a :: s).any fun i => (D.wires (List.ofFn x ++ [x 1 || x 2])).getD (↑i) false
      · exact Bool.false_le _
      · rw [List.any_eq_true] at h
        obtain ⟨i, hi, hwi⟩ := h
        have h' : ((a :: s).any fun i => (D.wires (List.ofFn y ++ [y 1 || y 2])).getD (↑i) false) = true := by
          rw [List.any_eq_true]
          exact ⟨i, hi, Bool.eq_true_of_true_le (hwi ▸ hm (↑i) hxy)⟩
        rw [h']
  intro x1
  refine ⟨D, useOr, a, s, hs, hnodup, hsize, hao2, hgnodup, ?_⟩
  intro x6 hx6
  change eval x6 = true ↔ x1 x6
  rcases hx6 with hmin | hmax
  · constructor
    · intro _
      exact hmin.1
    · rintro ⟨p, l, hl, he, hp, hlval⟩
      let z : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      have hle : z ≤ x6 := by
        intro i
        by_cases h : i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l
        · rcases h with rfl | rfl
          · change decide (_ ∨ _) ≤ _
            rw [show decide (Fin.castAdd 13 p = Fin.castAdd 13 p ∨ Fin.castAdd 13 p = Fin.natAdd 13 l) = true from decide_eq_true (Or.inl rfl), hp]
          · change decide (_ ∨ _) ≤ _
            rw [show decide (Fin.natAdd 13 l = Fin.castAdd 13 p ∨ Fin.natAdd 13 l = Fin.natAdd 13 l) = true from decide_eq_true (Or.inr rfl), hlval]
        · change decide (_ ∨ _) ≤ _
          rw [decide_eq_false h]
          exact Bool.false_le _
      exact Bool.eq_true_of_true_le ((hpos p l ⟨hl, he⟩) ▸ heval_mono hle)
  · constructor
    · intro heval
      exfalso
      let a1 : Fin 13 → Bool := fun p => x6 (Fin.castAdd 13 p)
      let b1 : Fin 13 → Bool := fun l => decide (∀ p, a1 p = true → ¬ E p l)
      let u : Fin 26 → Bool := Fin.append a1 b1
      have hle : x6 ≤ u := by
        intro i
        refine Fin.addCases (n := 13) (m := 13) (fun p => ?_) (fun l => ?_) i
        · simp [u, a1, Fin.append_left]
        · simp only [u, Fin.append_right]
          change x6 (Fin.natAdd 13 l) ≤ b1 l
          cases hl : x6 (Fin.natAdd 13 l)
          · exact Bool.false_le _
          · have hb : b1 l = true := by
              apply decide_eq_true
              intro p hp he
              exact hmax.1 ⟨p, l, he.1, he.2, hp, hl⟩
            simp [hb]
      have hfalse : eval u = false := hneg a1
      have hle' := heval_mono hle
      rw [heval, hfalse] at hle'
      contradiction
    · intro hx
      exact False.elim (hmax.1 hx)
