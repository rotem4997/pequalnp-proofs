import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_7368_746
    (hcover : ∀ (E : Fin 12 → Fin 12 → Prop) [DecidableRel E],
    let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
    let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
    ∀ x : Fin (12+12) → Bool,
      (¬ ∃ i j, E i j ∧ x (Fin.castAdd 12 i) = true ∧ x (Fin.natAdd 12 j) = true) →
      ∃ s : Fin 12 → Bool, M (N s) = s ∧ ∀ i, x i = true → Fin.addCases s (N s) i = true)
    (hwires : ∀ (C : Circuit), Monotone2 C → ∀ (x y : Fin 24 → Bool),
    (∀ i, x i = true → y i = true) → ∀ k,
    (C.wires (List.ofFn x)).getD k false = true →
    (C.wires (List.ofFn y)).getD k false = true)
    (hcert : let D : Finset (Fin 13) := {0, 1, 3, 9}
    let E := fun i j : Fin 12 =>
      Fin.succAbove (9 : Fin 13) i + Fin.succAbove (0 : Fin 13) j ∈ D
    let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
    let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
    let Q := fun b : Bool => if b then ({15, 16, 18} : Finset (Fin 24)) else {0, 1, 3}
    ∃ (C : Circuit) (a b : ℕ), Monotone2 C ∧ C.size ≤ 58 ∧
      C.gates.head? = some ⟨.or, [0,1]⟩ ∧ max C.output (max a b) < 24+C.size ∧
      (∀ i j, E i j → C.eval (List.ofFn fun k : Fin 24 =>
        decide (k = Fin.castAdd 12 i ∨ k = Fin.natAdd 12 j)) = true) ∧
      (∀ t i, i ∈ Q t → (C.wires (List.ofFn fun k : Fin 24 => decide (k = i))).getD
        (if t then b else a) false = true) ∧
      ∀ s, M (N s) = s →
        let z : Fin 24 → Bool := Fin.append s (N s)
        C.eval (List.ofFn z) = false ∧
        ∀ t, (C.wires (List.ofFn fun k => if k ∈ Q t then false else z k)).getD
          (if t then b else a) false = false) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 + x3 ∈ x1; have x3 : (Fin (24 : ℕ) → Bool) → Prop := fun (x3 : Fin (24 : ℕ) → Bool) => ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (12 : ℕ)), x2 (Fin.succAbove (9 : Fin (13 : ℕ)) x4) (Fin.succAbove (0 : Fin (13 : ℕ)) x5) ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (58 : ℕ) ∧ x4.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4.output < (24 : ℕ) + x4.size ∧ x5 < (24 : ℕ) + x4.size ∧ x6 < (24 : ℕ) + x4.size ∧ (∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.true ↔ x3 x7) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.false → (x4.wires (List.ofFn x7)).getD x5 Bool.false = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ (x4.wires (List.ofFn x7)).getD x6 Bool.false = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))) := by
  let E := fun i j : Fin 12 =>
      Fin.succAbove (9 : Fin 13) i + Fin.succAbove (0 : Fin 13) j ∈
        ({0, 1, 3, 9} : Finset (Fin 13))
  let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
  let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
  let Q := fun b : Bool => if b then ({15, 16, 18} : Finset (Fin 24)) else {0, 1, 3}
  obtain ⟨C, a, b, hm, hs, hfirst, bounds, hpair, hunit, hmax⟩ := hcert
  obtain ⟨ho, hab⟩ := max_lt_iff.mp bounds
  obtain ⟨ha, hb⟩ := max_lt_iff.mp hab
  let val := fun (k : ℕ) (x : Fin 24 → Bool) => (C.wires (List.ofFn x)).getD k false
  let edge := fun x : Fin 24 → Bool => ∃ i j, E i j ∧
    x (Fin.castAdd 12 i) = true ∧ x (Fin.natAdd 12 j) = true
  have mono (x y : Fin 24 → Bool) (hle : ∀ i, x i = true → y i = true) (k : ℕ) :
      val k x = true → val k y = true := hwires C hm x y hle k
  have accepts (x : Fin 24 → Bool) (hx : edge x) : C.eval (List.ofFn x) = true := by
    obtain ⟨i, j, he, hi, hj⟩ := hx
    apply mono _ x ?_ C.output (hpair i j he)
    intro k hk
    rcases of_decide_eq_true hk with rfl | rfl <;> assumption
  have rejects (x : Fin 24 → Bool) (hx : ¬ edge x) : C.eval (List.ofFn x) = false := by
    obtain ⟨s, hc, hxz⟩ := hcover E x hx
    have hz := (hmax s hc).1
    cases hv : C.eval (List.ofFn x) with
    | false => rfl
    | true => exact Bool.noConfusion ((mono x _ hxz C.output hv).symm.trans hz)
  have tagCorrect (x : Fin 24 → Bool) (hx : ¬ edge x) (t : Bool) :
      val (if t then b else a) x = decide (∃ i ∈ Q t, x i = true) := by
    by_cases hit : ∃ i ∈ Q t, x i = true
    · rw [decide_eq_true hit]
      obtain ⟨i, mem, on⟩ := hit
      apply mono _ x ?_ _ (hunit t i mem)
      intro j hj
      obtain rfl := of_decide_eq_true hj
      exact on
    · rw [decide_eq_false hit]
      obtain ⟨s, hc, hxz⟩ := hcover E x hx
      let z : Fin 24 → Bool := Fin.append s (N s)
      have le : ∀ k, x k = true → (if k ∈ Q t then false else z k) = true := by
        intro k on
        by_cases h : k ∈ Q t
        · exact (hit ⟨k, h, on⟩).elim
        · rw [if_neg h]
          exact hxz k on
      have hz := (hmax s hc).2 t
      cases hv : val (if t then b else a) x with
      | false => rfl
      | true => exact Bool.noConfusion ((mono x _ le _ hv).symm.trans hz)
  refine ⟨C, a, b, hm, hs, hfirst, ho, ha, hb, ?_, ?_⟩
  · intro x
    constructor
    · intro yes
      by_contra hx
      exact Bool.noConfusion (yes.symm.trans (rejects x hx))
    · exact accepts x
  · intro x no
    have hx : ¬ edge x := fun e => Bool.noConfusion ((accepts x e).symm.trans no)
    have tags (u v w : Fin 24) : decide (∃ i ∈ ({u,v,w} : Finset (Fin 24)), x i = true) =
        (x u || x v || x w) := by
      apply Bool.eq_iff_iff.mpr
      simp [Finset.mem_insert, or_and_right, exists_or, or_assoc]
    constructor
    · exact (tagCorrect x hx false).trans (tags 0 1 3)
    · exact (tagCorrect x hx true).trans (tags 15 16 18)
