import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK in
theorem PEqualNP.Outside.R_meta_17239_1
    (synth : ∃ C : Circuit, C.size ≤ 27 ∧
      (∀ j (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
          g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
        C.eval (List.ofFn fun i : Fin 14 =>
          decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) ∧
      (∀ m ∈ ([127, 244, 480, 720, 1188, 3008, 16256] : List ℕ), ∀ r : Fin 7,
        C.eval (List.ofFn (Fin.addCases
          (fun p : Fin 7 => m.testBit (p + r).val)
          (fun l : Fin 7 => m.testBit (7 + (l + r).val)))) = false) ∧
      ∀ v ∈ ([0, 7] : List ℕ), 2 ≤ ((scalarMults C 14 [0, 7] v).getD C.output none).getD 2)
    (cover : ∀ A : Fin 7 → Bool, ∃ m ∈ ([127, 244, 480, 720, 1188, 3008, 16256] : List ℕ), ∃ r : Fin 7,
      (∀ p : Fin 7, A p = true → m.testBit (p + r).val = true) ∧
      (∀ l : Fin 7, A l = false → A (l + 1) = false → A (l + 3) = false →
        m.testBit (7 + (l + r).val) = true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧ (∀ (x2 : Fin (7 : ℕ) → Bool), x1.eval (List.ofFn fun (x3 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x2 (fun (x4 : Fin (7 : ℕ)) => !(x2 x4 || x2 (x4 + (1 : Fin (7 : ℕ))) || x2 (x4 + (3 : Fin (7 : ℕ))))) x3) = Bool.false) ∧ ∀ x2 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (14 : ℕ) [(0 : ℕ), (7 : ℕ)] x2).getD x1.output Option.none).getD (2 : ℕ) := by
  classical
  obtain ⟨C, hs, hshape, hpos, hneg, hmult⟩ := synth
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] := by
    intro g hg
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨ho, a, b, hab, _, _, _⟩ := hshape j g (List.getElem?_eq_some_iff.mpr ⟨hj, he⟩)
    exact ⟨ho, a, b, hab⟩
  have stepMono (u v : List Bool) (g : Gate)
      (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b])
      (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (step u g).getD i false = true → (step v g).getD i false = true := by
    intro i hi
    by_cases hlt : i < u.length
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
      by_cases hz : i - u.length = 0
      · simp only [hz, List.getD_cons_zero] at hi ⊢
        obtain ⟨ho, a, b, hab⟩ := hg
        rcases ho with ho | ho
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].all id) = true at hi
          change ([v.getD a false, v.getD b false].all id) = true
          simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, Bool.and_eq_true] at hi ⊢
          exact ⟨h a hi.1, h b hi.2⟩
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].any id) = true at hi
          change ([v.getD a false, v.getD b false].any id) = true
          simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true] at hi ⊢
          exact hi.elim (fun ha => Or.inl (h a ha)) (fun hb => Or.inr (h b hb))
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
  have runMono : ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b]) →
      ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (run gs u).getD i false = true → (run gs v).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ _ _ _ h i hi; exact h i hi
    | cons g gs ih =>
      intro hg u v hlen h i hi
      change (run gs (step u g)).getD i false = true at hi
      change (run gs (step v g)).getD i false = true
      exact ih (fun k hk => hg k (by simp [hk])) _ _
        (by simp [step, hlen]) (stepMono u v g (hg g (by simp)) hlen h) i hi
  have evalMono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply runMono C.gates hG _ _ (by simp) ?_ C.output
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    split at hi
    · rename_i hlt
      simp [hlt] at hi ⊢
      exact h _ hi
    · simp at hi
  refine ⟨C, hs, hshape, hpos, ?_, hmult⟩
  intro A
  by_contra htrue
  have hx : C.eval (List.ofFn fun x3 : Fin (7 + 7) =>
      Fin.addCases A (fun x4 : Fin 7 => !(A x4 || A (x4 + 1) || A (x4 + 3))) x3) = true := by
    cases hev : C.eval (List.ofFn fun x3 : Fin (7 + 7) =>
        Fin.addCases A (fun x4 : Fin 7 => !(A x4 || A (x4 + 1) || A (x4 + 3))) x3)
    · exact (htrue hev).elim
    · rfl
  obtain ⟨m, hm, r, hp, hl⟩ := cover A
  let y : Fin 14 → Bool := fun i => Fin.addCases (motive := fun _ => Bool)
    (fun p : Fin 7 => m.testBit (p + r).val)
    (fun l : Fin 7 => m.testBit (7 + (l + r).val)) i
  have hxy : ∀ i : Fin 14,
      (Fin.addCases A (fun x4 : Fin 7 => !(A x4 || A (x4 + 1) || A (x4 + 3))) i) = true →
      y i = true := by
    intro i
    refine Fin.addCases (m := 7) (n := 7)
      (motive := fun j => Fin.addCases A (fun x4 : Fin 7 => !(A x4 || A (x4 + 1) || A (x4 + 3))) j = true → y j = true)
      ?_ ?_ i
    · intro p hxp
      rw [Fin.addCases_left] at hxp
      simpa only [y, Fin.addCases_left] using hp p hxp
    · intro l hxl
      rw [Fin.addCases_right] at hxl
      have off0 : A l = false := by cases h : A l <;> simp_all
      have off1 : A (l + 1) = false := by cases h : A (l + 1) <;> simp_all
      have off3 : A (l + 3) = false := by cases h : A (l + 3) <;> simp_all
      simpa only [y, Fin.addCases_right] using hl l off0 off1 off3
  have hyt := evalMono _ y hxy hx
  have hyf : C.eval (List.ofFn y) = false := hneg m hm r
  rw [hyf] at hyt
  cases hyt
