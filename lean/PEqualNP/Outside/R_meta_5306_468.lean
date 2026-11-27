import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The eight masks generate the maximal arc pairs by shifts, multipliers and duality.
theorem PEqualNP.Outside.R_meta_5306_468
    (valid :
      let row (w : ℕ) (s : Fin 13) (m : ℕ) (d : Bool) (i : Fin 26) :=
        w.testBit ((((if d then 13-m else m)*i.val+s.val)%13) +
          13*(if d then 1-i.val/13 else i.val/13))
      ∀ w ∈ ([7405575,23330829,5799955,22282261,21757977,21233693,19415081,5275731] : List ℕ), ∀ s : Fin 13, ∀ m ∈ ([1,3,9] : List ℕ), ∀ d : Bool,
        let P := Finset.univ.filter (fun p : Fin 13 => row w s m d (Fin.castAdd 13 p))
        let W := Finset.univ.filter (fun l : Fin 13 => row w s m d (Fin.natAdd 13 l))
        let I (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
        (∀ p ∈ P, ∀ l ∈ W, ¬I p l) ∧
        (∀ l, (P.filter (fun p => I p l)).card ≤ 2) ∧
        (∀ p, (W.filter (fun l => I p l)).card ≤ 2))
    (finiteTest :
      let row (w : ℕ) (s : Fin 13) (m : ℕ) (d : Bool) (i : Fin 26) :=
        w.testBit ((((if d then 13-m else m)*i.val+s.val)%13) +
          13*(if d then 1-i.val/13 else i.val/13))
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 → ¬ HasLineDegree 26 (Finset.range 13) C 1 →
        (∀ (l : Fin 13) (b : Fin 13), b ∈ ([0,1,3,9] : List (Fin 13)) →
          circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 (l+b) ∨ i = Fin.natAdd 13 l)) = true) →
        ∃ w ∈ ([7405575,23330829,5799955,22282261,21757977,21233693,19415081,5275731] : List ℕ), ∃ s : Fin 13, ∃ m ∈ ([1,3,9] : List ℕ), ∃ d : Bool,
          circuitFun 26 C (row w s m d) = true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true := by
  dsimp only at *
  intro C hm hs hl hp hyes
  let row (w : ℕ) (s : Fin 13) (m : ℕ) (d : Bool) (i : Fin 26) :=
        w.testBit ((((if d then 13-m else m)*i.val+s.val)%13) +
          13*(if d then 1-i.val/13 else i.val/13))
  have pos (l b : Fin 13) (hb : b ∈ ([0,1,3,9] : List (Fin 13))) :
      circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 (l+b) ∨ i = Fin.natAdd 13 l)) = true := by
    apply hyes
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨w, hw, s, m, hm', d, hit⟩ := finiteTest C hm hs hl hp pos
  let P := Finset.univ.filter (fun p : Fin 13 => row w s m d (Fin.castAdd 13 p))
  let W := Finset.univ.filter (fun l : Fin 13 => row w s m d (Fin.natAdd 13 l))
  obtain ⟨apart, points, lines⟩ := valid w hw s m hm' d
  refine ⟨P, W, apart, points, lines, ?_⟩
  have monotoneEval (x y : Fin 26 → Bool) (hxy : ∀ i, x i = true → y i = true) :
      circuitFun 26 C x = true → circuitFun 26 C y = true := by
    let V (w : List Bool) (i : ℕ) := w.getD i false
    let R (w z : List Bool) := w.length = z.length ∧ ∀ i, V w i = true → V z i = true
    have step (g : Gate) (hg : g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        g.op.eval (g.inputs.map (V w)) = true →
        g.op.eval (g.inputs.map (V z)) = true := by
      have hops := (hm g hg).1
      change g.op = .and ∨ g.op = .or at hops
      rcases hops with h | h <;> rw [h]
      · change (g.inputs.map (V w)).all id = true → (g.inputs.map (V z)).all id = true
        simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun all i hi => hr.2 i (all i hi)
      · change (g.inputs.map (V w)).any id = true → (g.inputs.map (V z)).any id = true
        simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,hval⟩
        exact ⟨i,hi,hr.2 i hval⟩
    let evalStep (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map (V w))]
    have run (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        R (gs.foldl evalStep w) (gs.foldl evalStep z) := by
      induction gs generalizing w z with
      | nil => exact hr
      | cons g gs ih =>
        apply ih (fun h hh => hsub h (List.mem_cons_of_mem _ hh))
        refine ⟨by simp only [evalStep,List.length_append,List.length_singleton,hr.1], ?_⟩
        intro i
        change (w ++ [_]).getD i false = true → (z ++ [_]).getD i false = true
        by_cases h : i < w.length
        · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by simpa only [← hr.1] using h)]
          exact hr.2 i
        · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by rw [← hr.1]; omega),← hr.1]
          cases i-w.length with
          | zero => exact step g (hsub g List.mem_cons_self) w z hr
          | succ k => simp
    have hi : R (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp only [List.length_ofFn], ?_⟩
      intro i
      by_cases h : i < 26
      · change (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true
        have hx : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact h
        have hy : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact h
        rw [List.getD_eq_getElem _ _ hx,List.getD_eq_getElem _ _ hy,
          List.getElem_ofFn,List.getElem_ofFn]
        exact hxy ⟨i,h⟩
      · change (List.ofFn x).getD i false = true → _
        rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        intro hf; cases hf
    exact (run C.gates (fun _ h => h) _ _ hi).2 C.output
  intro x hP hW
  apply monotoneEval (row w s m d) x _ hit
  intro i
  refine Fin.addCases (m := 13) (n := 13) (motive := fun j : Fin 26 => row w s m d j = true → x j = true) ?_ ?_ i
  · exact fun p h => hP p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · exact fun l h => hW l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
