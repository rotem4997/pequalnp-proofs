import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_4087_421
    (classify :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ P L : Finset (Fin 13),
        (∀ p ∈ P, ∀ l ∈ L, p - l ∉ D) →
        (∀ l : Fin 13, (P.filter fun p => p - l ∈ D).card ≤ 2) →
        (∀ p : Fin 13, (L.filter fun l => p - l ∈ D).card ≤ 2) →
        ∃ z : ℕ, ∃ dual : Bool, z ∈ ([7405575, 23330829, 5799955, 22282261, 21757977, 19988517, 19415081, 6619269] : List ℕ) ∧
          ∃ m ∈ ([1, 3, 9] : List (Fin 13)), ∃ t : Fin 13,
            (∀ p ∈ P, z.testBit (if dual then 13 + (-(m * p + t)).val else (m * p + t).val) = true) ∧
            (∀ l ∈ L, z.testBit (if dual then (-(m * l + t)).val else 13 + (m * l + t).val) = true))
    (synth53 :
      let M : List (Fin 13) := [1, 3, 9]
      ∃ (G : Fin 9 → Bool × Fin 13 × Fin 3) (C : Circuit), Monotone2 C ∧ C.size ≤ 18 ∧
        let enc (P L : Fin 13 → Bool) (i : Fin 53) : Bool :=
          if i.val < 13 then P (Fin.ofNat 13 i.val)
          else if i.val < 26 then L (Fin.ofNat 13 (i.val - 13))
          else
            let q := i.val - 26
            let s := G (Fin.ofNat 9 (q / 3))
            let d : Fin 13 := M.getD s.2.2.val 1
            let h (u : Fin 13) : Bool := if s.1 then P (s.2.1 + u) else L (s.2.1 - u)
            let a := h 0 || h d
            let b := h (3 * d) || h (9 * d)
            if q % 3 = 0 then a else if q % 3 = 1 then b else a || b
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          (¬∃ j : Fin 9, if (G j).1 then (G j).2.1 = l else (G j).2.1 = p) →
          circuitFun 53 C (enc (· == p) (· == l)) = true) ∧
        (∀ z ∈ ([7405575, 23330829, 5799955, 22282261, 21757977, 19988517, 19415081, 6619269] : List ℕ),
          ∀ m ∈ M, ∀ (t : Fin 13) (dual : Bool),
            circuitFun 53 C (enc
              (fun i => z.testBit (if dual then 13 + (-(m * i + t)).val else (m * i + t).val))
              (fun i => z.testBit (if dual then (-(m * i + t)).val else 13 + (m * i + t).val))) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool → Prop := fun (x2 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : List Bool) =>   x5.length = (70 : ℕ) ∧     (∀ (x6 : Fin (13 : ℕ)), x5.getD (↑x6) Bool.false = Decidable.decide (x6 ∈ x3) ∧ x5.getD ((13 : ℕ) + ↑x6) Bool.false = Decidable.decide (x6 ∈ x4)) ∧       ∀ (x6 : Fin (9 : ℕ)),         have x7 : Fin (13 : ℕ) := (x2 x6).2.1;         have x8 : Fin (13 : ℕ) := if (x2 x6).2.2 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if (x2 x6).2.2 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ));         let x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => if (x2 x6).1 = Bool.true then x7 + x9 ∈ x3 else x7 - x9 ∈ x4;         have x10 : ℕ := (26 : ℕ) + ((5 : ℕ) * ↑x6 - (1 : ℕ));         x5.getD x10 Bool.false = Decidable.decide (x9 (0 : Fin (13 : ℕ)) ∨ x9 x8) ∧ x5.getD (x10 + (1 : ℕ)) Bool.false = Decidable.decide (x9 ((3 : Fin (13 : ℕ)) * x8) ∨ x9 ((9 : Fin (13 : ℕ)) * x8)) ∧ x5.getD (x10 + (2 : ℕ)) Bool.false = (x5.getD x10 Bool.false || x5.getD (x10 + (1 : ℕ)) Bool.false); ∃ (x3 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (18 : ℕ) ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))) (x7 : List Bool), x2 x3 x5 x6 x7 → ((∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x5 = {x9} ∧ x6 = {x10} ∧ x9 - x10 ∈ x1 ∧ ¬∃ (x11 : Fin (9 : ℕ)), if (x3 x11).1 = Bool.true then (x3 x11).2.1 = x10 else (x3 x11).2.1 = x9) → x4.eval x7 = Bool.true) ∧ ((∀ x9 ∈ x5, ∀ x11 ∈ x6, x9 - x11 ∉ x1) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x5 | x11 - x10 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x6 | x11 - x12 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval x7 = Bool.false) := by
  dsimp only
  have hd3 : ∀ x : Fin 3, ([1, 3, 9] : List (Fin 13)).getD x.val 1 = if x = 0 then 1 else if x = 1 then 3 else 9 := by
    decide
  have hgeo : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → p ∈ singerLines3 l := by
    decide
  let enc (G : Fin 9 → Bool × Fin 13 × Fin 3) (P L : Fin 13 → Bool) (i : Fin 53) : Bool :=
    if i.val < 13 then P (Fin.ofNat 13 i.val)
    else if i.val < 26 then L (Fin.ofNat 13 (i.val - 13))
    else
      let q := i.val - 26
      let s := G (Fin.ofNat 9 (q / 3))
      let d : Fin 13 := ([1, 3, 9] : List (Fin 13)).getD s.2.2.val 1
      let h (u : Fin 13) : Bool := if s.1 then P (s.2.1 + u) else L (s.2.1 - u)
      let a := h 0 || h d
      let b := h (3 * d) || h (9 * d)
      if q % 3 = 0 then a else if q % 3 = 1 then b else a || b
  rcases synth53 with ⟨G, C, hMonoC, hSizeC, hPosC, hNegC⟩
  let mapWire (idx : ℕ) : ℕ :=
    if idx < 26 then idx
    else if idx < 53 then 26 + (5 * ((idx - 26) / 3) - 1) + (idx - 26) % 3
    else idx + 17
  let liftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map mapWire⟩
  let D : Circuit := ⟨C.gates.map liftGate, mapWire C.output⟩
  have hMonoD : Monotone2 D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen⟩ := hMonoC g0 hg0
    exact ⟨hop, by simpa [liftGate] using hlen⟩
  have hSizeD : D.size ≤ 18 := by
    change (C.gates.map liftGate).length ≤ 18
    rw [List.length_map]
    exact hSizeC
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hLiftWires : ∀ (gs : List Gate) (u w : List Bool),
      u.length ≥ 53 → w.length = u.length + 17 →
      (∀ idx, w.getD (mapWire idx) false = u.getD idx false) →
      ∀ idx, ((gs.map liftGate).foldl step w).getD (mapWire idx) false =
        (gs.foldl step u).getD idx false := by
    intro gs
    induction gs with
    | nil =>
      intro u w _ _ hinv idx
      exact hinv idx
    | cons g gs ih =>
      intro u w hu hw hinv idx
      apply ih (step u g) (step w (liftGate g))
        (by simp [step]; omega)
        (by simp [step]; omega)
      intro k
      have hgeval : (liftGate g).op.eval ((liftGate g).inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => u.getD i false) := by
        simp only [liftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hinv a
      have hmap_lt : ∀ a, a < u.length → mapWire a < w.length := by
        intro a ha
        simp only [mapWire]
        by_cases h1 : a < 26
        · simp only [h1, ↓reduceIte]; omega
        · by_cases h2 : a < 53
          · simp only [h1, h2, ↓reduceIte]; omega
          · simp only [h1, h2, ↓reduceIte]; omega
      have hmap_eq : mapWire u.length = w.length := by
        simp only [mapWire, show ¬u.length < 26 by omega, show ¬u.length < 53 by omega, ↓reduceIte]
        omega
      have hmap_gt : ∀ a, u.length < a → w.length < mapWire a := by
        intro a ha
        simp only [mapWire, show ¬a < 26 by omega, show ¬a < 53 by omega, ↓reduceIte]
        omega
      by_cases hk1 : k < u.length
      · have hmk : mapWire k < w.length := hmap_lt k hk1
        simp only [step, List.getD_append _ _ _ _ hk1, List.getD_append _ _ _ _ hmk]
        exact hinv k
      · by_cases hk2 : k = u.length
        · subst hk2
          simp only [step, hmap_eq]
          rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero]
          exact hgeval
        · have hk3 : u.length < k := by omega
          have hmk : w.length < mapWire k := hmap_gt k hk3
          simp only [step]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          have h1 : ([(liftGate g).op.eval ((liftGate g).inputs.map fun i => w.getD i false)]).length ≤
              mapWire k - w.length := by simp only [List.length_singleton]; omega
          have h2 : ([g.op.eval (g.inputs.map fun i => u.getD i false)]).length ≤
              k - u.length := by simp only [List.length_singleton]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
              List.getD_eq_getElem?_getD, List.getElem?_eq_none h2]
  have hMonoEval : ∀ (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (gs.foldl step u).getD i false = true → (gs.foldl step v).getD i false = true := by
    intro gs
    induction gs with
    | nil =>
      intro _ u v _ hsub i hi
      exact hsub i hi
    | cons g gs ih =>
      intro ops u v hlen hsub i hi
      apply ih (fun a ha => ops a (List.mem_cons_of_mem _ ha)) (step u g) (step v g)
        (by simp [step, hlen]) _ i hi
      intro k hk
      by_cases hkl : k < u.length
      · rw [List.getD_append _ _ _ _ hkl] at hk
        rw [List.getD_append _ _ _ _ (hkl.trans_eq hlen)]
        exact hsub k hk
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hk ⊢
        rw [← hlen]
        by_cases h0 : k - u.length = 0
        · rw [h0] at hk ⊢
          simp only [List.getD_cons_zero] at hk ⊢
          rcases ops g List.mem_cons_self with hop | hop <;> rw [hop] at hk ⊢
          · change (g.inputs.map fun j => u.getD j false).all id = true at hk
            change (g.inputs.map fun j => v.getD j false).all id = true
            simp only [List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
              forall_apply_eq_imp_iff₂] at hk ⊢
            exact fun j hj => hsub j (hk j hj)
          · change (g.inputs.map fun j => u.getD j false).any id = true at hk
            change (g.inputs.map fun j => v.getD j false).any id = true
            rw [List.any_eq_true] at hk ⊢
            obtain ⟨b, hb, hbeq⟩ := hk
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
            exact ⟨true, List.mem_map.mpr ⟨j, hj, hsub j (by simpa only [id_eq] using hbeq)⟩, rfl⟩
        · have hge : ([g.op.eval (g.inputs.map fun j => u.getD j false)]).length ≤
              k - u.length := by simp only [List.length_singleton]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hk
          exact Bool.noConfusion hk
  have hEncMono : ∀ (P1 L1 P2 L2 : Fin 13 → Bool),
      (∀ p, P1 p = true → P2 p = true) → (∀ l, L1 l = true → L2 l = true) →
      ∀ i : Fin 53, enc G P1 L1 i = true → enc G P2 L2 i = true := by
    intro P1 L1 P2 L2 hP hL i hi
    simp only [enc] at hi ⊢
    by_cases h1 : i.val < 13
    · simp only [h1, ↓reduceIte] at hi ⊢
      exact hP _ hi
    · by_cases h2 : i.val < 26
      · simp only [h1, h2, ↓reduceIte] at hi ⊢
        exact hL _ hi
      · simp only [h1, h2, ↓reduceIte] at hi ⊢
        let j : Fin 9 := Fin.ofNat 9 ((i.val - 26) / 3)
        have hh : ∀ u, (if (G j).1 = true then P1 ((G j).2.1 + u) else L1 ((G j).2.1 - u)) = true →
            (if (G j).1 = true then P2 ((G j).2.1 + u) else L2 ((G j).2.1 - u)) = true := by
          intro u hu
          by_cases hside : (G j).1 = true
          · simp only [hside, ↓reduceIte] at hu ⊢
            exact hP _ hu
          · simp only [hside, Bool.false_eq_true, ↓reduceIte] at hu ⊢
            exact hL _ hu
        by_cases hr0 : (i.val - 26) % 3 = 0
        · simp only [hr0, ↓reduceIte] at hi ⊢
          rcases Bool.or_eq_true_iff.mp hi with ha | hb
          · exact Bool.or_eq_true_iff.mpr (Or.inl (hh _ ha))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (hh _ hb))
        · by_cases hr1 : (i.val - 26) % 3 = 1
          · simp only [hr1, ↓reduceIte] at hi ⊢
            rcases Bool.or_eq_true_iff.mp hi with ha | hb
            · exact Bool.or_eq_true_iff.mpr (Or.inl (hh _ ha))
            · exact Bool.or_eq_true_iff.mpr (Or.inr (hh _ hb))
          · simp only [hr0, hr1, ↓reduceIte] at hi ⊢
            rcases Bool.or_eq_true_iff.mp hi with hab | hcd
            · rcases Bool.or_eq_true_iff.mp hab with ha | hb
              · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl (hh _ ha))))
              · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr (hh _ hb))))
            · rcases Bool.or_eq_true_iff.mp hcd with hc | hd
              · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.or_eq_true_iff.mpr (Or.inl (hh _ hc))))
              · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.or_eq_true_iff.mpr (Or.inr (hh _ hd))))
  refine ⟨G, D, hMonoD, hSizeD, ?_⟩
  intro P L w hw
  have hwlen := hw.1
  have hraw := hw.2.1
  have hsem := hw.2.2
  let u := List.ofFn (enc G (fun x => decide (x ∈ P)) (fun x => decide (x ∈ L)))
  have hBaseInv : ∀ idx, w.getD (mapWire idx) false = u.getD idx false := by
    intro idx
    by_cases hlt : idx < 53
    · have huget : u.getD idx false =
          enc G (fun x => decide (x ∈ P)) (fun x => decide (x ∈ L)) ⟨idx, hlt⟩ := by
        rw [List.getD_eq_getElem?_getD]
        simp only [u, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
      rw [huget]
      by_cases h1 : idx < 13
      · have hmw : mapWire idx = idx := by simp [mapWire, show idx < 26 by omega]
        rw [hmw]
        simp only [enc, h1, ↓reduceIte]
        have hfin : Fin.ofNat 13 idx = ⟨idx, h1⟩ := by
          ext; simp [Fin.ofNat, Nat.mod_eq_of_lt h1]
        rw [hfin]
        exact (hraw ⟨idx, h1⟩).1
      · by_cases h2 : idx < 26
        · have hmw : mapWire idx = idx := by simp [mapWire, h2]
          rw [hmw]
          simp only [enc, h1, h2, ↓reduceIte]
          have hlt13 : idx - 13 < 13 := by omega
          have hfin : Fin.ofNat 13 (idx - 13) = ⟨idx - 13, hlt13⟩ := by
            ext; simp [Fin.ofNat, Nat.mod_eq_of_lt hlt13]
          rw [hfin]
          have heq : 13 + (idx - 13) = idx := by omega
          have hr := (hraw ⟨idx - 13, hlt13⟩).2
          simpa only [heq] using hr
        · have hmw : mapWire idx = 26 + (5 * ((idx - 26) / 3) - 1) + (idx - 26) % 3 := by
            simp [mapWire, h2, hlt]
          rw [hmw]
          simp only [enc, h1, h2, ↓reduceIte]
          have hklt : (idx - 26) / 3 < 9 := by omega
          let k : Fin 9 := ⟨(idx - 26) / 3, hklt⟩
          have hkf : Fin.ofNat 9 ((idx - 26) / 3) = k := by
            ext; simp [k, Fin.ofNat, Nat.mod_eq_of_lt hklt]
          rw [hkf]
          obtain ⟨hs0, hs1, hs2⟩ := hsem k
          dsimp only [k] at hs0 hs1 hs2
          have hbit : ∀ u : Fin 13,
              (if (G k).1 = true then decide ((G k).2.1 + u ∈ P) else decide ((G k).2.1 - u ∈ L)) =
              decide (if (G k).1 = true then (G k).2.1 + u ∈ P else (G k).2.1 - u ∈ L) := by
            intro u
            by_cases hs : (G k).1 = true
            · simp only [hs, ↓reduceIte]
            · simp only [hs, Bool.false_eq_true, ↓reduceIte]
          have hrlt : (idx - 26) % 3 < 3 := Nat.mod_lt _ (by omega)
          have hr012 : (idx - 26) % 3 = 0 ∨ (idx - 26) % 3 = 1 ∨ (idx - 26) % 3 = 2 := by omega
          rcases hr012 with hr | hr | hr <;> simp only [hr]
          · simp only [Nat.add_zero, ↓reduceIte, hs0, hbit, hd3, Bool.decide_or]
            rfl
          · simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, hs1, hbit, hd3, Bool.decide_or]
            rfl
          · simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
              hs2, hs0, hs1, hbit, hd3, Bool.decide_or]
            rfl
    · have hge : 53 ≤ idx := by omega
      have hmw : mapWire idx = idx + 17 := by simp [mapWire, show ¬idx < 26 by omega, hlt]
      rw [hmw]
      have h1 : w.length ≤ idx + 17 := by omega
      have h2 : u.length ≤ idx := by simp only [u, List.length_ofFn]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
          List.getD_eq_getElem?_getD, List.getElem?_eq_none h2]
  have hEvalEq : D.eval w = circuitFun 53 C (enc G (fun x => decide (x ∈ P)) (fun x => decide (x ∈ L))) := by
    change (D.wires w).getD (mapWire C.output) false = (C.wires u).getD C.output false
    exact hLiftWires C.gates u w (by simp only [u, List.length_ofFn]; omega)
      (by simp only [u, List.length_ofFn, hwlen]) hBaseInv C.output
  rw [hEvalEq]
  constructor
  · intro hpos
    rcases hpos with ⟨p, l, hp, hl, hinc, hfree⟩
    subst hp
    subst hl
    have hfun : enc G (fun x => decide (x ∈ ({p} : Finset (Fin 13))))
        (fun x => decide (x ∈ ({l} : Finset (Fin 13)))) =
        enc G (· == p) (· == l) := by
      have hp1 : (fun x : Fin 13 => decide (x ∈ ({p} : Finset (Fin 13)))) = (· == p) := by
        funext x; simp only [Finset.mem_singleton]; exact (Bool.eq_iff_iff.mpr (by simp)).symm
      have hl1 : (fun x : Fin 13 => decide (x ∈ ({l} : Finset (Fin 13)))) = (· == l) := by
        funext x; simp only [Finset.mem_singleton]; exact (Bool.eq_iff_iff.mpr (by simp)).symm
      rw [hp1, hl1]
    rw [hfun]
    exact hPosC p l (hgeo p l hinc) hfree
  · intro hDisj hArcP hArcL
    obtain ⟨z, dual, hz, m, hm, t, hDomP, hDomL⟩ := classify P L hDisj hArcP hArcL
    let P2 : Fin 13 → Bool := fun i =>
      z.testBit (if dual then 13 + (-(m * i + t)).val else (m * i + t).val)
    let L2 : Fin 13 → Bool := fun i =>
      z.testBit (if dual then (-(m * i + t)).val else 13 + (m * i + t).val)
    have hFalse : circuitFun 53 C (enc G P2 L2) = false := hNegC z hz m hm t dual
    apply Bool.eq_false_iff.mpr
    intro hTrue
    have hSub : ∀ idx, u.getD idx false = true →
        (List.ofFn (enc G P2 L2)).getD idx false = true := by
      intro idx hidx
      by_cases hlt : idx < 53
      · simp only [u, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
          Option.getD_some] at hidx ⊢
        exact hEncMono _ _ P2 L2
          (fun p hp => hDomP p (decide_eq_true_eq.mp hp))
          (fun l hl => hDomL l (decide_eq_true_eq.mp hl))
          ⟨idx, hlt⟩ hidx
      · simp only [u, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
          Option.getD_none] at hidx
        exact Bool.noConfusion hidx
    have hOps : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg =>
      (hMonoC g hg).1
    have hvTrue : circuitFun 53 C (enc G P2 L2) = true :=
      hMonoEval C.gates hOps u (List.ofFn (enc G P2 L2))
        (by simp only [u, List.length_ofFn]) hSub C.output hTrue
    exact Bool.noConfusion (hvTrue.symm.trans hFalse)
