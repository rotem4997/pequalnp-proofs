import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_7893_318
    (finiteCofactors : ∀ (l h q : (Fin 9 → Bool) → Bool),
      Monotone l → Monotone h → Monotone q → (∀ x, l x ≤ h x) →
    let R : ℕ → Fin 9 → Bool := fun n i => n.testBit (i.val + 1)
    let P : (Fin 9 → Bool) → Bool := fun x =>
      ([(0,1), (1,2), (2,3), (0,5), (1,6), (4,6), (2,7), (4,7), (5,7), (3,8), (5,8), (6,8)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
    let S := fun (n : ℕ) => bif n.testBit 0 || q (R n) then h (R n) else l (R n)
    (∀ n ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), q (R n) = false) →
    (∀ n ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), S n = true) →
    (∀ n ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), S n = false) →
    ∀ x, h x = (x 0 || x 3 || x 4 || P x) ∧
      (l x = true → P x = true) ∧
      (l x || q x) = ((P x || (q (R 200) && (x 2 && x 5 && x 6))) ||
        (q (R 772) && (x 1 && x 7 && x 8))))
    (simultaneousBound : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
      PEqualNP.TopForm.IsAO2 10 C → 16 ≤ C.size ∧ C.size ≤ 18 →
      (w ≠ 0 ∧ w < 10 + C.size ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        10 + j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
    let f := fun (b : Bool) (x : Fin 9 → Bool) => PEqualNP.MetaComplexity.circuitFun 10 C (Fin.cases b x)
    let q := fun x : Fin 9 → Bool => (C.wires (List.ofFn (Fin.cases false x))).getD w false
    let R : ℕ → Fin 9 → Bool := fun n i => n.testBit (i.val + 1)
    let P : (Fin 9 → Bool) → Bool := fun x =>
      ([(0,1), (1,2), (2,3), (0,5), (1,6), (4,6), (2,7), (4,7), (5,7), (3,8), (5,8), (6,8)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
    (∀ x, f true x = (x 0 || x 3 || x 4 || P x) ∧
      (f false x = true → P x = true) ∧
      (f false x || q x) = ((P x || (q (R 200) && (x 2 && x 5 && x 6))) ||
        (q (R 772) && (x 1 && x 7 && x 8)))) → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 →     (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) →       (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) →         have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7;         have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false;         have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) || x7 x8));         (∀ x9 ∈ [(50 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ)], x7 x9 = Bool.false) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false)) := by
  have cofactorOrder : ∀ (C : Circuit) (w : ℕ),
      PEqualNP.TopForm.IsAO2 10 C →
      let l := fun x : Fin 9 → Bool => circuitFun 10 C (Fin.cases false x)
      let h := fun x : Fin 9 → Bool => circuitFun 10 C (Fin.cases true x)
      let q := fun x : Fin 9 → Bool =>
        (C.wires (List.ofFn (Fin.cases false x))).getD w false
      Monotone l ∧ Monotone h ∧ Monotone q ∧ ∀ x, l x ≤ h x := by
    intro C w hAO
    let step : List Bool → Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    let LeL (a b : List Bool) : Prop :=
      ∀ i, a.getD i false = true → b.getD i false = true
    have gate_mono (op : GateOp) (hop : op = .and ∨ op = .or) (args : List ℕ)
        (f f' : ℕ → Bool) (hh : ∀ i, f i = true → f' i = true) :
        op.eval (args.map f) = true → op.eval (args.map f') = true := by
      rcases hop with rfl | rfl
      · change (args.map f).all id = true → (args.map f').all id = true
        simp only [List.all_eq_true, List.mem_map, id]
        intro H x hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact hh i (H (f i) ⟨i, hi, rfl⟩)
      · change (args.map f).any id = true → (args.map f').any id = true
        simp only [List.any_eq_true, List.mem_map, id]
        rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
        exact ⟨f' i, ⟨i, hi, rfl⟩, hh i hx⟩
    have fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
        ∀ a b : List Bool, a.length = b.length → LeL a b →
          LeL (gs.foldl step a) (gs.foldl step b) := by
      induction gs with
      | nil => intro a b _ hh; exact hh
      | cons g gs ih =>
        intro a b hl hh
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
        · simp [step, hl]
        · intro i hi
          unfold step at hi ⊢
          by_cases hia : i < a.length
          · rw [List.getD_append _ _ _ _ hia] at hi
            rw [List.getD_append _ _ _ _ (by omega)]
            exact hh i hi
          · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
            rw [List.getD_append_right _ _ _ _ (by omega)]
            rw [← hl]
            by_cases he : i - a.length = 0
            · rw [he] at hi ⊢
              simp only [List.getD_cons_zero] at hi ⊢
              exact gate_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => hh k) hi
            · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 :=
                ⟨i - a.length - 1, by omega⟩
              rw [hm] at hi
              simp at hi
    have wireMono (v : ℕ) : Monotone (fun x : Fin 10 → Bool =>
        (C.wires (List.ofFn x)).getD v false) := by
      intro x y hxy
      apply Bool.le_iff_imp.mpr
      apply fold_mono C.gates hAO.1 _ _ (by simp) _ v
      intro i hi
      by_cases hlt : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi ⊢
        simp only [List.getElem_ofFn] at hi ⊢
        exact Bool.le_iff_imp.mp (hxy ⟨i, hlt⟩) hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction
    have outputMono : Monotone (circuitFun 10 C) := wireMono C.output
    have embedMono (b : Bool) : Monotone (fun x : Fin 9 → Bool => (Fin.cases b x : Fin 10 → Bool)) := by
      intro x y hxy i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_rfl
      · exact hxy j
    dsimp only
    refine ⟨outputMono.comp (embedMono false), outputMono.comp (embedMono true),
      (wireMono w).comp (embedMono false), ?_⟩
    intro x
    apply outputMono
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change false ≤ true
      decide
    · exact le_rfl
  intro C w hAO hs hw row0 w0 f0 ht hspec
  let l := fun x : Fin 9 → Bool => PEqualNP.MetaComplexity.circuitFun 10 C (Fin.cases false x)
  let h := fun x : Fin 9 → Bool => PEqualNP.MetaComplexity.circuitFun 10 C (Fin.cases true x)
  let q := fun x : Fin 9 → Bool => (C.wires (List.ofFn (Fin.cases false x))).getD w false
  let R := fun (n : ℕ) (i : Fin 9) => n.testBit (i.val + 1)
  have row (n : ℕ) (b : Bool) :
      Function.update (fun i : Fin 10 => n.testBit i.val) 0 b = Fin.cases b (R n) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [R, Fin.val_succ]
  have tap (n : ℕ) :
      (C.wires (List.ofFn (Function.update (fun i : Fin 10 => n.testBit i.val) 0 false))).getD w false = q (R n) := by
    rw [row]
  have sub (n : ℕ) :
      PEqualNP.MetaComplexity.circuitFun 10 C
        (Function.update (fun i : Fin 10 => n.testBit i.val) 0
          (n.testBit 0 || (C.wires (List.ofFn (Function.update (fun i : Fin 10 => n.testBit i.val) 0 false))).getD w false)) =
        (bif n.testBit 0 || q (R n) then h (R n) else l (R n)) := by
    rw [tap, row]
    cases hb : n.testBit 0 || q (R n) <;> rfl
  obtain ⟨hl, hh, hq, hlh⟩ := cofactorOrder C w hAO
  apply simultaneousBound C w hAO hs hw
  apply finiteCofactors l h q hl hh hq hlh
  · intro n hn
    exact (tap n).symm.trans (ht n hn)
  · intro n hn
    exact (sub n).symm.trans (hspec.1 n hn)
  · intro n hn
    exact (sub n).symm.trans (hspec.2 n hn)
