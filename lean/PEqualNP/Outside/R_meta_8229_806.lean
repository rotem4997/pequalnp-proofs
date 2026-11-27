import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_8229_806 :
    (
      ∃ (A : List (Bool × Fin 32 × Fin 32)) (T : List (Fin 32 × Fin 32)),
      let V := A.foldl (fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]) [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
       26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
      let term := fun p : Fin 32 × Fin 32 => V.getD p.1 0 &&& V.getD p.2 0
      A.length + 2 * T.length ≤ 22 ∧ T ≠ [] ∧
      (∀ j : Fin A.length, (A.get j).2.1.val < 11 + j.val ∧
        (A.get j).2.2.val < 11 + j.val) ∧
      (A.filter (·.1)).length = 2 ∧
      (∀ j : Fin A.length, (A.get j).1 = true →
        V.getD (11 + j.val) 0 &&& 1099511562240 ≠ 0) ∧
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length ∧
        term p &&& 1099511562240 = 0) ∧
      T.foldl (fun b p => b ||| term p) 0 = 65535) →
    (∀ (z : List ℕ) (A : List (Bool × Fin 32 × Fin 32)) (T : List (Fin 32 × Fin 32)),
      let step := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]
      let V := A.foldl step z
      z.length = 11 → A.length + 2 * T.length ≤ 22 → T ≠ [] →
      (∀ j : Fin A.length, (A.get j).2.1.val < 11 + j.val ∧
        (A.get j).2.2.val < 11 + j.val) →
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length) →
      ∃ (R : List (Bool × Fin 32 × Fin 32)) (B : Fin 21 → Bool × Fin 32 × Fin 32),
      List.ofFn B = A ++ T.map (fun p => (true, p)) ++ R ∧ (∀ g ∈ R, g.1 = false) ∧
      (∀ j : Fin 21, (B j).2.1.val < 11 + j.val ∧ (B j).2.2.val < 11 + j.val) ∧
      ((List.ofFn B).foldl step z).getD 31 0 =
        T.foldl (fun b p => b ||| (V.getD p.1 0 &&& V.getD p.2 0)) 0) →
    (∀ (z : List ℕ) (m : ℕ) (A R : List (Bool × Fin 32 × Fin 32))
        (T : List (Fin 32 × Fin 32)) (B : Fin 21 → Bool × Fin 32 × Fin 32),
      let step := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]
      let V := A.foldl step z
      let W := (List.ofFn B).foldl step z
      z.length = 11 → List.ofFn B = A ++ T.map (fun p => (true, p)) ++ R → (∀ g ∈ R, g.1 = false) →
      (∀ j : Fin A.length, (A.get j).1 = true → V.getD (11 + j.val) 0 &&& m ≠ 0) →
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length ∧
        (V.getD p.1 0 &&& V.getD p.2 0) &&& m = 0) →
      (List.ofFn (fun j : Fin 21 => decide ((B j).1 = true ∧
        W.getD (11 + j.val) 0 &&& m ≠ 0))).count true = (A.filter (·.1)).length ∧
      ∀ i : Fin 21, (B i).1 = true → W.getD (11 + i.val) 0 &&& m = 0 →
        A.length ≤ i.val) →
    (∀ (A R : List (Bool × Fin 32 × Fin 32)) (T : List (Fin 32 × Fin 32))
        (B : Fin 21 → Bool × Fin 32 × Fin 32),
      List.ofFn B = A ++ T.map (fun p => (true, p)) ++ R → (∀ g ∈ R, g.1 = false) →
      (∀ j : Fin 21, (B j).2.1.val < 11 + j.val ∧ (B j).2.2.val < 11 + j.val) →
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length) →
      let C : Circuit := ⟨(List.ofFn B).map (fun g =>
        ⟨if g.1 = true then .and else .or, [g.2.1.val, g.2.2.val]⟩), 31⟩
      ∀ i j : Fin 21, A.length ≤ i.val → (B j).1 = true → ¬ InCone 11 C i.val j.val) →
    ∃ (x1 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)),   (∀ (x2 : Fin (21 : ℕ)), ↑(x1 x2).2.1 < (11 : ℕ) + ↑x2 ∧ ↑(x1 x2).2.2 < (11 : ℕ) + ↑x2) ∧     have x2 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x2 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => { op := if x2.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x2.2.1, ↑x2.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (List.ofFn x1), output := (31 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };     have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] (List.ofFn x1);     x3.getD (31 : ℕ) (0 : ℕ) = (65535 : ℕ) ∧ List.count Bool.true (List.ofFn fun (x4 : Fin (21 : ℕ)) => Decidable.decide ((x1 x4).1 = Bool.true ∧ x3.getD ((11 : ℕ) + ↑x4) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ))) = (2 : ℕ) ∧ ∀ (x4 x5 : Fin (21 : ℕ)), (x1 x4).1 = Bool.true → x3.getD ((11 : ℕ) + ↑x4) (0 : ℕ) &&& (1099511562240 : ℕ) = (0 : ℕ) → (x1 x5).1 = Bool.true → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 ↑x4 ↑x5 := by
  intro core assemble flags cones
  obtain ⟨A, T, budget, hasTop, read, count, dirty, clean, output⟩ := core
  have topRead (p : Fin 32 × Fin 32) (hp : p ∈ T) :=
    And.intro (clean p hp).1 (clean p hp).2.1
  obtain ⟨R, B, layout, onlyOr, back, value⟩ :=
    assemble [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
       26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] A T rfl budget hasTop read topRead
  obtain ⟨countB, partition⟩ :=
    flags [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
       26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] 1099511562240 A R T B rfl layout onlyOr dirty clean
  refine ⟨B, back, value.trans output, countB.trans count, ?_⟩
  intro i j andI cleanI andJ
  exact cones A R T B layout onlyOr back topRead i j (partition i andI cleanI) andJ
