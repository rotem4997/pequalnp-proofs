import PEqualNP.Defs

set_option maxHeartbeats 15000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_2708_701
    (cover : ∀ x : Fin 14 → Bool, (¬ ∃ u v : Fin 14, 14 * u.val + v.val ∈ ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) ∧ x u = true ∧ x v = true) → ∃ m ∈ ([127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ), ∀ i : Fin 14, x i = true → m.testBit i.val = true)
    (monotone_wires : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → ∀ (x y : Fin 14 → Bool), (∀ i, x i = true → y i = true) → ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true)
    (normalize : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 25 → ∃ (t : Fin 26) (ops : Fin t → Bool) (src : Fin t → Option (Fin 40) × Option (Fin 40)), let D := ({gates := List.ofFn (fun i : Fin t => {op := if ops i then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val}), output := 0} : PEqualNP.CircuitLowerBounds.Circuit); ∀ x : Fin 14 → Bool, D.wires (List.ofFn x) = C.wires (List.ofFn x))
    (finite_exclusion : ∀ (t : Fin 26) (ops : Fin t → Bool) (src : Fin t → Option (Fin 40) × Option (Fin 40)) (a b : Fin 39), let D := ({gates := List.ofFn (fun i : Fin t => {op := if ops i then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val}), output := 0} : PEqualNP.CircuitLowerBounds.Circuit); let N := ([127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ); let w (m : ℕ) (j : Fin 39) := (D.wires (List.ofFn (fun (i : Fin 14) => m.testBit i.val))).getD j.val false; (∀ m ∈ ([129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112] : List ℕ), w m a = true ∧ w m b = true) → (∀ m ∈ N, w m a = false ∨ w m b = false) → (∃ m ∈ N, w m a = false ∧ w m b = true) → (∃ m ∈ N, w m b = false ∧ w m a = true) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  intro C a b hC ha hb
  dsimp only
  intro on off leftOnly rightOnly
  by_contra short
  have size : C.size ≤ 25 := by omega
  obtain ⟨t, ops, src, same⟩ := normalize C hC size
  let D := ({gates := List.ofFn (fun i : Fin t => {op := if ops i then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val}), output := 0} : PEqualNP.CircuitLowerBounds.Circuit)
  let ua : Fin 39 := ⟨a, by omega⟩
  let ub : Fin 39 := ⟨b, by omega⟩
  let U (x : Fin 14 → Bool) := (C.wires (List.ofFn x)).getD a false
  let V (x : Fin 14 → Bool) := (C.wires (List.ofFn x)).getD b false
  let H (x : Fin 14 → Bool) := ∃ u v : Fin 14, (u.val,v.val) ∈ ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true
  let row (m : ℕ) : Fin 14 → Bool := fun (i : Fin 14) => m.testBit i.val
  let N := ([127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ)
  have positive : ∀ m ∈ ([129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112] : List ℕ), H (row m) := by decide +kernel
  have negative : ∀ m ∈ N, ¬ H (row m) := by decide +kernel
  have edgeCode : ∀ u v : Fin 14, 14 * u.val + v.val ∈ ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) ↔ (u.val,v.val) ∈ ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) := by
    decide +kernel
  have extend (x : Fin 14 → Bool) (hx : ¬ H x) :
      ∃ m ∈ N, ∀ i, x i = true → row m i = true := by
    apply cover x
    rintro ⟨u,v,he,hu,hv⟩
    exact hx ⟨u,v,(edgeCode u v).mp he,hu,hv⟩
  have leftMax : ∃ m ∈ N, U (row m) = false ∧ V (row m) = true := by
    obtain ⟨x,hx,_,hv⟩ := leftOnly
    obtain ⟨m,hm,inc⟩ := extend x hx
    have fires : V (row m) = true := monotone_wires C hC x (row m) inc b hv
    have space : U (row m) = false ∨ V (row m) = false := off (row m) (negative m hm)
    exact ⟨m,hm,space.resolve_right (by rw [fires]; decide),fires⟩
  have rightMax : ∃ m ∈ N, V (row m) = false ∧ U (row m) = true := by
    obtain ⟨x,hx,_,hu⟩ := rightOnly
    obtain ⟨m,hm,inc⟩ := extend x hx
    have fires : U (row m) = true := monotone_wires C hC x (row m) inc a hu
    have space : U (row m) = false ∨ V (row m) = false := off (row m) (negative m hm)
    exact ⟨m,hm,space.resolve_left (by rw [fires]; decide),fires⟩
  have sameRow (m : ℕ) : D.wires (List.ofFn (row m)) = C.wires (List.ofFn (row m)) := same (row m)
  let W (m : ℕ) (j : Fin 39) := (D.wires (List.ofFn (row m))).getD j.val false
  have ea (m : ℕ) : W m ua = U (row m) := by
    change (D.wires (List.ofFn (row m))).getD a false = _
    rw [sameRow]
  have eb (m : ℕ) : W m ub = V (row m) := by
    change (D.wires (List.ofFn (row m))).getD b false = _
    rw [sameRow]
  apply finite_exclusion t ops src ua ub
  · intro m hm
    change W m ua = true ∧ W m ub = true
    rw [ea,eb]
    exact on (row m) (positive m hm)
  · intro m hm
    change W m ua = false ∨ W m ub = false
    rw [ea,eb]
    exact off (row m) (negative m hm)
  · obtain ⟨m,hm,h1,h2⟩ := leftMax
    exact ⟨m,hm,(ea m).trans h1,(eb m).trans h2⟩
  · obtain ⟨m,hm,h1,h2⟩ := rightMax
    exact ⟨m,hm,(eb m).trans h1,(ea m).trans h2⟩
