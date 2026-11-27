import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- Twenty positive flags, 37 maximal independent sets, and the missing flag
-- 129. Split the pinned normal-form CNF by the AND literal of its last slot.
set_option maxHeartbeats 2400000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_2276_521
    (complete : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (lastAnd : let p : List ℕ := [130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208]
      let d : List ℕ := [127,129,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
      ¬ FormulaSat ([755460] :: enc 14 24 (fun r => p.contains r) (p ++ d)))
    (other : let p : List ℕ := [130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208]
      let d : List ℕ := [127,129,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
      ¬ FormulaSat ([755461] :: [755465] :: enc 14 24 (fun r => p.contains r) (p ++ d)))
    (pad : let p : List ℕ := [130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208]
      let d : List ℕ := [127,129,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
      ¬ FormulaSat ([755464] :: enc 14 24 (fun r => p.contains r) (p ++ d))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → x6 (0 : Fin (14 : ℕ)) = Bool.false ∨ x6 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x6) = Bool.true ↔ x2 x6)) → x4.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = (0 : Fin (14 : ℕ)) ∨ x7 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x4.size := by
  dsimp only
  intro C mono check missing
  by_contra! tooSmall
  let p : List ℕ := [130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208]
  let d : List ℕ := [127,129,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
  let ordinary : List ℕ := [127,130,136,244,257,260,314,320,432,514,541,544,576,660,792,1025,1040,1056,1102,1220,1290,1548,2056,2064,2087,2112,2212,2338,2565,3078,3716,4100,4104,4128,4179,4304,4370,4625,5008,5186,6147,7426,8194,8196,8208,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
  let edges : List (Fin 14 × Fin 14) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let hit := fun x : Fin 14 → Bool => edges.any (fun e => x e.1 && x e.2)
  let row := fun (r : ℕ) (i : Fin 14) => r.testBit i.val
  have spec (x : Fin 14 → Bool) : (∃ a b : Fin 14,
      (a.val,b.val) ∈ ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧ x a = true ∧ x b = true) ↔ hit x = true := by
    change (∃ a b : Fin 14, (a.val,b.val) ∈ edges.map (fun e => (e.1.val,e.2.val)) ∧ _ ∧ _) ↔ _
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      obtain ⟨⟨u,v⟩,huv,eq⟩ := List.mem_map.mp hab
      have au : u = a := Fin.ext (congrArg Prod.fst eq)
      have bv : v = b := Fin.ext (congrArg Prod.snd eq)
      exact List.any_eq_true.mpr ⟨(u,v),huv,Bool.and_eq_true_iff.mpr ⟨au ▸ ha,bv ▸ hb⟩⟩
    · intro h
      obtain ⟨⟨a,b⟩,hab,on⟩ := List.any_eq_true.mp h
      exact ⟨a,b,List.mem_map.mpr ⟨(a,b),hab,rfl⟩,(Bool.and_eq_true_iff.mp on).1,(Bool.and_eq_true_iff.mp on).2⟩
  have tests : ∀ r ∈ ordinary,
      ((hit (row r) = true ∧ ∀ i, row r i = true → hit (Function.update (row r) i false) = false) ∨
      (hit (row r) = false ∧ ∀ i, row r i = false → hit (Function.update (row r) i true) = true)) ∧
      (row r 0 = false ∨ row r 7 = false) ∧ hit (row r) = p.contains r := by
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp (show ordinary.all (fun v => decide (
      ((hit (row v) = true ∧ ∀ i, row v i = true → hit (Function.update (row v) i false) = false) ∨
      (hit (row v) = false ∧ ∀ i, row v i = false → hit (Function.update (row v) i true) = true)) ∧
      (row v 0 = false ∨ row v 7 = false) ∧ hit (row v) = p.contains v)) = true from by decide +kernel) r hr)
  have hasRow : ∀ r ∈ p++d, r=129 ∨ r∈ordinary := by
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp (show (p++d).all (fun v => decide (v=129 ∨ v∈ordinary)) = true from by decide +kernel) r hr)
  have agree (r : ℕ) (hr : r ∈ p++d) : C.eval (List.ofFn (row r)) = p.contains r := by
    rcases hasRow r hr with rfl|regular
    · have matchRow : row 129 = fun i : Fin 14 => decide (i=0 ∨ i=7) := by funext i; fin_cases i <;> decide +kernel
      rw [matchRow]
      exact missing
    · obtain ⟨bd,absent,label⟩ := tests r regular
      have good := check (row r) (by simpa only [spec,Bool.not_eq_true] using bd) absent
      rw [spec] at good
      rw [← label]
      cases he : hit (row r) <;> cases hc : C.eval (List.ofFn (row r)) <;> simp_all
  have bounded : ∀ r ∈ p++d, r < 2^14 := by
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp (show (p++d).all (fun v => decide (v < 2^14)) = true from by decide +kernel) r hr)
  obtain ⟨a,h⟩ := complete 14 24 _ _ C bounded mono (by omega) agree
  have sat (b : Bool) (hb : a 377730 = b) :
      FormulaSat ([if b then 755460 else 755461] :: enc 14 24 (fun r => p.contains r) (p++d)) := by
    refine ⟨a,?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · refine ⟨_,List.mem_singleton_self _,?_⟩
      cases b
      · change (a 377730 == false) = true
        rw [hb]; rfl
      · change (a 377730 == true) = true
        rw [hb]; rfl
    · exact h c hc
  have padCase (hp : a 377732 = true) : False := by
    apply pad
    refine ⟨a,?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact ⟨755464,by simp,show (a 377732 == true) = true by rw [hp]; rfl⟩
    · exact h _ hc
  cases hb : a 377730 with
  | true => exact lastAnd (sat true hb)
  | false =>
    cases hp : a 377732 with
    | true => exact padCase hp
    | false =>
      apply other
      refine ⟨a,?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact ⟨755461,by simp,show (a 377730 == false) = true by rw [hb]; rfl⟩
      · rcases List.mem_cons.mp hc with rfl|hc
        · exact ⟨755465,by simp,show (a 377732 == false) = true by rw [hp]; rfl⟩
        · exact h _ hc
